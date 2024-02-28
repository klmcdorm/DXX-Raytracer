// ------------------------------------------------------------------
// Game-code includes

#include "Level.h"
#include "segment.h"
#include "textures.h"
#include "gameseq.h"
#include "wall.h"
#include "automap.h"
#include "render.h"
#include "fvi.h"

// ------------------------------------------------------------------
// RT includes

#include "Core/MiniMath.h"
#include "Core/Arena.h"
#include "RTgr.h"
#include "Renderer.h"
#include "Lights.h"

// ------------------------------------------------------------------

// Current active level
RT_ResourceHandle g_level_resource = { 0 };
int g_active_level = 0;

int m_light_count = 0;
RT_Light m_lights[1024] = {0};
int m_lights_definitions[1024] = {0};
side* m_extracted_light_sides[1024] = {0};

short m_lights_seg_ids[1024] = {-1};
short m_lights_relevance_score[1024] = { 0.0f };
short m_lights_to_sort[1024];
int m_lights_found = 0;

// Cache whether a line of sight exists from one segment to another.
uint8_t m_segment2segment_vis[MAX_SEGMENTS][MAX_SEGMENTS];
void InitSegment2SegmentVis() 
{
	fvi_query query;
	fvi_info result;
	vms_vector seg_i_center, seg_j_center;

	for (int i = 0; i < Num_segments; i++) 
	{
		m_segment2segment_vis[i][i] = 1;
		compute_segment_center(&seg_i_center, &Segments[i]);

		for (int j = 0; j < i; j++) 
		{
			compute_segment_center(&seg_j_center, &Segments[j]);

			query.startseg = i;
			query.p0 = &seg_i_center;
			query.p1 = &seg_j_center;
			query.rad = 0;
			query.thisobjnum = -1;
			query.ignore_obj_list = NULL;
			query.flags = FQ_TRANSWALL;

			find_vector_intersection(&query, &result);
			if (result.hit_type == HIT_WALL) 
			{
				m_segment2segment_vis[i][j] = 0;
				m_segment2segment_vis[j][i] = 0;
			}
			else 
			{
				m_segment2segment_vis[i][j] = 1;
				m_segment2segment_vis[j][i] = 1;
			}
		}
	}
}

RT_Triangle RT_TriangleFromIndices(RT_Vertex* verts, int vert_offset, int v0, int v1, int v2, int tmap) 
{
	RT_Triangle triangle = { 0 };

	triangle.material_edge_index = tmap;

	RT_Vec3 pos0 = verts[vert_offset + v0].pos;
	RT_Vec3 pos1 = verts[vert_offset + v1].pos;
	RT_Vec3 pos2 = verts[vert_offset + v2].pos;

	RT_Vec3 p10 = RT_Vec3Normalize(RT_Vec3Sub(pos1, pos0));
	RT_Vec3 p20 = RT_Vec3Normalize(RT_Vec3Sub(pos2, pos0));

	RT_Vec3 normal = RT_Vec3Normalize(RT_Vec3Cross(p10, p20));

	triangle.pos0 = pos0;
	triangle.pos1 = pos1;
	triangle.pos2 = pos2;
	triangle.normal0 = normal;
	triangle.normal1 = normal;
	triangle.normal2 = normal;
	triangle.uv0 = verts[vert_offset + v0].uv;
	triangle.uv1 = verts[vert_offset + v1].uv;
	triangle.uv2 = verts[vert_offset + v2].uv;
	triangle.color = 0xFFFFFFFF;

	return triangle;
}

void RT_ExtractLightsFromSide(side *side, RT_Vertex *vertices, RT_Vec3 normal, int seg_id)
{
	int light_index = RT_IsLight(side->tmap_num2 & 0x3FFF);
	if (light_index > -1)
	{
		RT_Vec2 uv_min = RT_Vec2Make(INFINITY, INFINITY);
		RT_Vec2 uv_max = RT_Vec2Make(-INFINITY, -INFINITY);
		for (int i = 0; i < 4; i++)
		{
			RT_Vec2 uv = RT_Vec2Make((f2fl(side->uvls[i].u)),(f2fl(side->uvls[i].v)));
			
			uv_min = RT_Vec2Min(uv, uv_min);
			uv_max = RT_Vec2Max(uv, uv_max);
		}

		bool multiple_lights = false;
		if(uv_min.x < -1.0 || uv_min.y < -1.0 || uv_max.x > 1.0 || uv_max.y > 1.0)
		{
			RT_Vec2 uv = RT_Vec2Sub(uv_max, uv_min);
			RT_Vec2 light_size = g_light_definitions[light_index].size;

			int num_x = max((int)(uv.x / light_size.x),1);
			int num_y = max((int)(uv.y / light_size.y),1);

			RT_LOGF(RT_LOGSERVERITY_INFO, "Creating lights in the following directions. {X: %i, Y: %i}", num_x, num_y);
			if(num_x > 1 && num_y > 1)
			{
				RT_LOGF(RT_LOGSERVERITY_INFO, "Multiple lights created!");
				multiple_lights = true;
			}
		}

		if (!multiple_lights) 
		{
			if (ALWAYS(m_light_count < RT_ARRAY_COUNT(m_lights)))
			{
				m_lights[m_light_count] = RT_InitLight(g_light_definitions[light_index], vertices, normal);
				m_lights_definitions[m_light_count] = light_index;
				m_extracted_light_sides[m_light_count] = side;

				m_lights_seg_ids[m_light_count] = seg_id;
				m_light_count++;
			}
		}
	}
}

RT_ResourceHandle RT_UploadLevelGeometry()
{
	RT_ResourceHandle level_handle = {0};

	RT_ArenaMemoryScope(&g_thread_arena)
	{
		RT_Vertex* verts = RT_ArenaAllocArray(&g_thread_arena, Num_segments * 6 * 4, RT_Vertex);
		RT_Triangle* triangles = RT_ArenaAllocArray(&g_thread_arena, Num_segments * 6 * 2, RT_Triangle);

		// Init lights segment id list
		for (size_t i = 0; i < _countof(m_lights_seg_ids); ++i) {
			m_lights_seg_ids[i] = -1;
		}

		int num_verts = 0;
		int num_indices = 0; 
		int num_triangles = 0;

		int num_mesh = 0;
		for (int seg_id = 0; seg_id < Num_segments; seg_id++)
		{
			segment *seg = &Segments[seg_id];

			for (int side_index = 0; side_index < MAX_SIDES_PER_SEGMENT; side_index++)
			{
				const int vertex_offset = num_verts;
				const int indices_offset = num_indices;

				side *s = &seg->sides[side_index];
				int vertnum_list[4];
				get_side_verts(&vertnum_list, seg_id, side_index);

				int vert_ids[4];

				for (int v = 0; v < 4; v++)
				{
					// Extract Vertex Data
					const int vertex_id = vertnum_list[v];
					vms_vector raw_vertex = Vertices[vertex_id];
					vms_vector raw_normal = s->normals[0]; // if quadrilateral use this as normal.

					RT_Vertex vert =
					{
						f2fl(raw_vertex.x),
						f2fl(raw_vertex.y),
						f2fl(raw_vertex.z),
						f2fl(s->uvls[v].u),
						f2fl(s->uvls[v].v),
						f2fl(raw_normal.x),
						f2fl(raw_normal.y),
						f2fl(raw_normal.z)
					};
					verts[vertex_offset + v] = vert;
					num_verts++;

					//assert(vert.uv.x >= -10.0 && vert.uv.x <= 10.0);
				}

				// Ignore invisible walls
				bool should_render = false;
				if (seg->children[side_index] == -1)
				{
					should_render = true;
				}
				else if (s->wall_num != -1)
				{
					wall *w = &Walls[s->wall_num];
					// TODO(daniel): What about blastable wallls?
					if (w->type != WALL_OPEN)
					{
						should_render = true;
					}
				}

				if (!should_render) { continue; }

				int absolute_side_index = MAX_SIDES_PER_SEGMENT*seg_id + side_index;
				switch (s->type) 
				{
					case SIDE_IS_TRI_13:
						triangles[num_triangles++] = RT_TriangleFromIndices(verts, vertex_offset, 0, 1, 3, absolute_side_index);
						triangles[num_triangles++] = RT_TriangleFromIndices(verts, vertex_offset, 1, 2, 3, absolute_side_index);
					break;
					
					case SIDE_IS_QUAD:
					case SIDE_IS_TRI_02:
					default:
						triangles[num_triangles++] = RT_TriangleFromIndices(verts, vertex_offset, 0, 1, 2, absolute_side_index);
						triangles[num_triangles++] = RT_TriangleFromIndices(verts, vertex_offset, 0, 2, 3, absolute_side_index);
					break;
				}
				
				RT_ExtractLightsFromSide(s, &verts[vertex_offset], triangles[num_triangles - 1].normal0, seg_id);
			}
		}

		// NOTE(daniel): This is a separate call, because I don't want to do something tweaky like
		// detecting whether tangents need to be calculated in RT_UploadMesh. You, the uploader, should know.
		RT_GenerateTangents(triangles, num_triangles);

		RT_UploadMeshParams params =
		{
			.triangle_count = num_triangles,
			.triangles      = triangles,
		};

		RT_LOGF(RT_LOGSERVERITY_INFO, "UPLOADING MESH >>\n");
		level_handle = RT_UploadMesh(&params);
		RT_LOGF(RT_LOGSERVERITY_INFO, "UPLOADING MESH OK\n");
	}

	return level_handle;
}

bool RT_UnloadLevel()
{
	// Only unload if a level acceleration structure actually exists
	if (RT_RESOURCE_HANDLE_VALID(g_level_resource))
	{
		RT_ReleaseMesh(g_level_resource);
		g_level_resource = RT_RESOURCE_HANDLE_NULL;

		m_light_count = 0;
		memset(m_lights, 0, sizeof(RT_Light) * 1024);

		return true;
	}

	return false;
}

bool RT_LoadLevel() 
{
	// Load a level only if a level acceleration structure does not exist yet
	if (!RT_RESOURCE_HANDLE_VALID(g_level_resource))
	{
		assert(!RT_RESOURCE_HANDLE_VALID(g_level_resource));
		// Load level geometry
		g_level_resource = RT_UploadLevelGeometry();
		g_active_level = Current_level_num;

		// NOTE: relatively slow for larger levels
		//RT_LOGF(RT_LOGSERVERITY_INFO, "InitSegment2SegmentVis START");
		//InitSegment2SegmentVis();
		//RT_LOGF(RT_LOGSERVERITY_INFO, "InitSegment2SegmentVis FINISH");

		return RT_RESOURCE_HANDLE_VALID(g_level_resource);
	}

	return false;
}

void RT_RenderLevel(RT_Vec3 player_pos) 
{
	// ------------------------------------------------------------------
	RT_UpdateMaterialEdges();
	RT_UpdateMaterialIndices();

	RT_FindAndSubmitNearbyLights(player_pos);

	RT_Mat4 mat = RT_Mat4Identity();
	RT_RaytraceMesh(g_level_resource, &mat, &mat);
}

// --------------------------------------------------------------------------------------
// 

// Heap / priority queue for TraverseSegmentsForLights.
// Static scope.
typedef struct _m_visit_queue_entry {
	// Segment to visit.
	uint16_t segment_index;
	// Location from which to reach segment (either actual Viewer position or segment side)
	RT_Vec3  entry_pos;
	// Distance from Viewer, by best scoring segment path (number of segments)
	uint8_t  depth;
	// Distance from Viewer, by best scoring segment path (length in units)
	float    segment_distance;
	// Accumulated light relevance score
	float    score;
} m_visit_queue_entry;

m_visit_queue_entry m_visit_queue[MAX_SEGMENTS];
uint16_t m_visit_queue_length = 0;

// Add an item to the static TraverseSegmentsForLights queue.
void AddToVisitQueue(m_visit_queue_entry entry)
{
	assert(m_visit_queue_length < MAX_SEGMENTS);

	// add at end of heap
	m_visit_queue[m_visit_queue_length] = entry;

	// bubble up
	uint16_t index = m_visit_queue_length;
	while (index > 0) 
	{
		uint16_t parent_index = (index - 1) / 2;
		if (m_visit_queue[parent_index].score <= m_visit_queue[index].score) 
		{
			break;
		}

		m_visit_queue_entry temp = m_visit_queue[parent_index];
		m_visit_queue[parent_index] = m_visit_queue[index];
		m_visit_queue[index] = temp;
		index = parent_index;
	}

	// adjust length
	m_visit_queue_length++;
}

// Remove an item from the static TraverseSegmentsForLights queue.
m_visit_queue_entry RemoveFromVisitQueue() 
{
	assert(m_visit_queue_length > 0);

	// remove from top of heap by swapping with last entry
	m_visit_queue_entry temp;
	m_visit_queue_entry result = m_visit_queue[0];
	m_visit_queue_length--;
	m_visit_queue[0] = m_visit_queue[m_visit_queue_length];

	// push down
	uint16_t index = 0;
	while (index < m_visit_queue_length) 
	{
		uint16_t swap_index;
		uint16_t left_child = (index * 2) + 1;
		uint16_t right_child = (index * 2) + 2;
		float score = m_visit_queue[index].score;
		float left_score  = left_child  < m_visit_queue_length ? m_visit_queue[left_child].score  : INFINITY;
		float right_score = right_child < m_visit_queue_length ? m_visit_queue[right_child].score : INFINITY;

		if (score < left_score && score < right_score) {
			break;
		}

		// score is >= min(left_score, right_score)
		if (left_score < right_score) 
		{
			swap_index = left_child;
		}
		else // right_score <= left_score
		{
			swap_index = right_child;
		}

		assert(swap_index < m_visit_queue_length);
		temp = m_visit_queue[index];
		m_visit_queue[index] = m_visit_queue[swap_index];
		m_visit_queue[swap_index] = temp;
		index = swap_index;
	}

	return result;
}

// Heuristic search through nearby segments for lights.
void TraverseSegmentsForLights(short seg_num, RT_Vec3 seg_entry_pos) {
	uint8_t lights_added[_countof(m_lights)] = { 0 };
	uint8_t visit_list[MAX_SEGMENTS] = { 0 };

	m_visit_queue_length = 0;
	m_visit_queue_entry visiting_now = {
		.segment_index = seg_num,
		.entry_pos = seg_entry_pos,
		.depth = 0,
		.segment_distance = 0,
		.score = 0,
	};
	AddToVisitQueue(visiting_now);

	while (m_visit_queue_length > 0) {
		visiting_now = RemoveFromVisitQueue();

		short   segnum             = visiting_now.segment_index;
		RT_Vec3 curr_seg_entry_pos = visiting_now.entry_pos;
		uint8_t curr_rec_depth     = visiting_now.depth;
		float   curr_rec_dist      = visiting_now.segment_distance;
		segment* seg = &Segments[segnum];

		// If we've already processed this segment, skip it
		if (visit_list[segnum]) {
			continue;
		}
		visit_list[segnum] = 1;

		// Upload all the lights in this segment
		for (int j = 0; j < m_light_count; ++j) {
			// Filter out lights that aren't in this segment
			if (m_lights_seg_ids[j] == -1)
				continue;
			if (m_lights_seg_ids[j] != segnum)
				continue;

			// Filter out lights that have already been added - this should fix the issue with lights being added twice
			if (lights_added[j] != 0)
				continue;

			// Filter out lights that are too far away from the camera - direct path
			const float distance_from_player = RT_Vec3Length(RT_Vec3Sub(RT_Vec3Fromvms_vector(&Viewer->pos), RT_TranslationFromMat34(m_lights[j].transform)));
			if (distance_from_player > max_distance)
				continue;

			// Filter out lights that are too far away from the camera - segment distance - this is broken, don't use it
			const float distance_from_seg_entry_pos = RT_Vec3Length(RT_Vec3Sub(curr_seg_entry_pos, RT_TranslationFromMat34(m_lights[j].transform)));
			//if (curr_rec_dist + distance_from_seg_entry_pos > max_seg_distance)
			//	continue;

			// Mark this light as added
			lights_added[j] = 1;

			// The lower the value, the more relevant the light is
			m_lights_relevance_score[m_lights_found] = (float)(curr_rec_dist + distance_from_seg_entry_pos);
			m_lights_to_sort[m_lights_found] = j;
			++m_lights_found;
		}

		// search adjacent segments, but not if we've traveled too far
		if (curr_rec_depth >= max_rec_depth) 
			continue;

		for (size_t i = 0; i < MAX_SIDES_PER_SEGMENT; ++i) {
			// Assuming that RENDPAST means "render past this wall", if that is 0, we stop the traversal here
			const int wid = WALL_IS_DOORWAY(seg, i);
			if ((wid & WID_RENDPAST_FLAG) == 0)
				continue;

			// Get the segment number of this child segment
			const short seg_num_child = seg->children[i];

			// If it's -1 or -2, there is no segment on this side, skip it
			if (seg_num_child < 0)
				continue;

			// Find the current segment's side's vertices
			RT_Vec3 verts[4];
			for (size_t j = 0; j < _countof(Side_to_verts_int[j]); ++j) {
				// Get one of the vertices of the side
				verts[j] = RT_Vec3Fromvms_vector(&Vertices[Segments[seg_num_child].verts[Side_to_verts_int[i][j]]]);
			}

			// Calculate center
			const RT_Vec3 tmp1 = RT_Vec3Add(verts[0], verts[1]);
			const RT_Vec3 tmp2 = RT_Vec3Add(verts[2], verts[3]);
			const RT_Vec3 center = RT_Vec3Muls(RT_Vec3Add(tmp1, tmp2), 0.25f);

			// Find distance between segment entry
			const RT_Vec3 vector_from_entry_to_curr_segment = RT_Vec3Sub(center, curr_seg_entry_pos);
			const float distance_from_entry_to_curr_segment_squared = RT_Vec3Length(vector_from_entry_to_curr_segment);

			// too far, skip it
			if (distance_from_entry_to_curr_segment_squared > max_seg_distance)
				continue;

			m_visit_queue_entry new_entry = {
				.segment_index = seg_num_child,
				.entry_pos = center,
				.depth = curr_rec_depth + 1,
				.segment_distance = curr_rec_dist + distance_from_entry_to_curr_segment_squared,
			};
			// TODO maybe alter score based on other factors, like line of sight
			new_entry.score = new_entry.segment_distance;
			// The same segment may be added multiple times -- but hopefully with different scores.
			AddToVisitQueue(new_entry);
		}
	}
}

void RT_UpdateLight(int index)
{
	RT_LightDefinition definition = g_light_definitions[m_lights_definitions[index]];
	RT_Light* light = &m_lights[index];
	light->kind = definition.kind;

	light->spot_angle    = RT_Uint8FromFloat(definition.spot_angle);
	light->spot_softness = RT_Uint8FromFloat(definition.spot_softness);

	light->emission = RT_PackRGBE(RT_Vec3Muls(definition.emission, g_light_multiplier));

	if(light->kind == RT_LightKind_Area_Sphere)
	{
		float r = definition.radius;
		RT_Vec3 position = RT_TranslationFromMat34(light->transform);

		RT_Mat34 transform = 
		{
			.e = 
			{
				r, 0, 0, position.x,
				0, r, 0, position.y,
				0, 0, r, position.z,
			}
		};
		light->transform = transform;
	}
	
}

void RT_FindAndSubmitNearbyLights(RT_Vec3 player_pos)
{
	int total = 0;

	for (int i = 0; i < m_light_count; i++)
	{
		if (g_pending_light_update)
		{
			RT_UpdateLight(i);
		}

		if (g_light_visual_debug)
		{
			RT_VisualizeLight(&m_lights[i]);
		}
	}

	if (light_culling_heuristic == 0){
		for (int i = 0; i < m_light_count; i++) 
		{
            const float distance = RT_Vec3Length(RT_Vec3Sub(RT_TranslationFromMat34(m_lights[i].transform), player_pos));
			if (distance < max_distance)
			{
				RT_RaytraceSubmitLight(m_lights[i]);
				total++;
			}
		}
	}

	// Segment based
	else if (light_culling_heuristic == 1) {
		const auto max_lights = RT_MAX_LIGHTS - RT_RaytraceGetCurrentLightCount(); // keep some room for dynamic lights
		m_lights_found = 0;
		uint8_t visit_list[MAX_SEGMENTS] = { 0 };
		uint8_t lights_added[_countof(m_lights)] = { 0 };

		// Find all the lights that the player has a direct path towards
		TraverseSegmentsForLights(Viewer->segnum, RT_Vec3Fromvms_vector(&Viewer->pos));

		// If the number of lights exceeds the max number of lights, we need to pick the best ones
		if (m_lights_found > max_lights) {
			// Bubble sort them based on segment distance. We want the ones with the lowest number to appear first in the list
			for (int end = m_lights_found - 1; end > 0; --end) {
				for (int i = 0; i < end; ++i) {
					if (m_lights_relevance_score[i + 0] > m_lights_relevance_score[i + 1]) {
						// Swap the scores
						const short temp1 = m_lights_relevance_score[i + 0];
						m_lights_relevance_score[i + 0] = m_lights_relevance_score[i + 1];
						m_lights_relevance_score[i + 1] = temp1;

						// Swap the indices in the list
						const short temp2 = m_lights_to_sort[i + 0];
						m_lights_to_sort[i + 0] = m_lights_to_sort[i + 1];
						m_lights_to_sort[i + 1] = temp2;
					}
				}
			}

			// We only want to upload the best ones
			m_lights_found = max_lights;
		}

		total = m_lights_found;

		// Submit the lights
		for (int i = 0; i < m_lights_found; ++i) {
			RT_RaytraceSubmitLight(m_lights[m_lights_to_sort[i]]);
		}
	}

	g_pending_light_update = false;
	g_active_lights = total;
}