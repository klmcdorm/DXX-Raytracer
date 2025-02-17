#include "Resource.h"
#include "GlobalDX.h"
#include "CommandQueue.h"
#include "CommandList.h"

namespace RT
{

	// -------------------------------------------------------------------------
	// Resources

	void CopyResource(ID3D12GraphicsCommandList* command_list, ID3D12Resource* dst, ID3D12Resource* src)
	{
		// NOTE(Justin): Probably should replace this at some point with a more lazy barrier approach instead of always transitioning back to old state
		// NOTE(Justin): This will crash if dst or src are not tracked, maybe handle this more gracefully (temp upload buffers are not worth being tracked)
		D3D12_RESOURCE_STATES dst_state = g_d3d.resource_tracker.GetResourceState(dst);
		D3D12_RESOURCE_STATES src_state = g_d3d.resource_tracker.GetResourceState(src);

		ResourceTransition(command_list, dst, D3D12_RESOURCE_STATE_COPY_DEST);
		ResourceTransition(command_list, src, D3D12_RESOURCE_STATE_COPY_SOURCE);

		command_list->CopyResource(dst, src);

		ResourceTransition(command_list, dst, dst_state);
		ResourceTransition(command_list, src, src_state);
	}

	// -------------------------------------------------------------------------
	// Buffers

	ID3D12Resource* CreateBuffer(RT_RESOURCE_TRACKER_DEBUG_PARAMS
		const wchar_t* name, size_t size, D3D12_HEAP_TYPE heap_type, D3D12_RESOURCE_FLAGS flags, D3D12_RESOURCE_STATES initial_state)
	{
		D3D12_HEAP_PROPERTIES heap_props = {};
		heap_props.Type = heap_type;

		D3D12_RESOURCE_DESC resource_desc = {};
		resource_desc.Dimension = D3D12_RESOURCE_DIMENSION_BUFFER;
		resource_desc.Alignment = D3D12_DEFAULT_RESOURCE_PLACEMENT_ALIGNMENT;
		resource_desc.Width = size;
		resource_desc.Height = 1;
		resource_desc.DepthOrArraySize = 1;
		resource_desc.MipLevels = 1;
		resource_desc.Format = DXGI_FORMAT_UNKNOWN;
		resource_desc.Layout = D3D12_TEXTURE_LAYOUT_ROW_MAJOR;
		resource_desc.SampleDesc.Count = 1;
		resource_desc.Flags = flags;

		ID3D12Resource* buffer;
		DX_CALL(g_d3d.device->CreateCommittedResource(&heap_props, D3D12_HEAP_FLAG_NONE, &resource_desc, initial_state, nullptr, IID_PPV_ARGS(&buffer)));

		buffer->SetName(name);
		g_d3d.resource_tracker.TrackObject(RT_RESOURCE_TRACKER_FWD_ARGS buffer, initial_state);

		return buffer;
	}

	ID3D12Resource* CreateReadOnlyBuffer(RT_RESOURCE_TRACKER_DEBUG_PARAMS
		const wchar_t* name, size_t size)
	{
		return CreateBuffer(RT_RESOURCE_TRACKER_FWD_ARGS name, size, D3D12_HEAP_TYPE_DEFAULT, D3D12_RESOURCE_FLAG_NONE, D3D12_RESOURCE_STATE_COMMON);
	}

	ID3D12Resource* CreateReadWriteBuffer(RT_RESOURCE_TRACKER_DEBUG_PARAMS
		const wchar_t* name, size_t size)
	{
		return CreateBuffer(RT_RESOURCE_TRACKER_FWD_ARGS name, size, D3D12_HEAP_TYPE_DEFAULT, D3D12_RESOURCE_FLAG_ALLOW_UNORDERED_ACCESS, D3D12_RESOURCE_STATE_COMMON);
	}

	ID3D12Resource* CreateUploadBuffer(RT_RESOURCE_TRACKER_DEBUG_PARAMS
		const wchar_t* name, size_t size)
	{
		return CreateBuffer(RT_RESOURCE_TRACKER_FWD_ARGS name, size, D3D12_HEAP_TYPE_UPLOAD, D3D12_RESOURCE_FLAG_NONE, D3D12_RESOURCE_STATE_GENERIC_READ);
	}

	ID3D12Resource* CreateReadbackBuffer(RT_RESOURCE_TRACKER_DEBUG_PARAMS
		const wchar_t* name, size_t size)
	{
		return CreateBuffer(RT_RESOURCE_TRACKER_FWD_ARGS name, size, D3D12_HEAP_TYPE_READBACK, D3D12_RESOURCE_FLAG_NONE, D3D12_RESOURCE_STATE_COPY_DEST);
	}

	ID3D12Resource* CreateAccelerationStructureBuffer(RT_RESOURCE_TRACKER_DEBUG_PARAMS
		const wchar_t* name, size_t size)
	{
		return CreateBuffer(RT_RESOURCE_TRACKER_FWD_ARGS name, size, D3D12_HEAP_TYPE_DEFAULT, D3D12_RESOURCE_FLAG_ALLOW_UNORDERED_ACCESS, D3D12_RESOURCE_STATE_RAYTRACING_ACCELERATION_STRUCTURE);
	}

	void CopyBuffer(ID3D12GraphicsCommandList* command_list, ID3D12Resource* dst, ID3D12Resource* src)
	{
		CopyResource(command_list, dst, src);
	}

	void CopyBufferRegion(ID3D12GraphicsCommandList* command_list, ID3D12Resource* dst, size_t dst_offset, ID3D12Resource* src, size_t src_offset, size_t num_bytes)
	{
		// NOTE(Justin): Probably should replace this at some point with a more lazy barrier approach instead of always transitioning back to old state
		D3D12_RESOURCE_STATES dst_state = g_d3d.resource_tracker.GetResourceState(dst);
		D3D12_RESOURCE_STATES src_state = g_d3d.resource_tracker.GetResourceState(src);

		ResourceTransition(command_list, dst, D3D12_RESOURCE_STATE_COPY_DEST);
		ResourceTransition(command_list, src, D3D12_RESOURCE_STATE_COPY_SOURCE);

		command_list->CopyBufferRegion(dst, dst_offset, src, src_offset, num_bytes);

		ResourceTransition(command_list, dst, dst_state);
		ResourceTransition(command_list, src, src_state);
	}

	void CreateBufferSRV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor, size_t first_element, uint32_t num_elements, uint32_t byte_stride)
	{
		D3D12_SHADER_RESOURCE_VIEW_DESC srv_desc = {};
		srv_desc.ViewDimension = D3D12_SRV_DIMENSION_BUFFER;
		srv_desc.Shader4ComponentMapping = D3D12_DEFAULT_SHADER_4_COMPONENT_MAPPING;
		srv_desc.Buffer.NumElements = num_elements;
		srv_desc.Buffer.FirstElement = first_element;
		srv_desc.Buffer.StructureByteStride = byte_stride;

		// ByteAddressBuffer
		if (byte_stride == 0)
		{
			srv_desc.Format = DXGI_FORMAT_R32_TYPELESS;
			srv_desc.Buffer.Flags = D3D12_BUFFER_SRV_FLAG_RAW;
		}
		// StructuredBuffer
		else
		{
			srv_desc.Format = DXGI_FORMAT_UNKNOWN;
			srv_desc.Buffer.Flags = D3D12_BUFFER_SRV_FLAG_NONE;
		}

		g_d3d.device->CreateShaderResourceView(resource, &srv_desc, descriptor);
	}

	void CreateBufferUAV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor, size_t first_element, uint32_t num_elements, uint32_t byte_stride)
	{
		D3D12_UNORDERED_ACCESS_VIEW_DESC uav_desc = {};
		uav_desc.ViewDimension = D3D12_UAV_DIMENSION_BUFFER;
		uav_desc.Buffer.NumElements = num_elements;
		uav_desc.Buffer.FirstElement = first_element;
		uav_desc.Buffer.StructureByteStride = byte_stride;
		uav_desc.Buffer.CounterOffsetInBytes = 0;

		// ByteAddressBuffer
		if (byte_stride == 0)
		{
			uav_desc.Format = DXGI_FORMAT_R32_TYPELESS;
			uav_desc.Buffer.Flags = D3D12_BUFFER_UAV_FLAG_RAW;
		}
		// StructuredBuffer
		else
		{
			uav_desc.Format = DXGI_FORMAT_UNKNOWN;
			uav_desc.Buffer.Flags = D3D12_BUFFER_UAV_FLAG_NONE;
		}

		g_d3d.device->CreateUnorderedAccessView(resource, nullptr, &uav_desc, descriptor);
	}

	void CreateAccelerationStructureSRV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor)
	{
		D3D12_SHADER_RESOURCE_VIEW_DESC srv_desc = {};
		srv_desc.RaytracingAccelerationStructure.Location = resource->GetGPUVirtualAddress();
		srv_desc.ViewDimension = D3D12_SRV_DIMENSION_RAYTRACING_ACCELERATION_STRUCTURE;
		srv_desc.Shader4ComponentMapping = D3D12_DEFAULT_SHADER_4_COMPONENT_MAPPING;

		g_d3d.device->CreateShaderResourceView(nullptr, &srv_desc, descriptor);
	}

	// -------------------------------------------------------------------------
	// Textures

	ID3D12Resource* CreateTexture(RT_RESOURCE_TRACKER_DEBUG_PARAMS const wchar_t* name, const D3D12_RESOURCE_DESC* resource_desc, D3D12_CLEAR_VALUE* clear_value)
	{
		D3D12_HEAP_PROPERTIES heap_props = {};
		heap_props.Type = D3D12_HEAP_TYPE_DEFAULT;

		ID3D12Resource* texture;
		DX_CALL(g_d3d.device->CreateCommittedResource(&heap_props, D3D12_HEAP_FLAG_NONE, resource_desc,
			D3D12_RESOURCE_STATE_PIXEL_SHADER_RESOURCE | D3D12_RESOURCE_STATE_NON_PIXEL_SHADER_RESOURCE, clear_value, IID_PPV_ARGS(&texture)));

		texture->SetName(name);
		g_d3d.resource_tracker.TrackObject(RT_RESOURCE_TRACKER_FWD_ARGS texture, D3D12_RESOURCE_STATE_PIXEL_SHADER_RESOURCE | D3D12_RESOURCE_STATE_NON_PIXEL_SHADER_RESOURCE);

		return texture;
	}

	ID3D12Resource* CreateTexture(RT_RESOURCE_TRACKER_DEBUG_PARAMS const wchar_t* name, DXGI_FORMAT format, D3D12_RESOURCE_FLAGS flags, size_t width, uint32_t height, D3D12_RESOURCE_STATES state, uint16_t mips, D3D12_CLEAR_VALUE* clear_value)
	{
		D3D12_HEAP_PROPERTIES heap_props = {};
		heap_props.Type = D3D12_HEAP_TYPE_DEFAULT;

		D3D12_RESOURCE_DESC resource_desc = {};
		resource_desc.Dimension = D3D12_RESOURCE_DIMENSION_TEXTURE2D;
		resource_desc.Alignment = D3D12_DEFAULT_RESOURCE_PLACEMENT_ALIGNMENT;
		resource_desc.Width = width;
		resource_desc.Height = height;
		resource_desc.DepthOrArraySize = 1;
		resource_desc.MipLevels = mips;
		resource_desc.Format = format;
		resource_desc.Layout = D3D12_TEXTURE_LAYOUT_UNKNOWN;
		resource_desc.SampleDesc.Count = 1;
		resource_desc.SampleDesc.Quality = 0;
		resource_desc.Flags = flags;

		ID3D12Resource* texture;
		DX_CALL(g_d3d.device->CreateCommittedResource(&heap_props, D3D12_HEAP_FLAG_NONE, &resource_desc,
			state, clear_value, IID_PPV_ARGS(&texture)));

		texture->SetName(name);
		g_d3d.resource_tracker.TrackObject(RT_RESOURCE_TRACKER_FWD_ARGS texture, state);

		return texture;
	}

	void CopyTexture(ID3D12GraphicsCommandList* command_list, ID3D12Resource* dst, ID3D12Resource* src)
	{
		CopyResource(command_list, dst, src);
	}

	void CopyTextureRegion(ID3D12GraphicsCommandList* command_list, ID3D12Resource* dst, uint32_t dst_x, uint32_t dst_y, uint32_t dst_z,
		const D3D12_TEXTURE_COPY_LOCATION* src_loc, const D3D12_BOX* src_box)
	{
		D3D12_TEXTURE_COPY_LOCATION dest_texture_loc = {};
		dest_texture_loc.pResource = dst;
		dest_texture_loc.SubresourceIndex = 0;
		dest_texture_loc.Type = D3D12_TEXTURE_COPY_TYPE_SUBRESOURCE_INDEX;

		D3D12_RESOURCE_STATES dst_state = g_d3d.resource_tracker.GetResourceState(dst);

		ResourceTransition(command_list, dst, D3D12_RESOURCE_STATE_COPY_DEST);
		command_list->CopyTextureRegion(&dest_texture_loc, dst_x, dst_y, dst_z, src_loc, src_box);
		ResourceTransition(command_list, dst, dst_state);
	}

	void UploadTextureData(ID3D12Resource* dst, size_t row_pitch, size_t row_count, const void* data_ptr)
	{
		D3D12_PLACED_SUBRESOURCE_FOOTPRINT pitch_footprint;
		D3D12_RESOURCE_DESC dst_desc = dst->GetDesc();
		size_t dst_byte_size;
		g_d3d.device->GetCopyableFootprints(&dst_desc, 0, 1, 0, &pitch_footprint, nullptr, nullptr, &dst_byte_size);

		RingBufferAllocation ring_buf_alloc = AllocateFromRingBuffer(&g_d3d.resource_upload_ring_buffer, dst_byte_size, D3D12_TEXTURE_DATA_PLACEMENT_ALIGNMENT);
		D3D12_PLACED_SUBRESOURCE_FOOTPRINT placed_footprint = {};
		placed_footprint.Offset = ring_buf_alloc.byte_offset;
		placed_footprint.Footprint = pitch_footprint.Footprint;

		uint8_t* src_ptr = (uint8_t*)data_ptr;
		uint8_t* dst_ptr = ring_buf_alloc.ptr;

		size_t dst_pitch = pitch_footprint.Footprint.RowPitch;

		for (size_t y = 0; y < row_count; ++y)
		{
			memcpy(dst_ptr, src_ptr, row_pitch);

			src_ptr += row_pitch;
			dst_ptr += dst_pitch;
		}

		D3D12_TEXTURE_COPY_LOCATION src_loc = {};
		src_loc.pResource = ring_buf_alloc.resource;
		src_loc.PlacedFootprint = placed_footprint;
		src_loc.Type = D3D12_TEXTURE_COPY_TYPE_PLACED_FOOTPRINT;

		CommandList& command_list = *ring_buf_alloc.command_list;
		CopyTextureRegion(command_list, dst, 0, 0, 0, &src_loc, nullptr);
	}

	void UploadTextureDataDDS(ID3D12Resource* dst, size_t width, size_t height, size_t bpp, size_t mipCount, const void* data_ptr)
	{
		uint8_t* src_ptr = (uint8_t*)data_ptr;  // keep track of where we are in the texture data between mipmaps

		for (size_t mipIndex = 0; mipIndex < mipCount ; ++mipIndex)
		{

			size_t divider = (size_t)round(pow(2, (double) mipIndex));

			D3D12_PLACED_SUBRESOURCE_FOOTPRINT pitch_footprint;
			D3D12_RESOURCE_DESC dst_desc = dst->GetDesc();
			size_t dst_byte_size;		// total size of destination memory
			size_t dst_row_byte_size;	// row size of destination memory
			UINT dst_row_num;			// how many rows of data are there.  this is different than height as dds is in 4x4 blocks of data
			g_d3d.device->GetCopyableFootprints(&dst_desc,(UINT) mipIndex, 1, 0, &pitch_footprint, &dst_row_num, &dst_row_byte_size, &dst_byte_size);

			size_t src_byte_size = ((width / divider) * (height / divider)) / (bpp / 8);	// total size of source memory
			size_t src_row_byte_size = src_byte_size / dst_row_num;							// row size of source memory

			RingBufferAllocation ring_buf_alloc = AllocateFromRingBuffer(&g_d3d.resource_upload_ring_buffer, dst_byte_size, D3D12_TEXTURE_DATA_PLACEMENT_ALIGNMENT);
			D3D12_PLACED_SUBRESOURCE_FOOTPRINT placed_footprint = {};
			placed_footprint.Offset = ring_buf_alloc.byte_offset;
			placed_footprint.Footprint = pitch_footprint.Footprint;

			uint8_t* dst_ptr = ring_buf_alloc.ptr;

			size_t dst_pitch = pitch_footprint.Footprint.RowPitch;

			// copy the texture data into the ring buffer
			for (size_t y = 0; y < dst_row_num; ++y)
			{
				memcpy(dst_ptr, src_ptr, src_row_byte_size);
			
				// Increment the src and dst pointers.  
				// They are incremented by different amounts because the destination memory each row must be a multiple of 256bytes so padding is added to every row that is below this multiple.
				// The dds file does not have this requirement and is more tightly packed.
				src_ptr += src_row_byte_size;
				dst_ptr += dst_pitch;
			}
			

			D3D12_TEXTURE_COPY_LOCATION src_loc = {};
			src_loc.pResource = ring_buf_alloc.resource;
			src_loc.PlacedFootprint = placed_footprint;
			src_loc.Type = D3D12_TEXTURE_COPY_TYPE_PLACED_FOOTPRINT;

			D3D12_TEXTURE_COPY_LOCATION dest_loc = {};
			dest_loc.pResource = dst;
			dest_loc.SubresourceIndex = (UINT)mipIndex;
			dest_loc.Type = D3D12_TEXTURE_COPY_TYPE_SUBRESOURCE_INDEX;

			D3D12_RESOURCE_STATES dst_state = g_d3d.resource_tracker.GetResourceState(dst);

			CommandList& command_list = *ring_buf_alloc.command_list;
			ResourceTransition(command_list, dst, D3D12_RESOURCE_STATE_COPY_DEST);
			command_list->CopyTextureRegion(&dest_loc, 0, 0, 0, &src_loc, nullptr);
			ResourceTransition(command_list, dst, dst_state);

		}

	}

	void CreateTextureSRV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor, DXGI_FORMAT format, uint32_t mips)
	{
		D3D12_SHADER_RESOURCE_VIEW_DESC srv_desc = {};
		srv_desc.Format = format;
		srv_desc.ViewDimension = D3D12_SRV_DIMENSION_TEXTURE2D;
		srv_desc.Shader4ComponentMapping = D3D12_DEFAULT_SHADER_4_COMPONENT_MAPPING;
		srv_desc.Texture2D.MipLevels = mips == UINT32_MAX ? resource->GetDesc().MipLevels : mips;
		srv_desc.Texture2D.MostDetailedMip = 0;
		srv_desc.Texture2D.PlaneSlice = 0;
		srv_desc.Texture2D.ResourceMinLODClamp = 0;

		g_d3d.device->CreateShaderResourceView(resource, &srv_desc, descriptor);
	}

	void CreateTextureUAV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor, DXGI_FORMAT format)
	{
		D3D12_UNORDERED_ACCESS_VIEW_DESC uav_desc = {};
		uav_desc.Format = format;
		uav_desc.ViewDimension = D3D12_UAV_DIMENSION_TEXTURE2D;
		uav_desc.Texture2D.MipSlice = 0;
		uav_desc.Texture2D.PlaneSlice = 0;

		g_d3d.device->CreateUnorderedAccessView(resource, nullptr, &uav_desc, descriptor);
	}

	void CreateTextureRTV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor, DXGI_FORMAT format)
	{
		D3D12_RENDER_TARGET_VIEW_DESC rtv_desc = {};
		rtv_desc.Format = format;
		rtv_desc.ViewDimension = D3D12_RTV_DIMENSION_TEXTURE2D;
		rtv_desc.Texture2D.MipSlice = 0;
		rtv_desc.Texture2D.PlaneSlice = 0;

		g_d3d.device->CreateRenderTargetView(resource, &rtv_desc, descriptor);
	}

	void CreateTextureDSV(ID3D12Resource* resource, D3D12_CPU_DESCRIPTOR_HANDLE descriptor, DXGI_FORMAT format)
	{
		D3D12_DEPTH_STENCIL_VIEW_DESC dsv_desc = {};
		dsv_desc.Format = format;
		dsv_desc.ViewDimension = D3D12_DSV_DIMENSION_TEXTURE2D;
		dsv_desc.Texture2D.MipSlice = 0;
		dsv_desc.Flags = D3D12_DSV_FLAG_NONE;

		g_d3d.device->CreateDepthStencilView(resource, &dsv_desc, descriptor);
	}

}
