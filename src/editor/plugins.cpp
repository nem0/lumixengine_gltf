#define _CRT_SECURE_NO_WARNINGS
#define CGLTF_IMPLEMENTATION
#include "cgltf.h"
#undef _CRT_SECURE_NO_WARNINGS

#include "animation/animation.h"
#include "editor/asset_compiler.h"
#include "editor/world_editor.h"
#include "editor/studio_app.h"
#include "engine/crc32.h"
#include "engine/engine.h"
#include "engine/file_system.h"
#include "engine/job_system.h"
#include "engine/log.h"
#include "engine/lua_wrapper.h"
#include "engine/path_utils.h"
#include "renderer/model.h"
#include <float.h>

using namespace Lumix;


namespace
{


struct ModelWriter {
	ModelWriter(const char* src, IAllocator& allocator) 
		: allocator(allocator)
		, out(allocator)
		, src(src)
	{}

	template <typename T> void write(const T& obj) { out.write(&obj, sizeof(obj)); }
	void write(const void* ptr, size_t size) { out.write(ptr, size); }

	void writeModelHeader() {
		Model::FileHeader header;
		header.magic = 0x5f4c4d4f; // == '_LMO';
		header.version = (u32)Model::FileVersion::LATEST;
		write(header);
	}

	static bool hasAttribute(const cgltf_mesh& mesh, cgltf_attribute_type type) {
		for(u32 i = 0; i < mesh.primitives[0].attributes_count; ++i) {
			if (mesh.primitives[0].attributes[i].type == type) return true;
		}
		return false;
	}

	static u8 getComponentsCount(const cgltf_attribute& attr) {
		switch(attr.data->type) {
			case cgltf_type_scalar: return 1;
			case cgltf_type_vec2: return 2;
			case cgltf_type_vec3: return 3;
			case cgltf_type_vec4: return 4;
			case cgltf_type_mat2: return 8;
			case cgltf_type_mat3: return 12;
			case cgltf_type_mat4: return 16;
			default: ASSERT(false); return 0;
		}
	}

	void writeMeshes(cgltf_data* data) {
		const PathUtils::FileInfo src_info(src);
		const u32 mesh_count = (u32)data->meshes_count;
		write(mesh_count);

		i32 attr_offset = 0;
		i32 indices_offset = 0;
	
		auto writeMesh = [&](const cgltf_mesh& import_mesh ) {
			ASSERT(import_mesh.primitives_count == 1);
			ASSERT(import_mesh.primitives[0].type == cgltf_primitive_type_triangles);
			const bool is_rigid_animated = isRigidAnimated(data, import_mesh);
			const u32 attribute_count = (u32)import_mesh.primitives[0].attributes_count + (is_rigid_animated ? 2 : 0);
			write(attribute_count);

			for(u32 i = 0; i < import_mesh.primitives[0].attributes_count; ++i) {
				const cgltf_attribute& attr = import_mesh.primitives[0].attributes[i];
				switch (attr.type) {
					case cgltf_attribute_type_position: 
						write(Mesh::AttributeSemantic::POSITION);
						break;
					case cgltf_attribute_type_normal: 
						write(Mesh::AttributeSemantic::NORMAL);
						break;
					case cgltf_attribute_type_texcoord: 
						write(Mesh::AttributeSemantic::TEXCOORD0);
						break;
					case cgltf_attribute_type_color: 
						write(Mesh::AttributeSemantic::COLOR0);
						break;
					case cgltf_attribute_type_tangent: 
						write(Mesh::AttributeSemantic::TANGENT);
						break;
					default: ASSERT(false); break;
				}
				switch(attr.data->component_type) {
					case cgltf_component_type_r_32f: write(ffr::AttributeType::FLOAT); break;
					case cgltf_component_type_r_8u: write(ffr::AttributeType::U8); break;
					default: ASSERT(false); break;
				}
				write(getComponentsCount(attr));
			}

			if (is_rigid_animated) {
				write(Mesh::AttributeSemantic::INDICES);
				write(ffr::AttributeType::I16);
				write((u8)4);
				write(Mesh::AttributeSemantic::WEIGHTS);
				write(ffr::AttributeType::FLOAT);
				write((u8)4);
			}

			const cgltf_material* material = import_mesh.primitives[0].material;
			StaticString<MAX_PATH_LENGTH + 128> mat_id(src_info.m_dir, material->name, ".mat");
			const i32 len = stringLength(mat_id.data);
			write(len);
			write(mat_id.data, len);

			const u32 name_len = (u32)stringLength(import_mesh.name);
			write(name_len);
			write(import_mesh.name, name_len);
		};

		for (u32 i = 0; i < data->meshes_count; ++i) {
			writeMesh(data->meshes[i]);
		}
	}

	static u32 getAttributeSize(const cgltf_attribute& attr) {
		const u32 cmp_count = getComponentsCount(attr);

		u32 cmp_size = 0;
		switch (attr.data->component_type) {
			case cgltf_component_type_r_8u:
			case cgltf_component_type_r_8: cmp_size = 1; break;
			case cgltf_component_type_r_16:
			case cgltf_component_type_r_16u: cmp_size = 2; break;
			case cgltf_component_type_r_32u:
			case cgltf_component_type_r_32f: cmp_size = 4; break;
			default: ASSERT(false); break;
		}
		return cmp_size * cmp_count;
	}

	static u32 getVertexSize(const cgltf_data* data, const cgltf_mesh& mesh) {
		u32 size = 0;
		for (u32 j = 0; j < mesh.primitives[0].attributes_count; ++j) {
			const cgltf_attribute& attr = mesh.primitives[0].attributes[j];
			size += getAttributeSize(attr);
		}
		if (isRigidAnimated(data, mesh)) {
			size += sizeof(u16) * 4 + sizeof(Vec4);
		}
		return size;
	}
	
	static Matrix getMeshTransform(cgltf_data* data, const cgltf_mesh& mesh) {
		Matrix res = Matrix::IDENTITY;
		const cgltf_node* node = nullptr;
		for (u32 i = 0; i < data->nodes_count; ++i) {
			if (data->nodes[i].mesh == &mesh) {
				node = &data->nodes[i];
				break;
			}
		}

		if (node) cgltf_node_transform_world(node, &res.m11);
		return res;
	}

	static const cgltf_node& getNode(const cgltf_data* data, const cgltf_mesh& mesh) {
		for (u32 i = 0; i < data->nodes_count; ++i) {
			if(data->nodes[i].mesh == &mesh) return data->nodes[i];
		}
		ASSERT(false);
		return data->nodes[0];
	}

	static bool isAnimated(const cgltf_data* data, const cgltf_node& node) {
		for (u32 i = 0; i < data->animations_count; ++i) {
			const cgltf_animation& anim = data->animations[i];
			for (u32 j = 0; j < anim.channels_count; ++j) {
				if (anim.channels[j].target_node == &node) return true;
			}
		}
		return node.parent && isAnimated(data, *node.parent);
	}

	static bool isRigidAnimated(const cgltf_data* data, const cgltf_mesh& mesh) {
		for (u32 i = 0; i < mesh.primitives[0].attributes_count; ++i) {
			if (mesh.primitives[0].attributes[i].type == cgltf_attribute_type_joints) return false;
		}

		const cgltf_node& node = getNode(data, mesh);
		return isAnimated(data, node);
	}

	u32 getIndex(const cgltf_data* data, const cgltf_node& node) {
		for (u32 i = 0; i < data->nodes_count; ++i) {
			if (&data->nodes[i] == &node) return i;
		}
		ASSERT(false);
		return 0;
	}

	void writeGeometry(cgltf_data* data) {
		AABB aabb = {{0, 0, 0}, {0, 0, 0}};
		float radius_squared = 0;
		OutputMemoryStream vertices_blob(allocator);
		for (u32 i = 0; i < data->meshes_count; ++i) {
			cgltf_mesh& mesh = data->meshes[i];
			const cgltf_accessor* indices = mesh.primitives[0].indices;
			const bool are_indices_16_bit = indices->component_type == cgltf_component_type_r_16u;
			const u32 index_size = are_indices_16_bit ? sizeof(u16) : sizeof(u32);
			write(index_size);
			write(u32(indices->count));
			const u8* buffer = (const u8*)indices->buffer_view->buffer->data;
			write(buffer + indices->buffer_view->offset + indices->offset, index_size * indices->count);
			//aabb.merge(import_mesh.aabb);
			//radius_squared = maximum(radius_squared, import_mesh.radius_squared);
		}

		for (u32 i = 0; i < data->meshes_count; ++i) {
			cgltf_mesh& mesh = data->meshes[i];
			const Matrix mesh_mtx = getMeshTransform(data, mesh);
			Array<u8> vb(allocator);
			const u32 vertex_size = getVertexSize(data, mesh);
			vb.resize(int(vertex_size * mesh.primitives[0].attributes[0].data->count));

			u32 offset = 0;
			for (u32 j = 0; j < mesh.primitives[0].attributes_count; ++j) {
				const cgltf_attribute& attr = mesh.primitives[0].attributes[j];

				const u32 attr_size = getAttributeSize(attr);
				const u8* tmp = (const u8*)attr.data->buffer_view->buffer->data;
				tmp += attr.data->buffer_view->offset;
				tmp += attr.data->offset;
				for(u32 k = 0; k < attr.data->count; ++k) {
					memcpy(&vb[k * vertex_size + offset], tmp, attr_size);
					tmp += attr.data->stride;
				}

				if(attr.type == cgltf_attribute_type_position
					&& attr.data->type == cgltf_type_vec3
					&& attr.data->component_type == cgltf_component_type_r_32f) 
				{
					for(u32 k = 0; k < attr.data->count; ++k) {
						Vec3* p = (Vec3*)&vb[k * vertex_size + offset];
						*p = mesh_mtx.transformPoint(*p);
					}
				}

				if((attr.type == cgltf_attribute_type_normal || attr.type == cgltf_attribute_type_tangent)
					&& attr.data->type == cgltf_type_vec3
					&& attr.data->component_type == cgltf_component_type_r_32f) 
				{
					for(u32 k = 0; k < attr.data->count; ++k) {
						Vec3* p = (Vec3*)&vb[k * vertex_size + offset];
						*p = mesh_mtx.transformVector(*p);
					}
				}

				offset += attr_size;
			}

			if (isRigidAnimated(data, mesh)) {
				const u32 count = (u32)mesh.primitives[0].attributes[0].data->count;
				for(u32 j = 0; j < count; ++j) {
					u16* indices = (u16*)&vb[j * vertex_size + offset];
					Vec4* weights = (Vec4*)&vb[j * vertex_size + offset + sizeof(u16) * 4];
					*weights = Vec4(1, 0, 0, 0);
					indices[0] = getIndex(data, getNode(data, mesh));
					indices[1] = indices[2] = indices[3] = 0;
				}
			}

			write((u32)vb.size());
			write(vb.begin(), vb.byte_size());
		}
		
		// TODO 
		const float bounding_r = FLT_MAX;
		write(bounding_r);
		/*write(sqrtf(radius_squared) * bounding_shape_scale);
		aabb.min *= bounding_shape_scale;
		aabb.max *= bounding_shape_scale;*/
		write(aabb);
	}

	void writeSkeleton(const cgltf_data* data) {
		write((u32)data->nodes_count);

		for (u32 i = 0; i < data->nodes_count; ++i) {
			const cgltf_node& node = data->nodes[i];
			u32 len = (u32)stringLength(node.name);
			write(len);
			write(node.name, len);

			if (!node.parent) {
				write((i32)-1);
			}
			else {
				const i32 idx = i32(node.parent - data->nodes);
				write(idx);
			}
			// TODO
			/*
			const ImportMesh* mesh = getAnyMeshFromBone(node, int(&node - bones.begin()));
			Matrix tr = toLumix(getBindPoseMatrix(mesh, node));
			tr.normalizeScale();

			Quat q = fixOrientation(tr.getRotation());
			Vec3 t = fixOrientation(tr.getTranslation());
			write(t * cfg.mesh_scale);
			write(q);*/

			Matrix mtx;
			cgltf_node_transform_world(&node, &mtx.m11);

			const Vec3 t = mtx.getTranslation();
			const Quat r = mtx.getRotation();
			write(t);
			write(r);
		}
	}

	void writeLODs(const cgltf_data* data) {
		const u32 count = 1;
		write(count);
		const u32 to_mesh = (u32)data->meshes_count - 1;
		write(to_mesh);
		const float factor = FLT_MAX;
		write(factor);
	}

	IAllocator& allocator;
	StaticString<MAX_PATH_LENGTH> src;
	OutputMemoryStream out;
};


struct CompilerPlugin : AssetCompiler::IPlugin {
	struct Meta
	{
		float scale = 1;
		bool split = false;
	};

	CompilerPlugin(StudioApp& app) 
		: app(app) 
		, in_progress(app.getWorldEditor().getAllocator())
	{
		app.getAssetCompiler().registerExtension("gltf", Model::TYPE);	
		app.getAssetCompiler().registerExtension("glb", Model::TYPE);	
	}

	~CompilerPlugin() {
		JobSystem::wait(subres_signal);
	}

	static const cgltf_animation_channel* getAnimChannel(const cgltf_animation& anim
		, const cgltf_node& node
		, cgltf_animation_path_type type) 
	{
		for (u32 i = 0; i < anim.channels_count; ++i) {
			if (anim.channels[i].target_node == &node && anim.channels[i].target_path == type) return &anim.channels[i];
		}
		return nullptr;
	}

	static void writeTimes(const cgltf_animation_channel* ch, Ref<OutputMemoryStream> out) {
		const cgltf_accessor* times = ch->sampler->input;
		const float* data = (const float*)((const u8*)times->buffer_view->buffer->data + times->buffer_view->offset);
		const float max = times->max[0];
		for (u32 i = 0; i < times->count; ++i) {
			const float t = data[i];
			const u16 f = u16(0xffFe * (t / max));
			out->write(f);
		}
	}

	static void writeAccessor(const cgltf_accessor* data, Ref<OutputMemoryStream> out) {
		const u8* mem = (const u8*)data->buffer_view->buffer->data + data->buffer_view->offset + data->offset;
		out->write(mem, data->stride * data->count);
	}

	void writeAnimations(const cgltf_data* data, const char* gltf_path) {
		AssetCompiler& compiler = app.getAssetCompiler();
		WorldEditor& editor = app.getWorldEditor();
		FileSystem& fs = editor.getEngine().getFileSystem();
		IAllocator& allocator = app.getWorldEditor().getAllocator();
		OutputMemoryStream out(allocator);
		for (u32 i = 0; i < data->animations_count; ++i) {
			const cgltf_animation& anim = data->animations[i];
			out.clear();
			for (u32 j = 0; j < data->nodes_count; ++j) {
				const cgltf_node& node = data->nodes[j];
				const cgltf_animation_channel* pos = getAnimChannel(anim, node, cgltf_animation_path_type_translation);
				const cgltf_animation_channel* rot = getAnimChannel(anim, node, cgltf_animation_path_type_rotation);
				if(!pos && !rot) continue;

				const u32 name_hash = crc32(node.name);
				out.write(name_hash);

				if(pos) {
					out.write((u32)pos->sampler->input->count);
					writeTimes(pos, Ref(out));
					writeAccessor(pos->sampler->output, Ref(out));
				}
				else {
					out.write((u32)0);
				}

				if(rot) {
					out.write((u32)rot->sampler->input->count);
					writeTimes(rot, Ref(out));
					writeAccessor(rot->sampler->output, Ref(out));
				}
				else {
					out.write((u32)0);
				}
			}
			
			StaticString<MAX_PATH_LENGTH> res_locator(anim.name, ":", gltf_path);
			compiler.writeCompiledResource(res_locator, Span<u8>((u8*)out.getData(), (int)out.getPos()));
		}
	}

	void writeMaterials(const cgltf_data* data, const char* dir) {
		WorldEditor& editor = app.getWorldEditor();
		FileSystem& fs = editor.getEngine().getFileSystem();
		// TODO do not overwrite existing materials
		OutputMemoryStream out(editor.getAllocator());
		for (u32 i = 0; i < data->materials_count; ++i) {
			const cgltf_material& mat = data->materials[i];
			out.clear();
			auto writeString = [&out](const char* str){
				out.write(str, stringLength(str));
			};
			writeString("shader \"pipelines/standard.shd\"\n");
			if (mat.has_pbr_metallic_roughness) {
				writeString("texture \"");
				if (mat.pbr_metallic_roughness.base_color_texture.texture) {
					writeString(mat.pbr_metallic_roughness.base_color_texture.texture->image->uri);
				}
				writeString("\"\n");

				writeString("texture \"");
				if (mat.normal_texture.texture) {
					writeString(mat.normal_texture.texture->image->uri);
				}
				writeString("\"\n");

				// TODO other textures
			}

			StaticString<MAX_PATH_LENGTH> out_path(fs.getBasePath(), dir, mat.name, ".mat");
			OS::OutputFile file;
			if(!file.open(out_path)) {
				logError("gltf") << "Could not create " << out_path;
				continue;
			}
			file.write(out.getData(), out.getPos());
			file.close();
		}
	}

	bool compile(const Path& src) override {
		WorldEditor& editor = app.getWorldEditor();
		FileSystem& fs = editor.getEngine().getFileSystem();
		AssetCompiler& compiler = app.getAssetCompiler();

		Array<u8> content(editor.getAllocator());
		if (!fs.getContentSync(Path(src), Ref(content))) {
			logError("gltf") << "Could not load " << src;
			return false;
		}

		cgltf_data* gltf_data = nullptr;
		cgltf_options options = {};
		if (cgltf_parse(&options, content.begin(), content.byte_size(), &gltf_data) != cgltf_result_success) {
			logError("gltf") << "Failed to parse " << src;
			return false;
		}

		Array<Array<u8>> buffers(editor.getAllocator());
		for (u32 i = 0; i < gltf_data->buffers_count; ++i) {
			buffers.emplace(editor.getAllocator());
		}

		const PathUtils::FileInfo src_fi(src.c_str());
		for (u32 i = 0; i < gltf_data->buffers_count; ++i) {
			const char* uri = gltf_data->buffers[i].uri;
			const StaticString<MAX_PATH_LENGTH> path(src_fi.m_dir, uri);
			if (!fs.getContentSync(Path(path), Ref(buffers[i]))) {
				logError("gltf") << "Could not load " << uri;
				cgltf_free(gltf_data);
				return false;
			}
		}

		for (u32 i = 0; i < gltf_data->buffers_count; ++i) {
			ASSERT(!gltf_data->buffers[i].data);
			gltf_data->buffers[i].data = buffers[i].begin();
		}
		
		ModelWriter writer(src.c_str(), editor.getAllocator());
		writer.writeModelHeader();
		writer.writeMeshes(gltf_data);
		writer.writeGeometry(gltf_data);
		writer.writeSkeleton(gltf_data);
		writer.writeLODs(gltf_data);
		writeMaterials(gltf_data, src_fi.m_dir);
		writeAnimations(gltf_data, src.c_str());

		for (u32 i = 0; i < gltf_data->buffers_count; ++i) {
			gltf_data->buffers[i].data = nullptr;
		}

		cgltf_free(gltf_data);
		
		Span<u8> compiled_data((u8*)writer.out.getData(), (int)writer.out.getPos());
		return compiler.writeCompiledResource(src.c_str(), compiled_data);
	}
	
	Meta getMeta(const Path& path) const
	{
		Meta meta;
		app.getAssetCompiler().getMeta(path, [&](lua_State* L){
			LuaWrapper::getOptionalField(L, LUA_GLOBALSINDEX, "scale", &meta.scale);
			LuaWrapper::getOptionalField(L, LUA_GLOBALSINDEX, "split", &meta.split);
		});
		return meta;
	}

	void addSubresources(AssetCompiler& compiler, const char* path) {
		compiler.addResource(Model::TYPE, path);
		
		const Meta meta = getMeta(Path(path));
		struct JobData {
			CompilerPlugin* plugin;
			StaticString<MAX_PATH_LENGTH> path;
			Meta meta;
		};
		JobData* data = LUMIX_NEW(app.getWorldEditor().getAllocator(), JobData);
		data->plugin = this;
		data->path = path;
		data->meta = meta;
		JobSystem::runEx(data, [](void* ptr) {
			JobData* data = (JobData*)ptr;
			CompilerPlugin* plugin = data->plugin;
			WorldEditor& editor = plugin->app.getWorldEditor();
			FileSystem& fs = editor.getEngine().getFileSystem();
			AssetCompiler& compiler = plugin->app.getAssetCompiler();
			
			Array<u8> content(editor.getAllocator());
			if (!fs.getContentSync(Path(data->path), Ref(content))) {
				logError("gltf") << "Could not load " << data->path;
				LUMIX_DELETE(editor.getAllocator(), data);
				return;
			}

			cgltf_data* gltf_data = nullptr;
			cgltf_options options = {};
			if (cgltf_parse(&options, content.begin(), content.byte_size(), &gltf_data) != cgltf_result_success) {
				logError("gltf") << "Failed to parse " << data->path;
				LUMIX_DELETE(editor.getAllocator(), data);
				return;
			}

			if(data->meta.split) {
				for (u32 i = 0; i < gltf_data->meshes_count; ++i) {
					const cgltf_mesh& mesh = gltf_data->meshes[i];
					char mesh_name[256];
					StaticString<MAX_PATH_LENGTH> tmp(mesh_name, ":", data->path);
					compiler.addResource(Model::TYPE, tmp);
				}
			}

			for (u32 i = 0; i < gltf_data->animations_count; ++i) {
				const cgltf_animation& anim = gltf_data->animations[i];
				StaticString<MAX_PATH_LENGTH> tmp(anim.name, ":", data->path);
				compiler.addResource(Animation::TYPE, tmp);
			}

			cgltf_free(gltf_data);
			LUMIX_DELETE(editor.getAllocator(), data);
		}, &subres_signal, JobSystem::INVALID_HANDLE, 2);		
	}

	JobSystem::SignalHandle subres_signal = JobSystem::INVALID_HANDLE;
	StudioApp& app;
	Array<FileSystem::AsyncHandle> in_progress;
};


struct StudioAppPlugin : StudioApp::IPlugin {
	StudioAppPlugin(StudioApp& app) : app(app) {}

	~StudioAppPlugin() {
		IAllocator& allocator = app.getWorldEditor().getAllocator();
		AssetCompiler& compiler = app.getAssetCompiler();
		compiler.removePlugin(*compiler_plugin);
		LUMIX_DELETE(allocator, compiler_plugin);
	}

	void init() override {
		IAllocator& allocator = app.getWorldEditor().getAllocator();
		AssetCompiler& compiler = app.getAssetCompiler();

		compiler_plugin = LUMIX_NEW(allocator, CompilerPlugin)(app);

		const char* exts[] = {"gltf", "glb", nullptr};
		compiler.addPlugin(*compiler_plugin, exts);
	}

	const char* getName() const override { return "gtlf_import"; }

	StudioApp& app;
	CompilerPlugin* compiler_plugin;
};

} // anonoymous namespace


LUMIX_STUDIO_ENTRY(gltf_import)
{
	auto& allocator = app.getWorldEditor().getAllocator();
	return LUMIX_NEW(allocator, StudioAppPlugin)(app);
}
