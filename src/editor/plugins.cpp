#define _CRT_SECURE_NO_WARNINGS
#define CGLTF_IMPLEMENTATION
#include "cgltf.h"
#undef _CRT_SECURE_NO_WARNINGS

#include "animation/animation.h"
#include "editor/asset_compiler.h"
#include "editor/world_editor.h"
#include "editor/studio_app.h"
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
			const u32 attribute_count = (u32)import_mesh.primitives[0].attributes_count;
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
/*			if (import_mesh.is_skinned)
			{
				i32 indices_attr = 6;
				write(indices_attr);
				i32 weight_attr = 7;
				write(weight_attr);
			}*/

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

	static u32 getVertexSize(const cgltf_mesh& mesh) {
		u32 size = 0;
		for (u32 j = 0; j < mesh.primitives[0].attributes_count; ++j) {
			const cgltf_attribute& attr = mesh.primitives[0].attributes[j];
			size += getAttributeSize(attr);
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
			const u32 vertex_size = getVertexSize(mesh);
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

	void writeSkeleton() {
		write((u32)0);
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

	void writeMaterials(const cgltf_data* data, const char* dir) {
		WorldEditor& editor = app.getWorldEditor();
		FileSystem& fs = editor.getEngine().getFileSystem();
		for (u32 i = 0; i < data->materials_count; ++i) {
			const cgltf_material& mat = data->materials[i];
			OutputMemoryStream out(editor.getAllocator());
			auto writeString = [&out](const char* str){
				out.write(str, stringLength(str));
			};
			writeString("shader \"pipelines/standard.shd\"\n");

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
		writer.writeSkeleton();
		writer.writeLODs(gltf_data);
		writeMaterials(gltf_data, src_fi.m_dir);

		for (u32 i = 0; i < gltf_data->buffers_count; ++i) {
			gltf_data->buffers[i].data = nullptr;
		}

		cgltf_free(gltf_data);
		
		const char* output_dir = compiler.getCompiledDir();
		StaticString<MAX_PATH_LENGTH> out_path(fs.getBasePath(), output_dir, src.getHash(), ".res");
		OS::OutputFile file;
		if (!file.open(out_path)) {
			logError("gltf") << "Could not save " << out_path << "(" << src << ")";
			return false;
		}

		const bool written = file.write(writer.out.getData(), writer.out.getPos());
		file.close();

		if(!written) logError("gltf") << "Could not save " << out_path << "(" << src << ")";
		
		return written;
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
