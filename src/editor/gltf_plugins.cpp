#define _CRT_SECURE_NO_WARNINGS
#include "animation/animation.h"
#include "core/crt.h"
#include "core/hash.h"
#include "core/job_system.h"
#include "core/log.h"
#include "core/math.h"
#include "core/os.h"
#include "core/path.h"
#include "core/profiler.h"
#include "core/tokenizer.h"
#include "editor/asset_browser.h"
#include "editor/asset_compiler.h"
#include "editor/editor_asset.h"
#include "editor/studio_app.h"
#include "editor/utils.h"
#include "editor/world_editor.h"
#include "engine/component_uid.h"
#include "engine/engine.h"
#include "engine/file_system.h"
#include "engine/resource_manager.h"
#include "engine/world.h"
#include "renderer/editor/fbx_importer.h"
#include "renderer/editor/model_importer.h"
#include "renderer/editor/model_meta.h"
#include "renderer/editor/world_viewer.h"
#include "renderer/model.h"
#include "renderer/render_module.h"

#define CGLTF_IMPLEMENTATION
#include "cgltf.h"
#undef _CRT_SECURE_NO_WARNINGS

using namespace Lumix;

static const ComponentType MODEL_INSTANCE_TYPE = reflection::getComponentType("model_instance");

namespace {

static AttributeSemantic toLumix(cgltf_attribute_type type) {
	switch (type) {
		case cgltf_attribute_type_position: return AttributeSemantic::POSITION;
		case cgltf_attribute_type_normal: return AttributeSemantic::NORMAL;
		case cgltf_attribute_type_tangent: return AttributeSemantic::TANGENT;
		case cgltf_attribute_type_texcoord: return AttributeSemantic::TEXCOORD0;
		case cgltf_attribute_type_color: return AttributeSemantic::COLOR0;
		case cgltf_attribute_type_joints: return AttributeSemantic::JOINTS;
		case cgltf_attribute_type_weights: return AttributeSemantic::WEIGHTS;
		default: ASSERT(false); return AttributeSemantic::NONE;
	}
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

struct GLTFImporter : ModelImporter {
	GLTFImporter(StudioApp& app)
		: ModelImporter(app)
		, m_app(app)
		, m_allocator(app.getAllocator())
		, m_binaries(m_allocator)
	{}

	~GLTFImporter() {
		if (!m_src_data) return;
		for (u32 i = 0; i < m_src_data->buffers_count; ++i) {
			m_src_data->buffers[i].data = nullptr;
		}
		cgltf_free(m_src_data);
	}

	template <typename T>
	static T evalCurve(const cgltf_animation_channel& channel, float time) {
		const cgltf_accessor* times = channel.sampler->input;
		const float* data = (const float*)((const u8*)times->buffer_view->buffer->data + times->buffer_view->offset + times->offset);
		for (u32 i = 0; i < times->count; ++i) {
			if (data[i] > time) {
				const cgltf_accessor* pos_data = channel.sampler->output;
				ASSERT(pos_data->stride == sizeof(T));
				const u8* ptr = (const u8*)pos_data->buffer_view->buffer->data + pos_data->buffer_view->offset + pos_data->offset + i * pos_data->stride;
				T result;
				memcpy(&result, ptr, sizeof(result));
				return result;
			}
		}
		
		const cgltf_accessor* pos_data = channel.sampler->output;
		const u8* ptr = (const u8*)pos_data->buffer_view->buffer->data + pos_data->buffer_view->offset + pos_data->offset + (times->count - 1) * pos_data->stride;
		T result;
		memcpy(&result, ptr, sizeof(result));
		return result;
	}

	void fillTracks(const ImportAnimation& anim
		, Array<Array<Key>>& tracks
		, u32 from_sample
		, u32 num_samples
		) const override
	{
		tracks.reserve(m_bones.size());
		ASSERT(m_src_data->nodes_count == m_bones.size());
		
		for (u32 bone_idx = 0; bone_idx < (u32)m_bones.size(); ++bone_idx) {
			tracks.emplace(m_allocator);
			const u32 j = u32(m_bones[bone_idx].id - 1);
			const cgltf_node& node = m_src_data->nodes[j];
			const cgltf_animation& src_anim = m_src_data->animations[anim.index];
			const cgltf_animation_channel* pos = getAnimChannel(src_anim, node, cgltf_animation_path_type_translation);
			const cgltf_animation_channel* rot = getAnimChannel(src_anim, node, cgltf_animation_path_type_rotation);
			if(!pos && !rot) continue;

			Array<Key>& keys = tracks[bone_idx];
			keys.resize(num_samples);

			for (u32 i = 0; i < num_samples; ++i) {
				keys[i].pos = pos ? evalCurve<Vec3>(*pos, (from_sample + i) / (float)anim.fps) : Vec3(0);
				keys[i].rot = rot ? evalCurve<Quat>(*rot, (from_sample + i) / (float)anim.fps) : Quat::IDENTITY;
			}
		}
	}

	const Bone* getBoneByID(u64 id) const {
		for (const Bone& bone : m_bones) {
			if (bone.id == id) return &bone;
		}
		return nullptr;
	}

	bool parseSimple(const Path& src) override {
		return parse(src, nullptr);
	}

	bool parse(const Path& src, const ModelMeta& meta) override {
		return parse(src, &meta);
	}

	bool parse(const Path& src, const ModelMeta* meta) {
		PROFILE_FUNCTION();
		FileSystem& fs = m_app.getEngine().getFileSystem();

		OutputMemoryStream content(m_allocator);
		if (!fs.getContentSync(src, content)) {
			logError("Could not load ", src);
			return false;
		}

		// TODO allocator
		cgltf_options options = {};
		if (cgltf_parse(&options, content.data(), content.size(), &m_src_data) != cgltf_result_success) {
			logError("Could not parse ", src);
			return false;
		}

		for (u32 i = 0; i < m_src_data->buffers_count; ++i) {
			m_binaries.emplace(m_allocator);
		}

		StringView dir = Path::getDir(src);
		for (u32 i = 0; i < m_src_data->buffers_count; ++i) {
			const char* uri = m_src_data->buffers[i].uri;
			
			if (strncmp(uri, "data:", 5) == 0) {
				const char* comma = strchr(uri, ',');
				if (comma && comma - uri >= 7 && strncmp(comma - 7, ";base64", 7) == 0) {
					cgltf_result res = cgltf_load_buffer_base64(&options, m_src_data->buffers[i].size, comma + 1, &m_src_data->buffers[i].data);
					if (res != cgltf_result_success) {
						logError(src, ": failed to load buffer");
						return false;
					}
				}
				else {
					logError(src, ": Unknown buffer format");
					return false;
				}
			}
			else {
				const StaticString<MAX_PATH> path(dir, uri);
				if (!fs.getContentSync(Path(path), m_binaries[i])) {
					logError("Failed to load ", path);
					cgltf_free(m_src_data);
					m_src_data = nullptr;
					return false;
				}
				m_src_data->buffers[i].data = m_binaries[i].getMutableData();
			}
		}

		StringView src_dir = Path::getDir(src);

		for (u32 mesh_index = 0; mesh_index < m_src_data->meshes_count; ++mesh_index) {
			const cgltf_mesh& src_mesh = m_src_data->meshes[mesh_index];

			for (u32 primitive_index = 0; primitive_index < src_mesh.primitives_count; ++primitive_index) {
				ImportMesh& mesh = m_meshes.emplace(m_allocator);
				ImportGeometry& geom = m_geometries.emplace(m_allocator);
				mesh.mesh_index = mesh_index;
				mesh.geometry_idx = m_geometries.size() - 1;
				geom.material_index = m_materials.size();
				geom.submesh = primitive_index;
			
				const cgltf_primitive& primitive = src_mesh.primitives[primitive_index];
				ASSERT(primitive.type == cgltf_primitive_type_triangles);

				// TODO bake vertex ao, rigid animated
				// TODO make sure position is first and is Vec3
				// TODO makes sure normal & tangent are in proper format

				geom.attributes.push({
					.semantic = AttributeSemantic::POSITION,
					.type = gpu::AttributeType::FLOAT,
					.num_components = 3
				});

				// TODO move to postprocess
				for (u32 i = 0; i < primitive.attributes_count; ++i) {
					AttributeDesc desc;
					const cgltf_attribute& attr = primitive.attributes[i];
					if (attr.type == cgltf_attribute_type_position) continue;
					switch (attr.type) {
						case cgltf_attribute_type_normal: desc.semantic = AttributeSemantic::NORMAL; break;
						case cgltf_attribute_type_texcoord: desc.semantic = AttributeSemantic::TEXCOORD0; break;
						case cgltf_attribute_type_color: desc.semantic = AttributeSemantic::COLOR0; break;
						case cgltf_attribute_type_tangent: desc.semantic = AttributeSemantic::TANGENT; break;
						case cgltf_attribute_type_weights: desc.semantic = AttributeSemantic::WEIGHTS; break;
						case cgltf_attribute_type_joints: desc.semantic = AttributeSemantic::JOINTS; break;
						case cgltf_attribute_type_position:
						case cgltf_attribute_type_invalid: ASSERT(false); break;
					}

					switch(attr.data->component_type) {
						case cgltf_component_type_r_32f: desc.type = gpu::AttributeType::FLOAT; break;
						case cgltf_component_type_r_8u: desc.type = gpu::AttributeType::U8; break;
						case cgltf_component_type_r_8: desc.type = gpu::AttributeType::I8; break;
						case cgltf_component_type_r_16: desc.type = gpu::AttributeType::I16; break;
						case cgltf_component_type_r_16u: desc.type = gpu::AttributeType::U16; break;
						default: ASSERT(false); break;
					}
					desc.num_components = getComponentsCount(attr);
					if (desc.semantic == AttributeSemantic::JOINTS) {
						desc.type = gpu::AttributeType::U16;
						desc.num_components = 4;
					}
					geom.attributes.push(desc);
				}

				geom.vertex_size = 0;
				for (const AttributeDesc& attr : geom.attributes) {
					geom.vertex_size += gpu::getSize(attr.type) * attr.num_components;
				}
				mesh.name = src_mesh.name ? src_mesh.name : "default";

				ImportMaterial& material = m_materials.emplace(m_allocator);
				const cgltf_material* src_mat = primitive.material;
				for (ImportTexture& t : material.textures) t.import = false;
				if (src_mat) {
					material.name = src_mat->name;

					if (src_mat->has_pbr_metallic_roughness) {
						const cgltf_pbr_metallic_roughness& pbr = primitive.material->pbr_metallic_roughness;
						material.diffuse_color = Vec3(pbr.base_color_factor[0], pbr.base_color_factor[1], pbr.base_color_factor[2]);
						if (pbr.base_color_texture.texture) {
							material.textures[ImportTexture::DIFFUSE].import = true;
							material.textures[ImportTexture::DIFFUSE].src = src_dir;
							material.textures[ImportTexture::DIFFUSE].src.append(pbr.base_color_texture.texture->image->uri);
						}
					}

					if (src_mat->normal_texture.texture) {
						material.textures[ImportTexture::NORMAL].import = true;
						material.textures[ImportTexture::NORMAL].src = src_dir;
						material.textures[ImportTexture::NORMAL].src.append(src_mat->normal_texture.texture->image->uri);
					}
				}
				else {
					logError(src, ": Mesh without material - ", mesh.name);
					return false;
				}
			}
		}

		m_bones.reserve((u32)m_src_data->nodes_count);
		for (u32 i = 0; i < m_src_data->nodes_count; ++i) {
			Bone& bone = m_bones.emplace(m_allocator);
			bone.name = m_src_data->nodes[i].name;
			bone.id = i + 1;
			bone.parent_id = m_src_data->nodes[i].parent ? u64(m_src_data->nodes[i].parent - m_src_data->nodes) + 1 : 0;
			bone.bind_pose_matrix = Matrix::IDENTITY;
			const cgltf_node& node = m_src_data->nodes[i];
			if (node.has_matrix) {
				memcpy(&bone.bind_pose_matrix, &node.matrix, sizeof(bone.bind_pose_matrix));	
			}
			else {
				Vec3 t = {0, 0, 0};
				Quat r = Quat::IDENTITY;
				if (node.has_translation) memcpy(&t, node.translation, sizeof(t));
				if (node.has_rotation) memcpy(&r, node.rotation, sizeof(r));
				bone.bind_pose_matrix = Matrix(t, r);
			}
		}

		sortBones();

		for (u32 i = 0; i < (u32)m_bones.size(); ++i) {
			const Bone* parent = getBoneByID(m_bones[i].parent_id);
			if (!parent) continue;
			m_bones[i].bind_pose_matrix = parent->bind_pose_matrix * m_bones[i].bind_pose_matrix;
		}

		for (u32 i = 0; i < m_src_data->animations_count; ++i) {
			ImportAnimation& anim = m_animations.emplace();
			anim.index = i;
			anim.name = m_src_data->animations[i].name;
			anim.fps = 60; // TODO
			anim.length = m_src_data->animations[i].samplers[0].input->max[0];
		}

		postprocess(*meta, src);

		return true;
	}

	void sortBones() {
		const int count = m_bones.size();
		u32 first_nonroot = 0;
		for (i32 i = 0; i < count; ++i) {
			if (m_bones[i].parent_id == 0) {
				swap(m_bones[i], m_bones[first_nonroot]);
				++first_nonroot;
			}
		}

		for (i32 i = 0; i < count; ++i) {
			for (int j = i + 1; j < count; ++j) {
				if (m_bones[i].parent_id == m_bones[j].id) {
					swap(m_bones[j], m_bones[i]);
					--i;
					break;
				}
			}
		}
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

		if (node) cgltf_node_transform_world(node, &res.columns[0].x);
		return res;
	}

	void postprocess(const ModelMeta& meta, const Path& path) {
		u32 bone_remap[1024];
		for (i32 i = 0; i < m_bones.size(); ++i) {
			bone_remap[m_bones[i].id - 1] = i;
		}
		
		for (ImportMesh& mesh : m_meshes) {
			ImportGeometry& geom = m_geometries[mesh.geometry_idx];
			const cgltf_mesh& src_mesh = m_src_data->meshes[mesh.mesh_index];
			const cgltf_primitive& primitive = src_mesh.primitives[geom.submesh];
			const cgltf_accessor* indices = primitive.indices;
			// TODO handle indices == nullptr
			switch (indices->component_type) {
				case cgltf_component_type_r_16u: geom.index_size = 2; break;
				case cgltf_component_type_r_32u: geom.index_size = 4; break;
				default: ASSERT(false); break;
			}
			geom.indices.resize((u32)indices->count);
			// TODO are all these offsets in bytes?
			const u8* ptr = (const u8*)indices->buffer_view->buffer->data + indices->buffer_view->offset + indices->offset;
			for (u32 i = 0; i < indices->count; ++i) {
				switch (geom.index_size) {
					case 2: geom.indices[i] = *(u16*)(ptr + i * 2); break;
					case 4: geom.indices[i] = *(u16*)(ptr + i * 4); break;
					default: ASSERT(false); break;
				}
			}
			
			const Matrix mesh_mtx = getMeshTransform(m_src_data, src_mesh);
			
			geom.vertex_buffer.resize(geom.vertex_size * primitive.attributes[0].data->count);
			for (u32 j = 0; j < primitive.attributes_count; ++j) {
				u32 attr_offset = 0;
				for (AttributeDesc& desc : geom.attributes) {
					if (desc.semantic == toLumix(primitive.attributes[j].type)) break;
					attr_offset += gpu::getSize(desc.type) * desc.num_components;
				}

				const cgltf_attribute& attr = primitive.attributes[j];
				u32 attr_size = getAttributeSize(attr);
				const u8* src_data = (const u8*)attr.data->buffer_view->buffer->data + attr.data->buffer_view->offset + attr.data->offset;
				u8* vb = geom.vertex_buffer.getMutableData();
				
				if (attr.type == cgltf_attribute_type_joints) {
					if (attr.data->component_type == cgltf_component_type_r_8u && attr.data->type == cgltf_type_vec4) {
						for (u32 k = 0; k < attr.data->count; ++k) {
							u8 joints_u8[4];
							u16 joints_u16[4];
							memcpy(joints_u8, src_data, attr_size);
							for(u32 i = 0; i < 4; ++i) joints_u16[i] = bone_remap[joints_u8[i]];
							memcpy(&vb[k * geom.vertex_size + attr_offset], joints_u16, sizeof(joints_u16));
							src_data += attr.data->stride;
						}
						attr_size = sizeof(u16) * 4;
					}
					else if (attr.data->component_type == cgltf_component_type_r_16u && attr.data->type == cgltf_type_vec4) {
						for (u32 k = 0; k < attr.data->count; ++k) {
							u16 joints[4];
							memcpy(joints, src_data, attr_size);
							for(u32 i = 0; i < 4; ++i) joints[i] = bone_remap[joints[i]];
							memcpy(&vb[k * geom.vertex_size + attr_offset], joints, sizeof(joints));
							src_data += attr.data->stride;
						}
					}
					else {
						ASSERT(false);
					}
				}
				else {
					for (u32 k = 0; k < attr.data->count; ++k) {
						memcpy(&vb[k * geom.vertex_size + attr_offset], src_data, attr_size);
						src_data += attr.data->stride;
					}
				}

				if(attr.type == cgltf_attribute_type_position
					&& attr.data->type == cgltf_type_vec3
					&& attr.data->component_type == cgltf_component_type_r_32f) 
				{
					for(u32 k = 0; k < attr.data->count; ++k) {
						Vec3* p = (Vec3*)&vb[k * geom.vertex_size + attr_offset];
						*p = mesh_mtx.transformPoint(*p);
					}
				}

				if((attr.type == cgltf_attribute_type_normal || attr.type == cgltf_attribute_type_tangent)
					&& attr.data->type == cgltf_type_vec3
					&& attr.data->component_type == cgltf_component_type_r_32f) 
				{
					for(u32 k = 0; k < attr.data->count; ++k) {
						Vec3* p = (Vec3*)&vb[k * geom.vertex_size + attr_offset];
						*p = mesh_mtx.transformVector(*p);
					}
				}
			}
		}
		
		postprocessCommon(meta);
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

	StudioApp& m_app;
	IAllocator& m_allocator;
	cgltf_data* m_src_data = nullptr;
	Array<OutputMemoryStream> m_binaries;
};


struct GLTFPlugin : AssetBrowser::IPlugin, AssetCompiler::IPlugin {
	struct EditorWindow : AssetEditorWindow, SimpleUndoRedo {
		EditorWindow(const Path& path, GLTFPlugin& plugin)
			: AssetEditorWindow(plugin.m_app)
			, SimpleUndoRedo(plugin.m_app.getAllocator())
			, m_path(path)
			, m_plugin(plugin)
			, m_viewer(plugin.m_app)
		{
			StudioApp& app = plugin.m_app;
			Engine& engine = app.getEngine();
			m_resource = engine.getResourceManager().load<Model>(path);

			auto* render_module = static_cast<RenderModule*>(m_viewer.m_world->getModule(MODEL_INSTANCE_TYPE));
			render_module->setModelInstancePath(*m_viewer.m_mesh, m_resource->getPath());
		}

		void deserialize(InputMemoryStream& blob) override { ASSERT(false); }
		void serialize(OutputMemoryStream& blob) override { ASSERT(false); }
		void windowGUI() override {}
		const Path& getPath() override { return m_path; }
		const char* getName() const override { return "gltf"; }

		Path m_path;
		GLTFPlugin& m_plugin;
		WorldViewer m_viewer;
		Model* m_resource;
	};

	struct Meta {
		float scale = 1;
		bool split = false;
	};

	GLTFPlugin(StudioApp& app) 
		: m_app(app) 
	{
		AssetCompiler& compiler = app.getAssetCompiler();
		compiler.registerExtension("gltf", Model::TYPE);
		compiler.registerExtension("glb", Model::TYPE);
		const char* exts[] = { "gltf", "glb" };
		compiler.addPlugin(*this, Span(exts));
		app.getAssetBrowser().addPlugin(*this, Span(exts));
	}

	~GLTFPlugin() {
		m_app.getAssetCompiler().removePlugin(*this);
		m_app.getAssetBrowser().removePlugin(*this);
		jobs::wait(&m_subres_signal);
	}

	void openEditor(const Path& path) override {
		IAllocator& allocator = m_app.getAllocator();
		UniquePtr<EditorWindow> win = UniquePtr<EditorWindow>::create(allocator, path, *this);
		m_app.getAssetBrowser().addWindow(win.move());
	}

	const char* getLabel() const override {
		return "Model";
	}

	ResourceType getResourceType() const override {
		return Model::TYPE;
	}

	bool compile(const Path& src) override {
		GLTFImporter writer(m_app);
		ModelMeta meta(m_app.getAllocator());
		meta.skeleton = src;
		if (!writer.parse(src, &meta)) return false;

		bool result = writer.write(src, meta);
		result = result && writer.writeMaterials(src, meta, false);
		return result;
	}
	
	Meta getMeta(const Path& path) const
	{
		Meta meta;
		OutputMemoryStream blob(m_app.getAllocator());
		if (m_app.getAssetCompiler().getMeta(path, blob)) {
			StringView sv((const char*)blob.data(), (u32)blob.size());
			const ParseItemDesc descs[] = {
				{"scale", &meta.scale},
				{"split", &meta.split},
			};
			parse(sv, path.c_str(), descs);
		}
		return meta;
	}

	void addSubresources(AssetCompiler& compiler, const Path& path) {
		compiler.addResource(Model::TYPE, path);
		
		const Meta meta = getMeta(path);
		struct JobData {
			GLTFPlugin* plugin;
			Path path;
			Meta meta;
		};
		JobData* data = LUMIX_NEW(m_app.getWorldEditor().getAllocator(), JobData);
		data->plugin = this;
		data->path = path;
		data->meta = meta;
		jobs::run(data, [](void* ptr) {
			JobData* data = (JobData*)ptr;
			GLTFPlugin* plugin = data->plugin;
			WorldEditor& editor = plugin->m_app.getWorldEditor();
			FileSystem& fs = editor.getEngine().getFileSystem();
			AssetCompiler& compiler = plugin->m_app.getAssetCompiler();
			
			OutputMemoryStream content(editor.getAllocator());
			if (!fs.getContentSync(data->path, content)) {
				logError("Could not load ", data->path);
				LUMIX_DELETE(editor.getAllocator(), data);
				return;
			}

			cgltf_data* gltf_data = nullptr;
			cgltf_options options = {};
			if (cgltf_parse(&options, content.data(), content.size(), &gltf_data) != cgltf_result_success) {
				logError("Failed to parse ", data->path);
				LUMIX_DELETE(editor.getAllocator(), data);
				return;
			}

			if(data->meta.split) {
				for (u32 i = 0; i < gltf_data->meshes_count; ++i) {
					const cgltf_mesh& mesh = gltf_data->meshes[i];
					char mesh_name[256];
					Path tmp(mesh_name, ":", data->path);
					compiler.addResource(Model::TYPE, tmp);
				}
			}

			for (u32 i = 0; i < gltf_data->animations_count; ++i) {
				const cgltf_animation& anim = gltf_data->animations[i];
				Path tmp(anim.name, ".ani:", data->path);
				compiler.addResource(Animation::TYPE, tmp);
			}

			cgltf_free(gltf_data);
			LUMIX_DELETE(editor.getAllocator(), data);
		}, &m_subres_signal, 2);		
	}

	jobs::Counter m_subres_signal;
	StudioApp& m_app;
};


struct StudioAppPlugin : StudioApp::IPlugin {
	StudioAppPlugin(StudioApp& app) : app(app) {}

	~StudioAppPlugin() {
		IAllocator& allocator = app.getWorldEditor().getAllocator();
		AssetCompiler& compiler = app.getAssetCompiler();
		compiler.removePlugin(*plugin);
		LUMIX_DELETE(allocator, plugin);
	}

	void init() override {
		IAllocator& allocator = app.getWorldEditor().getAllocator();
		AssetCompiler& compiler = app.getAssetCompiler();

		plugin = LUMIX_NEW(allocator, GLTFPlugin)(app);

		const char* exts[] = {"gltf", "glb"};
		compiler.addPlugin(*plugin, Span(exts));
	}

	bool showGizmo(WorldView& view, ComponentUID cmp) override { return false; }

	const char* getName() const override { return "gtlf_import"; }

	StudioApp& app;
	GLTFPlugin* plugin;
};

} // anonoymous namespace


LUMIX_STUDIO_ENTRY(gltf_import) {
	IAllocator& allocator = app.getWorldEditor().getAllocator();
	return LUMIX_NEW(allocator, StudioAppPlugin)(app);
}
