-- Runs inside the plugin project. Paths are relative to this file.
files { "src/**.c", "src/**.cpp", "src/**.h" }
defines { "BUILDING_GLTF_IMPORT" }
if _OPTIONS["dynamic-plugins"] then
	links { "engine" }
end
