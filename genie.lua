if plugin "gltf_import" then
	files { 
		"src/**.c",
		"src/**.cpp",
		"src/**.h",
		"genie.lua"
	}
	defines { "BUILDING_GLTF_IMPORT" }
	links { "engine" }
end