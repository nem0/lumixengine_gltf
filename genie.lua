project "gltf_import"
	libType()
	files { 
		"src/**.c",
		"src/**.cpp",
		"src/**.h",
		"genie.lua"
	}
	defines { "BUILDING_GLTF_IMPORT" }
	links { "engine" }
	useLua()
	defaultConfigurations()

linkPlugin("gltf_import")