cmake_minimum_required(VERSION 3.12)
project(
        Diviner
        VERSION 1.0.0
        HOMEPAGE_URL https://github.com/TravisWheelerLab/Diviner
)

set(CMAKE_C_STANDARD 11)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY build)

file(MAKE_DIRECTORY ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})

# Custom target for handling dependencies, Perl scripts, and shell scripts. We
# just move all these files to the build directory to aid in distribution and
# installation. These will be automatically run by the build.

add_custom_target(
        build-perl ALL
        COMMAND cp
                ${CMAKE_SOURCE_DIR}/src/*.pl
                ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/
        COMMAND cp
                ${CMAKE_SOURCE_DIR}/src/*.pm
                ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/
)

add_custom_target(
        build-shell ALL
	COMMAND cp
		${CMAKE_SOURCE_DIR}/src/run_diviner.sh
		${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/diviner
 	COMMAND ln
 		-s ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/diviner
 		   ${CMAKE_SOURCE_DIR}/diviner
)

add_custom_target(
        build-dependencies ALL
        COMMAND ${CMAKE_SOURCE_DIR}/src/install-dependencies.sh
        VERBATIM
)
