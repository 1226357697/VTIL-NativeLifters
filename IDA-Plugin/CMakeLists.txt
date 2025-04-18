cmake_minimum_required(VERSION 3.10)

project(VTIL-IDA-Plugin)
set(CMAKE_CXX_STANDARD 17)

set(PRODUCK_NAME ${PROJECT_NAME}64)

file(GLOB_RECURSE SOURCES CONFIGURE_DEPENDS *.cpp *.hpp)
file(GLOB_RECURSE INCLUDES CONFIGURE_DEPENDS includes/*)

set(IDA_SDK_ROOT "D:/Book/IDA_Pro_7.7/SDK77/idasdk77")
set(IDA_PLUGIN "D:/Book/IDA_Pro_7.7/plugins")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${IDA_PLUGIN})

add_definitions(
    -D__EA64__=1
)

include_directories(
    ${IDA_SDK_ROOT}/include
)

link_directories(
    ${IDA_SDK_ROOT}/lib/x64_win_vc_64
)


add_library(${PRODUCK_NAME}  SHARED 
    ${SOURCES}
    ${INCLUDES}
)

source_group(TREE ${PROJECT_SOURCE_DIR} FILES ${SOURCES} ${INCLUDES})

target_include_directories(${PRODUCK_NAME} PUBLIC includes)

target_link_libraries(${PRODUCK_NAME} PUBLIC NativeLifters-Core VTIL ida)

set_target_properties(${PRODUCK_NAME} PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY_DEBUG ${IDA_PLUGIN}
    RUNTIME_OUTPUT_DIRECTORY_RELEASE ${IDA_PLUGIN}
)
