cmake_minimum_required(VERSION 3.20)
project(PilleLowerAdd LANGUAGES C CXX)

find_package(MLIR REQUIRED CONFIG)

# Linking the shared MLIR library keeps the plugin and mlir-opt in the same
# registry. The development installation must include this optional library.
if(NOT TARGET MLIR OR NOT TARGET LLVM)
  message(FATAL_ERROR
    "This example requires the MLIR and LLVM shared libraries (MLIR_BUILD_MLIR_DYLIB=ON, LLVM_BUILD_LLVM_DYLIB=ON)")
endif()

add_library(PilleLowerAdd MODULE lower-add-plugin.cpp)
target_compile_features(PilleLowerAdd PRIVATE cxx_std_17)
target_include_directories(PilleLowerAdd SYSTEM PRIVATE
  ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
target_link_libraries(PilleLowerAdd PRIVATE MLIR LLVM)
if(NOT LLVM_ENABLE_RTTI)
  if(MSVC)
    target_compile_options(PilleLowerAdd PRIVATE /GR-)
  else()
    target_compile_options(PilleLowerAdd PRIVATE -fno-rtti)
  endif()
endif()

# A predictable filename for Toolchain(~pass_plugins: [".../PilleLowerAdd.so"])
# on Unix platforms, including macOS.
set_target_properties(PilleLowerAdd PROPERTIES PREFIX "")
