cmake_minimum_required(VERSION 3.20)
project(PilleSmtQuery LANGUAGES C CXX)

# Configure with -DMLIR_DIR=<prefix>/lib/cmake/mlir, where <prefix> is the same
# installation that supplies the mlir-opt used through PILLE_MLIR_PREFIX.
find_package(MLIR REQUIRED CONFIG)

# Linking the shared MLIR library keeps the plugin and mlir-opt in the same
# registry. The development installation must include this optional library.
if(NOT TARGET MLIR OR NOT TARGET LLVM)
  message(FATAL_ERROR
    "This plugin requires the MLIR and LLVM shared libraries (MLIR_BUILD_MLIR_DYLIB=ON, LLVM_BUILD_LLVM_DYLIB=ON)")
endif()

add_library(PilleSmtQuery MODULE smt-query-plugin.cpp)
target_compile_features(PilleSmtQuery PRIVATE cxx_std_17)
target_include_directories(PilleSmtQuery SYSTEM PRIVATE
  ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
target_link_libraries(PilleSmtQuery PRIVATE MLIR LLVM)
if(NOT LLVM_ENABLE_RTTI)
  if(MSVC)
    target_compile_options(PilleSmtQuery PRIVATE /GR-)
  else()
    target_compile_options(PilleSmtQuery PRIVATE -fno-rtti)
  endif()
endif()

# A predictable filename on Unix platforms, including macOS: PilleSmtQuery.so.
set_target_properties(PilleSmtQuery PROPERTIES PREFIX "" SUFFIX ".so")
