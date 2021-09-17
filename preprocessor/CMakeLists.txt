cmake_minimum_required(VERSION 3.4.3)
project(tricera-preprocessors)

#===============================================================================
# 1. LOAD LLVM CONFIGURATION
#===============================================================================
# Set this to a valid LLVM installation dir
set(CT_LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")

# Add the location of ClangConfig.cmake to CMake search paths (so that
# find_package can locate it)
list(APPEND CMAKE_PREFIX_PATH "${CT_LLVM_INSTALL_DIR}/lib/cmake/clang/")

find_package(Clang REQUIRED CONFIG)

# HelloWorld includes headers from LLVM and Clang - update the include paths
# accordingly
include_directories(SYSTEM "${LLVM_INCLUDE_DIRS};${CLANG_INCLUDE_DIRS}")

#===============================================================================
# 2. TRICERA PREPROCESSOR BUILD CONFIGURATION
#===============================================================================
# Use the same C++ standard as LLVM does
set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

# LLVM is normally built without RTTI. Be consistent with that.
if(NOT LLVM_ENABLE_RTTI)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()


# TOOLS
# ===================
set(TRICERA_TOOLS
    tri-pp
)

set(tri-pp_SOURCES
  TriceraPreprocessorMain.cpp
  lib/TriceraPreprocessor.cpp
  lib/UsedFunctionAndTypeCollector.cpp
  lib/TypedefRemover.cpp
  lib/UnusedDeclCommenter.cpp
  lib/TypeCanoniser.cpp
  lib/ForLoopStmtExtractor.cpp
  lib/Utilites.cpp
)

# CONFIGURATION
# ===================
foreach( tool ${TRICERA_TOOLS} )
# Create a library/executable corresponding to 'plugin'
    add_executable(
      ${tool}
      ${${tool}_SOURCES}
      )

#    add_library(${tool} SHARED
#      ${${tool}_SOURCES}
#    )

# Link with libclangTooling
    target_link_libraries(
      ${tool}
      clangTooling
    )

# Configure include directories for 'tool'
    target_include_directories(
      ${tool}
      PRIVATE
      "${CMAKE_CURRENT_SOURCE_DIR}/include"
      )

    set_target_properties(${tool} PROPERTIES
      LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/preprocessor/build)
endforeach()

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
# add_library(tricera-preprocessor SHARED TriceraPreprocessorMain.cpp)

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)

# add_executable(tricera-preprocessor TriceraPreprocessorMain.cpp)

# target_link_libraries(tricera-preprocessor clangTooling)
