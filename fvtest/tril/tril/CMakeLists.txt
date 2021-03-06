###############################################################################
#
# (c) Copyright IBM Corp. 2017, 2017
#
#  This program and the accompanying materials are made available
#  under the terms of the Eclipse Public License v1.0 and
#  Apache License v2.0 which accompanies this distribution.
#
#      The Eclipse Public License is available at
#      http://www.eclipse.org/legal/epl-v10.html
#
#      The Apache License v2.0 is available at
#      http://www.opensource.org/licenses/apache2.0.php
#
# Contributors:
#    Multiple authors (IBM Corp.) - initial implementation and documentation
###############################################################################

cmake_minimum_required(VERSION 3.2 FATAL_ERROR)

if(NOT TARGET tril)

project(tril LANGUAGES C CXX)

find_package(BISON)
find_package(FLEX)

set(OMR_PATH ${CMAKE_CURRENT_SOURCE_DIR}/../../../../omr)
set(JITBUILDER_PATH ${OMR_PATH}/jitbuilder)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED TRUE)
set(CMAKE_CXX_EXTENSIONS OFF)

BISON_TARGET(tril_parser tril.y ${CMAKE_CURRENT_BINARY_DIR}/tril.parser.c)
FLEX_TARGET(tril_scanner tril.l ${CMAKE_CURRENT_BINARY_DIR}/tril.scanner.c
    COMPILE_FLAGS "--yylineno --header-file=${CMAKE_CURRENT_BINARY_DIR}/tril.scanner.h")
#            DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/tril.scanner.h)
ADD_FLEX_BISON_DEPENDENCY(tril_scanner tril_parser)

add_library(tril STATIC
    ${BISON_tril_parser_OUTPUTS}
    ${FLEX_tril_scanner_OUTPUTS}
    ast.c
    ilgen.cpp
    jitbuilder_compiler.cpp
)

target_compile_definitions(tril PUBLIC
    BITVECTOR_BIT_NUMBERING_MSB
    UT_DIRECT_TRACE_REGISTRATION
    JITTEST
    JITBUILDER_SPECIFIC
    PROD_WITH_ASSUMES
    TR_HOST_X86
    TR_HOST_64BIT
    BITVECTOR_64BIT
    LINUX
    TR_TARGET_X86
    TR_TARGET_64BIT
    SUPPORTS_THREAD_LOCAL
    _LONG_LONG
)

target_include_directories(tril PUBLIC
    ${CMAKE_CURRENT_BINARY_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${JITBUILDER_PATH}/release/include
    ${JITBUILDER_PATH}/x
    ${JITBUILDER_PATH}
    ${OMR_PATH}/compiler/x/amd64
    ${OMR_PATH}/compiler/x
    ${OMR_PATH}/compiler
    ${OMR_PATH}
    ${OMR_PATH}/include_core
)

# not very robust but since we can't build JitBuilder by itself using cmake yet,
# this will have to do
if(NOT "${CMAKE_PROJECT_NAME}" STREQUAL "omr")
    set(OMR_JITBUILDER ON CACHE BOOL "")
    set(OMR_WARNINGS_AS_ERRORS OFF CACHE BOOL "")
    add_subdirectory(${OMR_PATH} ${CMAKE_CURRENT_BINARY_DIR}/omr)
endif()
target_link_libraries(tril INTERFACE
    jitbuilder
    dl
)

#export(TARGETS tril jitbuilder FILE tril-config.cmake)
#install(FILES ast.h ilgen.hpp DESTINATION include)
#install(TARGETS tril EXPORT tril-targets ARCHIVE DESTINATION lib)
#install(EXPORT tril-targets FILE tril-config.cmake DESTINATION lib/cmake/tril)
endif()
