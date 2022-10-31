cmake_minimum_required(VERSION 3.0.0)
project(coding-therory-a VERSION 0.1.0)

set(CMAKE_CXX_STANDARD 20)
add_compile_options(-Wall -Wextra -Wno-dangling-else)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin/")
add_definitions(-D_DEBUG)

add_executable(coding-therory-a a.cpp)
