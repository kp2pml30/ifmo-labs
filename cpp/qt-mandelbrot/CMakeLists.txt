cmake_minimum_required(VERSION 3.5)

project(mandel LANGUAGES CXX)

set(CMAKE_INCLUDE_CURRENT_DIR ON)

set(CMAKE_AUTOUIC ON)
set(CMAKE_AUTOMOC ON)
set(CMAKE_AUTORCC ON)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include(CheckCXXCompilerFlag)
# unset(supports_fast_math CACHE)
check_cxx_compiler_flag(-ffast-math supports_fast_math)
if (supports_fast_math)
	add_compile_options(-ffast-math)
endif()

find_package(QT NAMES Qt6 Qt5 COMPONENTS Widgets REQUIRED)
find_package(Qt${QT_VERSION_MAJOR} COMPONENTS Widgets REQUIRED)

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fsanitize=thread")

add_executable(mandel
	main.cpp
	mainwindow.cpp
	mainwindow.ui
	mandelbrot.cpp
)

target_link_libraries(mandel PRIVATE Qt${QT_VERSION_MAJOR}::Widgets)
find_library(PThread pthread)
if (PThread)
	target_link_libraries(mandel PRIVATE  ${PThread})
endif()
