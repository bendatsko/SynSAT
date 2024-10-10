cmake_minimum_required(VERSION 3.29)
project(SynSAT)

set(CMAKE_CXX_STANDARD 14)

include_directories(.)

add_executable(SynSAT
    main.cpp
    main.h)
