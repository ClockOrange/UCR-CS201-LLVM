# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /Applications/CMake.app/Contents/bin/cmake

# The command to remove a file.
RM = /Applications/CMake.app/Contents/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build

# Include any dependencies generated for this target.
include CMakeFiles/LivenessAnalysisPass.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include CMakeFiles/LivenessAnalysisPass.dir/compiler_depend.make

# Include the progress variables for this target.
include CMakeFiles/LivenessAnalysisPass.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/LivenessAnalysisPass.dir/flags.make

CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o: CMakeFiles/LivenessAnalysisPass.dir/flags.make
CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o: /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis/LivenessAnalysis.cpp
CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o: CMakeFiles/LivenessAnalysisPass.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o"
	/Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o -MF CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o.d -o CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o -c /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis/LivenessAnalysis.cpp

CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.i"
	/Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis/LivenessAnalysis.cpp > CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.i

CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.s"
	/Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis/LivenessAnalysis.cpp -o CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.s

# Object files for target LivenessAnalysisPass
LivenessAnalysisPass_OBJECTS = \
"CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o"

# External object files for target LivenessAnalysisPass
LivenessAnalysisPass_EXTERNAL_OBJECTS =

libLivenessAnalysisPass.so: CMakeFiles/LivenessAnalysisPass.dir/LivenessAnalysis.cpp.o
libLivenessAnalysisPass.so: CMakeFiles/LivenessAnalysisPass.dir/build.make
libLivenessAnalysisPass.so: CMakeFiles/LivenessAnalysisPass.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX shared module libLivenessAnalysisPass.so"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/LivenessAnalysisPass.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/LivenessAnalysisPass.dir/build: libLivenessAnalysisPass.so
.PHONY : CMakeFiles/LivenessAnalysisPass.dir/build

CMakeFiles/LivenessAnalysisPass.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/LivenessAnalysisPass.dir/cmake_clean.cmake
.PHONY : CMakeFiles/LivenessAnalysisPass.dir/clean

CMakeFiles/LivenessAnalysisPass.dir/depend:
	cd /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/Transforms/LivenessAnalysis /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build /Users/clockorange/Documents/UCR_CS/compiler/project_03/HelloDataflow-LLVM/Pass/build/CMakeFiles/LivenessAnalysisPass.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/LivenessAnalysisPass.dir/depend

