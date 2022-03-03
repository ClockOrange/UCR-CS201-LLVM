#! /bin/sh

echo "Enter test file number: "
read NUMBER
echo " --------- % Test " $NUMBER " %---------- "

cd Pass/build
cmake -DCMAKE_BUILD_TYPE=Release ../Transforms/LivenessAnalysis
make -j4
cd ../../test
clang -S -fno-discard-value-names -emit-llvm "test$NUMBER.c" -o "test$NUMBER.ll"
#opt -load ../Pass/build/libLivenessAnalysisPass.so -enable-new-pm=0 -passes=LivenessAnalysis "test$NUMBER.ll" -debug-pass-manager
opt -load-pass-plugin ../Pass/build/libLivenessAnalysisPass.so  -passes=liveness-analysis "test$NUMBER.ll" -debug-pass-manager