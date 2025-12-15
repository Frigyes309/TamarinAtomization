#!/bin/bash
echo "Compiling m4 files..."

m4 init.spthy.m4 > compiled/init.spthy
m4 xor.spthy.m4 > compiled/xor.spthy
#m4 and.spthy.m4 > compiled/and.spthy
m4 xor_simple.spthy.m4 > compiled/xor_simple.spthy

echo "Successfully compiled m4 files."

tamarin-prover interactive compiled/$1.spthy