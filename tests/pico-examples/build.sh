#!/bin/bash

for filename in ./*.pio; do
  echo "building $filename"
  output=$(pioasm -o hex $filename)
  test "$output" && echo "$output" > "./${filename%.*}.hex"
done
