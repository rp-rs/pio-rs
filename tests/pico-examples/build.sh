#!/bin/bash

for filename in ./*.pio; do
  echo "building $filename"
  pioasm -o hex $filename "./${filename%.*}.hex"
done
