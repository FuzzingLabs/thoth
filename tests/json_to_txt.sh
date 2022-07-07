#!/bin/bash
source ~/cairo_venv/bin/activate
for filename in tests/json_files/*.json; do
    name=$(basename $filename)
    name="${name%%.*}"
    echo $name
    python3 __main__.py cairo -file tests/json_files/"$name".json > tests/ref_files/"$name".txt
done