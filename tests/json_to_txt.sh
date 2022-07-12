#!/bin/bash
source ~/cairo_venv/bin/activate
for filename in tests/json_test_files/*.json; do
    name=$(basename $filename)
    name="${name%%.*}"
    echo $name
    python3 __main__.py -file tests/json_test_files/"$name".json -vvv > tests/ref_files/"$name".txt
done