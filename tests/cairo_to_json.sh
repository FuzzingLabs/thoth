#!/bin/bash
source ~/cairo_venv/bin/activate
for filename in tests/cairo_files/*.cairo; do
    name=$(basename $filename)
    name="${name%%.*}"
    echo $name
    cairo-compile tests/cairo_files/"$name".cairo --output tests/json_files/"$name".json
done