#!/bin/bash
source ~/cairo_venv/bin/activate
substr1="starknet"
substr2="cairo"
for filename in tests/json_files/*.json; do
    name=$(basename $filename)
    name="${name%%.*}"
    if [[ $name == *"$substr1"* ]];
    then
        echo 1
    else
        if [[ $name == *"$substr2"* ]];
        then
            echo 2
        else
            rm tests/json_files/"$name".json
        fi
    fi
done