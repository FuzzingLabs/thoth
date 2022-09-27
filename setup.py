#!/usr/bin/env python3

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as f:
    long_description = f.read()

setup(
    name="thoth",
    description="Cairo/Starknet bytecode analyzer, disassembler and decompiler",
    url="https://github.com/FuzzingLabs/thoth",
    keywords="cairo-lang starknet disassembler decompiler analysis security reversing cfg callflow",
    author="FuzzingLabs",
    version="0.3.0",
    packages=find_packages(),
    python_requires=">=3.6",
    install_requires=[
        "graphviz",
    ],
    license="AGPL-3.0",
    long_description=long_description,
    long_description_content_type="text/markdown",
    entry_points={
        "console_scripts": [
            "thoth = thoth.thoth:main",
        ]
    },
)
