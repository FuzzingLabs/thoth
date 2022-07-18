from setuptools import setup

setup(
    name="Thoth",
    version="0.1.0",
    description="Cairo language disassembler",
    url="https://github.com/shuds13/pyexample",
    author="FuzzingLabs",
    author_email="contact@fuzzinglabs.com",
    license="AGPL-3.0",
    packages=["thoth"],
    python_requires=">=3.7",
    install_requires=[
        "graphviz",
    ],
)
