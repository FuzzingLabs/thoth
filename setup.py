from setuptools import setup

setup(
    name='Thoth',
    version='0.1.0',    
    description='Cairo language disassembler',
    url='https://github.com/shuds13/pyexample',
    author='FuzzingLabs',
    author_email='contact@fuzzinglabs.com',
    license='BSD 2-clause',
    packages=['thoth'],
    install_requires=['graphviz',                 
                      ],

    classifiers=[
        'Development Status :: 1 - Planning',
        'Intended Audience :: Science/Research',
        'License :: OSI Approved :: BSD License',  
        'Operating System :: POSIX :: Linux',        
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.4',
        'Programming Language :: Python :: 3.5',
    ],
)