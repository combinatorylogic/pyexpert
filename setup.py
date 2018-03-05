from setuptools import setup, find_packages

setup(
    name='pyexpert',
    packages=find_packages(exclude=['tests']),
    version='0.0.1',
    description='A small prolog implementation for embedded expert systems',
    long_description=open('README.md').read(),
    keywords=['prolog'],
    install_requires=['arpeggio'],
    license='MIT'
)
