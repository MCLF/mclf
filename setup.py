from setuptools import setup, find_packages

setup(
    name="mclf",
    packages=find_packages(include=['mclf*']),
    install_requires=['patchy']
)


