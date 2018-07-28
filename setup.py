from setuptools import setup, find_packages

setup(
    name="mclf",
    packages=find_packages(include=['mclf*']),
    install_requires=['patchy', 'henselization==0.0.0'],
    dependency_links=['https://github.com/MCLF/henselization/tarball/master#egg=henselization-0.0.0']
)


