from setuptools import setup, find_packages

with open("README.md", "r") as fh:
    long_description = fh.read()

setup(
    name="mclf",
    version="1.0.0",
    author="Stefan Wewers, Julian Rüth",
    author_email="stefan.wewers@uni-ulm.de",
    description="A Sage toolbox for computing with Models of Curves over Local Fields",
    url="https://github.com/mclf/mclf",
    long_description=long_description,
    long_description_content_type="text/markdown",
    packages=find_packages(include=['mclf*']),
    install_requires=['patchy', 'henselization==0.0.0'],
    dependency_links=['https://github.com/MCLF/henselization/tarball/master#egg=henselization-0.0.0']
    classifiers=(
        "Development Status :: 4 - Beta",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)",
        "Programming Language :: Python :: 2",
        "Programming Language :: Python :: 3",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Operating System :: OS Independent")
)
