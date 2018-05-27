from setuptools import setup, find_packages

setup(
    name = 'sage-asv',
    version = '0.1.0',
    py_modules=['sage_asv'],
    scripts=['sage_asv.py'],
    packages = find_packages(), 
    install_requires = ["asv"]
)
