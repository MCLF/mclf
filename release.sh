#!/bin/bash

# Usage: ./release.sh 1.0.3
#
# Uploads the latest master as release "1.0.3" to PyPI

REPOSITORY=${REPOSITORY:-origin}

set -exo pipefail

echo "Switching to a clean master..."
git fetch $REPOSITORY
git checkout $REPOSITORY/master
if [ ! -z "$(git status --porcelain --ignored)" ]; then
    echo "Working directory is not completely clean. Please run git clean -fdx and git reset --hard."
    exit 1
fi

echo "Setting version..."
echo "$1" > version

if [ ! -z "$(git status --porcelain --ignored)" ]; then
    echo "Committing version change and pushing to $REPOSITORY..."
    git add version
    git commit -m "Release $1"
    git push $REPOSITORY HEAD:master
fi

echo "Creating tag and pushing to $REPOSITORY..."
git tag "$1"
git push --tags $REPOSITORY "$1"

echo "Building for PyPI..."
python2 setup.py bdist_wheel
python3 setup.py bdist_wheel

echo "Pushing to PyPI..."
twine upload dist/*

echo "Please go to https://github.com/MCLF/mclf/releases/new and create a release from the tag $1."
