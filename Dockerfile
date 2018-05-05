# A Dockerfile for [binder](http://mybinder.readthedocs.io/en/latest/using.html#Dockerfile)
# TODO: Change this to an official version of sagemath once https://trac.sagemath.org/ticket/24655 has been merged
FROM saraedum/sagemath:develop
COPY --chown=sage:sage . .
