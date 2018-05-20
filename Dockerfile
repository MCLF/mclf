# A Dockerfile for [binder](http://mybinder.readthedocs.io/en/latest/using.html#Dockerfile)
FROM sagemath/sagemath:8.2
COPY --chown=sage:sage . .
