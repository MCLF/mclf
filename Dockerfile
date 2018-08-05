# A Dockerfile for [binder](https://mybinder.readthedocs.io/en/latest/using.html#Dockerfile)
FROM sagemath/sagemath:8.3
COPY --chown=sage:sage . .
RUN sage -python setup.py install
