# A Dockerfile for [binder](http://mybinder.readthedocs.io/en/latest/using.html#Dockerfile)
FROM sagemath/sagemath:8.3.beta3
COPY --chown=sage:sage . .
RUN sage -python setup.py install
