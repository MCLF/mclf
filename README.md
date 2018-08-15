# MCLF

[![Documentation Status](https://readthedocs.org/projects/mclf/badge/)](https://mclf.readthedocs.io/?badge=latest)
[![CircleCI](https://circleci.com/gh/MCLF/mclf/tree/master.svg?style=svg)](https://circleci.com/gh/MCLF/mclf/tree/master)
[![Coverage Status](https://coveralls.io/repos/github/MCLF/mclf/badge.svg?branch=master)](https://coveralls.io/github/MCLF/mclf?branch=master)
[![asv](https://img.shields.io/badge/benchmarked%20by-asv-green.svg?style=flat)](https://mclf.github.io/mclf-asv)
[![PyPI](https://img.shields.io/pypi/v/mclf.svg)](https://pypi.org/project/mclf/)

### A Sage toolbox for computing with **M**odels of **C**urves over **L**ocal **F**ields

This is still a rather immature version of our toolbox. Nevertheless, you can
use it to compute, for a large class of curves over the rationals, the stable
reduction at primes of bad reduction.

Let Y be a smooth projective curve over a field K and let vK be a discrete valuation on K.
The principal goal is to compute  the *semistable reduction* of Y with respect to vK.
This means that we want to know

* a finite Galois extension L/K,
* an extension vL of vK to L,
* the special fiber of an integral semistable model of Y over the valuation
  ring of vL, and
* the action of the decomposition group of vL on that special fiber.

At the moment we can do this only in certain special cases, which should
nevertheless be useful.

If you have at least [Sage 8.2](https://www.sagemath.org/) you can install the
latest version of this package with `sage -pip install --user --upgrade mclf`.

If you can not install Sage on your local machine, you can also click
[![Launch on mybinder.org](https://camo.githubusercontent.com/d57df63fab21897847014ebaec3e7f5f48951ad2/68747470733a2f2f626574612e6d7962696e6465722e6f72672f62616467652e737667)](https://mybinder.org/v2/gh/mclf/MCLF/master?filepath=example.ipynb)
to run an interactive Jupyter notebook with mclf preinstalled.

The package can be loaded with
```
sage: from mclf import *
```
We create a Picard curve over the rational number field.      
```
sage: R.<x> = QQ[]
sage: Y = SuperellipticCurve(x^4-1, 3)
sage: Y
superelliptic curve y^3 = x^4 - 1 over Rational Field
```
In general, the class `SuperellipticCurve` allows you to create a superelliptic curve of the form y<sup>n</sup> = f(x),
for a polynomial f over an arbitrary field K. But you can also define any smooth projective curve Y with given
function field.

We define the 2-adic valuation on the rational field. Then we are able to create an
object of the class `SemistableModel` which represents a semistable model of the curve Y with respect to the 2-adic
valuation.
```
sage: v_2 = QQ.valuation(2)
sage: Y2 = SemistableModel(Y, v_2)
sage: Y2.is_semistable() # this may take a while
True
```
The stable reduction of Y at p=2 has four components, one of genus 0 and
three of genus 1.
```
sage: [Z.genus() for Z in Y2.components()]
[0, 1, 1, 1]
sage: Y2.components_of_positive_genus()
[the smooth projective curve with Function field in y defined by y^3 + x^4 + x^2,
 the smooth projective curve with Function field in y defined by y^3 + x^2 + x,
 the smooth projective curve with Function field in y defined by y^3 + x^2 + x + 1]
```
We can also extract some arithmetic information on the curve Y from the stable reduction.
For instance, we can compute the *conductor exponent* of Y at p=2:
```
sage: Y2.conductor_exponent()
6
```
Now let us compute the semistable reduction of Y at p=3:
```
sage: v_3 = QQ.valuation(3)
sage: Y3 = SemistableModel(Y, v_3)
sage: Y3.is_semistable()
True
sage: Y3.components_of_positive_genus()
[the smooth projective curve with Function field in y defined by y^3 + y + 2*x^4]
```
We see that Y has potentially good reduction at p=3. The conductor exponent is:
```
sage: Y3.conductor_exponent()
6
```

For more details on the functionality and the restrictions of the toolbox, see the
[Documentation](https://mclf.readthedocs.io/en/latest/).
For the mathematical background see

* J. Rüth, [Models of Curves and Valuations](https://oparu.uni-ulm.de/xmlui/handle/123456789/3302), PhD thesis, Ulm University, 2014
* I.I. Bouw, S. Wewers, [Computing L-Functions and semistable reduction of superellipic curves](https://arxiv.org/abs/1211.4459?context=math.AG),
  Glasgow Math. J., 59(1), 2017, 77-108
* I.I. Bouw, S. Wewers,[Semistable reduction of curves and computation of bad Euler factors of L-functions](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.100/mitarbeiter/wewers/course_notes.pdf),
   lecture notes for a minicourse at ICERM
* S. Wewers, Semistable reduction of superelliptic curves of degree p, preprint, 2017

#### Known bugs and issues

See our [issues list](https://github.com/MCLF/mclf/issues), and tell us of any bugs or ommissions that are not covered there.

#### Experimental Changes

We also have an unstable [experimental](https://github.com/MCLF/mclf/tree/experimental) version with the latest experimental features and bugs that you can try out by clicking on [![Launch on mybinder.org](https://camo.githubusercontent.com/d57df63fab21897847014ebaec3e7f5f48951ad2/68747470733a2f2f626574612e6d7962696e6465722e6f72672f62616467652e737667)](https://mybinder.org/v2/gh/mclf/MCLF/experimental?filepath=example.ipynb), note that this version currently [![CircleCI](https://circleci.com/gh/MCLF/mclf/tree/experimental.svg?style=svg)](https://circleci.com/gh/MCLF/mclf/tree/experimental) our own test suite.

#### Development workflow

Most development happens on feature branches against the `master` branch. The
`master` branch is considered stable and usually we create a new release and
upload it to PyPI whenever there is something merged into `master`. We
sometimes collect a number of experimental changes on the `experimental`
branch.
