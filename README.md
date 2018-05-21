# MCLF

[![Documentation Status](https://readthedocs.org/projects/mclf/badge/)](http://mclf.readthedocs.io/?badge=latest)
[![CircleCI](https://circleci.com/gh/MCLF/mclf/tree/master.svg?style=svg)](https://circleci.com/gh/MCLF/mclf/tree/master)

### A Sage toolbox for computing with **M**odels of **C**urves over **L**ocal **F**ields

This is still a rather immature version of our toolbox. Nevertheless, you can use
it to compute the stable reduction at primes of bad reduction, for a large class
of curves over the rationals.

You need at least [Sage 8.2](http://www.sagemath.org/) for the following examples to work. If you can not install Sage on your local machine, you can also click [![Launch on mybinder.org](https://camo.githubusercontent.com/d57df63fab21897847014ebaec3e7f5f48951ad2/68747470733a2f2f626574612e6d7962696e6465722e6f72672f62616467652e737667)](https://mybinder.org/v2/gh/mclf/MCLF/master?filepath=example.ipynb) to try this in an interactive Jupyter notebook.

Let Y be a smooth projective curve over a field K and let vK be a discrete valuation on K.
The principal goal is to compute  the *semistable reduction* of Y with respect to vK.
This means that we want to know

* a finite Galois extension L/K,
* an extension vL of vK to L,
* the special fiber of an integral semistable model of Y_L over the valuation
  ring of vL, and
* the action of the decomposition group of vL on the special fiber.

At the moment we can do this only in certain special cases, which should
nevertheless be useful. Let us do an example:

The package can be loaded with
```
from mclf import *
```
We create a Picard curve over the rational number field.      
```
sage: R.<x> = QQ[]
sage: Y = SuperellipticCurve(x^4-1, 3)
sage: Y
superelliptic curve y^3 = x^4 + 1 over Rational Field
```
In general, the class `SuperellipticCurve` allows you to create a superelliptic curve of the form y<sup>n</sup> = f(x),
for a polynomial f over an arbitrary field K. But you can also define any smooth projective curve Y with given
function field.

We define the 2-adic valuation on the rational field. Then we are able to create an
object which represents a semistable model of the curve Y with respect to the 2-adic
valuation.
```
sage: v_2 = QQ.valuation(2)
sage: Y2 = SemistableModel(Y, v_2)
sage: Y2.is_semistable()
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
[Documentation](http://mclf.readthedocs.io/en/latest/).
For the mathematical background see

 > J. Rüth, Models of Curves and Valuations, PhD thesis, Ulm University, 2014
 >
 > I.I. Bouw, S. Wewers, Computing L-Functions and semistable reduction of superellipic curves,
 > Glasgow Math. J., 59(1), 2017, 77-108
 >
 > [Semistable reduction of curves and computation of bad Euler factors of L-functions](http://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.100/mitarbeiter/wewers/course_notes.pdf),
 > S. Wewers and I.I. Bouw, lecture notes for a minicourse at ICERM
 >
 > S. Wewers, Semistable reduction of superelliptic curves of degree p, preprint, 2017


#### Experimental Changes

We also have an unstable [develop](https://github.com/MCLF/mclf/tree/develop) version with the latest experimental features and bugs that you can try out by clicking on [![Launch on mybinder.org](https://camo.githubusercontent.com/d57df63fab21897847014ebaec3e7f5f48951ad2/68747470733a2f2f626574612e6d7962696e6465722e6f72672f62616467652e737667)](https://mybinder.org/v2/gh/mclf/MCLF/develop?filepath=example.ipynb), note that this version currently [![CircleCI](https://circleci.com/gh/MCLF/mclf/tree/develop.svg?style=svg)](https://circleci.com/gh/MCLF/mclf/tree/develop) our own test suite.
