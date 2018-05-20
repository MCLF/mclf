# MCLF

[![Documentation Status](https://readthedocs.org/projects/mclf/badge/)](http://mclf.readthedocs.io/?badge=latest)
[![CircleCI](https://circleci.com/gh/MCLF/mclf/tree/master.svg?style=svg)](https://circleci.com/gh/MCLF/mclf/tree/master)

### A Sage toolbox for computing with *M*odels of *C*urves over *L*ocal *F*ields

This is a very preliminary version. At the moment it is only possible to compute
the semistable reduction of superelliptic curves of degree p over Q<sub>p</sub> and the
exponent of conductor at p, under some restrictions (see an example below).

You need at least [Sage 8.2](http://www.sagemath.org/) for the following examples to work. If you can not install Sage on your local machine, you can also click [![Launch on mybinder.org](https://camo.githubusercontent.com/d57df63fab21897847014ebaec3e7f5f48951ad2/68747470733a2f2f626574612e6d7962696e6465722e6f72672f62616467652e737667)](https://mybinder.org/v2/gh/mclf/MCLF/master?filepath=example.ipynb) to try this in an interactive Jupyter notebook.

The package can be loaded with
```
from mclf import *
```

Let us do an example: a Picard curve over the rational number field, relative to the 3-adic valuation.      
```
sage: K = QQ
sage: v_3 = K.valuation(3)
sage: R.<x> = K[]
sage: Y = Superp(x^4+1, v_3, 3)
sage: Y
superelliptic curve Y: y^3 = x^4 + 1 over Rational Field, with respect to 3-adic valuation
```
In general, the class `Superp` allows you to create a superelliptic curve of the form y<sup>p</sup> = f(x),
for a polynomial f over a number field K and a prime p. We also have to specify a discrete valuation on K with
residue characteristic p. The class should then provide access to  a variety of functions which allows you to compute
the semistable reduction of the curve and analyze it. For instance, it is possible to compute the
conductor exponent at the chosen p-adic valuation.

The mathematical background will soon appear in

 > S. Wewers, Semistable reduction of superelliptic curves of degree p, preprint, 2017

A rough sketch and some examples can already be found in

 > [Semistable reduction of curves and computation of bad Euler factors of L-functions](http://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.100/mitarbeiter/wewers/course_notes.pdf),
 > S. Wewers and I.I. Bouw, lecture notes for a minicourse at ICERM

For the time being, our implementation only works under certain restrictions on the
superelliptic curve Y: y<sup>p</sup> = f(x)

- the base field has to be the field of rational numbers
- the degree of the polynomial f has to prime to p (we can always bring any superelliptic curve
  of degree p into this form as long as there is at least one rational branch point),
- the Jacobian of Y has potentially good reduction at p.   

These restrictions should disappear soon.

In the explicit example from above, we get:
```
sage: Y.compute_semistable_reduction()
We try to compute the semistable reduction of the
superelliptic curve Y: y^3 = x^4 + 1 over Rational Field, with respect to 3-adic valuation
which has genus  3

First we compute the etale locus:
Affinoid with 1 components:
Elementary affinoid defined by
v(x) >= 3/8

There is exactly one reduction component to consider:


Reduction component corresponding to
Elementary affinoid defined by
v(x) >= 3/8

It splits over  3-adic completion of Number Field in pi8 with defining polynomial x^8 - 3
into 1 lower components.
The upper components are:
The smooth projective curve over Finite Field of size 3 with Function field in y defined by y^3 + y + 2*x^4.
Contribution of this component to the reduction genus is  3


The curve has abelian reduction, since the total reduction genus
is equal to the genus of the generic fiber.
```
This result shows that the curve `Y` has potentially good reduction over a tame extension of the `3`-adic numbers of ramification index `8`. The reduction is the
curve over the finite field with 3 elements, given by the equation y^3 + y +2x^4 = 0.

Now we can also compute
the conductor exponent at p=3:
```
sage: Y.conductor_exponent()
6
```

#### Experimental Changes

We also have an unstable [develop](https://github.com/MCLF/mclf/tree/develop) version with the latest experimental features and bugs that you can try out by clicking on [![Launch on mybinder.org](https://camo.githubusercontent.com/d57df63fab21897847014ebaec3e7f5f48951ad2/68747470733a2f2f626574612e6d7962696e6465722e6f72672f62616467652e737667)](https://mybinder.org/v2/gh/mclf/MCLF/develop?filepath=example.ipynb), note that this version currently [![CircleCI](https://circleci.com/gh/MCLF/mclf/tree/develop.svg?style=svg)](https://circleci.com/gh/MCLF/mclf/tree/develop) our own test suite.
