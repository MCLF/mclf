# MCLF

### A Sage toolbox for computing with **M**odels of **C**urves over **L**ocal **F**ields


This is a very preliminary version. At the moment it is only possible to compute
the semistable reduction of superelliptic curves of degree p over Q_p and the
exponent of conductor at p, under some restrictions (see an example below).  

Everything is based on Julian Rüth's Sage package `mac_lane`, which allows us to work with quite general valuations. See

https://github.com/saraedum/mac_lane

The package can be loaded with
```
from mclf import *
```
However, the `mac_lane` package needs to be available -- at the moment it is necessary to
clone the branch ``modified`` available under https://github.com/swewers/mac_lane.
Hopefully, there will soon be an integrated version of mac_lane in Sage 8.1.

Let us do an example: a Picard curve over the rational number field, relative to the 3-adic valuation.      
```
sage: K = QQ
sage: v_3 = pAdicValuation(K, 3)
sage: R.<x> = K[]
sage: Y = Superp(x^4+1, v_3, 3)
sage: Y
superelliptic curve Y: y^3 = x^4 + 1 over Rational Field, with respect to 3-adic valuation
```
In general, the class `Superp` allows you to create a superelliptic curve of the form ``y^p = f(x)``,
for a polynomial f over a number field K and a prime p. We also have to specify a discrete valuation on K with
residue characteristic p. The class should then provide access to  a variety of functions which allows you to compute
the semistable reduction of the curve and analyze it. For instance, it is possible to compute the
conductor exponent at the chosen p-adic valuation.

The mathematical background will soon appear in

 >S. Wewers, Semistable reduction of superelliptic curves of degree p, preprint, 2017

A rough sketch and some examples can already be found in

 > [Semistable reduction of curves and computation of bad Euler factors of L-functions](http://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.100/mitarbeiter/wewers/course_notes.pdf),
 > S. Wewers and I.I. Bouw, lecture notes for a minicourse at ICERM

For the time being, our implementation only works under certain restrictions on the
superelliptic curve Y: y^p=f(x)

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
This result shows that the the curve `Y` has potentially good reduction over a tame extension of the `3`-adic numbers of ramification index `8`. The reduction is the
curve over FF_3 given by the equation y^3 + y +2x^4 = 0. Now we can also compute
the conductor exponent at p=3:
```
sage: Y.conductor_exponent()
6
```

Update with more functionality should appear regularly.
