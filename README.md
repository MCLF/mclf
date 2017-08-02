# MCLF

### A Sage toolbox for computing with **M**odels of **C**urves over **L**ocal **F**ields


This is a very preliminary version; the only part so far which is both usable and of general interest is the first step in the computation of the semistable reduction of superelliptic curves of degree p: the computation of the *etale locus*. See an example below.


Everything is based on Julian Rüth's Sage package `mac_lane`, which allows us to work with quite general valuations. See

https://github.com/saraedum/mac_lane

The package can be loaded with
```
from mclf import *
```
However, the `mac_lane` package needs to be available -- either as a standalone python module, or preinstalled in the new Sage version 8.1 (forthcoming).

Let us do an example: a Picard curve over the rational number field, relative to the 3-adic valuation.      
```
sage: K = QQ
sage: v_3 = pAdicValuation(K, 3)
sage: R.<x> = K[]
sage: Y = Superp(x^4+1, v_3, 3)
sage: Y
The superelliptic curve Y: y^3 = x^4 + 1 over Rational Field with 3-adic valuation
```
In general, the class `Superp` allows you to create a superelliptic curve of the form ``y^p = f(x)``,
for a polynomial f over a number field K and a prime p. We also have to specify a discrete valuation on K with
residue characteristic p. The class should then provide access to  a variety of functions which allows you to compute
the semistable reduction of the curve and analyze it. The mathematical background will soon appear in

 >S. Wewers, Semistable reduction of superelliptic curves of degree p, preprint, 2017

A rough sketch and some examples can already be found in

 > [Semistable reduction of curves and computation of bad Euler factors of L-functions](http://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.100/mitarbeiter/wewers/course_notes.pdf),
 > S. Wewers and I.I. Bouw, lecture notes for a minicourse at ICERM

For the time being, the only function that is available is a certain (crucial) precomputation, namely the computation
of the *etale locus*. This is an affinoid subdomain of the projective line over K, considered as an analytic space
in the sense of Berkovich.  See § 4.2 of the ICERM notes cited above for more details.

In the explicit example from above, we get:
```
sage: U_et = Y.compute_etale_locus()
sage: U_et
Affinoid with 2 components:
Elementary affinoid defined by
v(x) >= 3/8
Elementary affinoid defined by
v(1/x) >= 3/2
```
Actually, the result obtained is not quite correct: the etale locus only consists of the first component
(defined by ``v(x)\geq 3/8``); the (fake) second component shows up because the code does not yet deal properly
with the region 'outside the closed unit disk'.

An update with more functionality should appear soon.
