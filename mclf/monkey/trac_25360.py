# -*- coding: utf-8 -*-

#*****************************************************************************
#       Copyright (C) 2018 Julian Rüth <julian.rueth@fsfe.org>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from .util import AbstractMonkey

class Monkey(AbstractMonkey):
    _trac = "https://trac.sagemath.org/ticket/25360"

    def _test(self):
        from sage.all import GF, PolynomialRing, proof
        k = GF(4, 'u')
        u = k.gen()
        R = PolynomialRing(k, 'v')
        v = R.gen()
        l = R.quo(v**3 + v + 1)
        v = l.gen()
        R = PolynomialRing(l, 'x,y')
        x,y = R.gens()
        f = y**3 + x**3 + (u + 1)*x
        with proof.WithProof('polynomial', False):
            f.factor()
    
    def _patch(self):
        import patchy
        import sage.rings.polynomial.multi_polynomial_element
        patchy.patch(sage.rings.polynomial.multi_polynomial_element.MPolynomial_polydict.factor, """
@@ -1726,8 +1747,12 @@ class MPolynomial_polydict(Polynomial_singular_repr, MPolynomial_element):
     if base_ring.is_finite():
         if base_ring.characteristic() > 1<<29:
             raise NotImplementedError("Factorization of multivariate polynomials over prime fields with characteristic > 2^29 is not implemented.")
+
+    if proof is None:
+        from sage.structure.proof.proof import get_flag
+        proof = get_flag(subsystem="polynomial")
     if proof:
-        raise NotImplementedError("proof = True factorization not implemented.  Call factor with proof=False.")
+        raise NotImplementedError("Provably correct factorization not implemented. Disable this error by wrapping your code in a `with proof.WithProof('polynomial', False):` block.")
 
     R._singular_().set_ring()
     S = self._singular_().factorize()
        """) 

Monkey().patch()
