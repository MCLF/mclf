# -*- coding: utf-8 -*-

# ***************************************************************************
#       Copyright (C) 2018 Julian Rüth <julian.rueth@fsfe.org>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ***************************************************************************

from .util import AbstractMonkey


class Monkey(AbstractMonkey):
    _trac = "https://trac.sagemath.org/ticket/24533"

    def _test(self):
        from sage.all import GF, FunctionField, PolynomialRing
        k = GF(4)
        a = k.gen()
        R = PolynomialRing(k, 'b')
        b = R.gen()
        l = k.extension(b**2 + b + a, 'b')
        K = FunctionField(l, 'x')
        x = K.gen()
        R = PolynomialRing(K, 't')
        t = R.gen()
        F = t*x
        F.factor(proof=False)

    def _patch(self):
        import patchy
        import sage.rings.function_field.function_field_valuation
        patchy.patch(sage.rings.function_field.function_field.RationalFunctionField._factor_univariate_polynomial, r"""
@@ -2580,7 +2574,10 @@ class RationalFunctionField(FunctionField):
         if old_variable_name != a.variable_name():
             a = a.change_variable_name(old_variable_name)
         unit *= (c**e)
-        w.append((a,e))
+        if a.is_unit():
+            unit *= a**e
+        else:
+            w.append((a,e))
     from sage.structure.factorization import Factorization
     return Factorization(w, unit=unit)
        """)

        import sage.rings.polynomial.multi_polynomial_element
        patchy.patch(sage.rings.polynomial.multi_polynomial_element.MPolynomial_polydict.factor, r"""
@@ -1715,6 +1729,10 @@ class MPolynomial_polydict(Polynomial_singular_repr, MPolynomial_element):
             F = base_ring(self).factor()
             return Factorization([(R(f),m) for f,m in F], unit=F.unit())

+    base_ring = self.base_ring()
+    if hasattr(base_ring, '_factor_multivariate_polynomial'):
+        return base_ring._factor_multivariate_polynomial(self, proof=proof)
+
     # try to use univariate factoring
     try:
         F = self.univariate_polynomial().factor()
        """)

        import sage.rings.polynomial.polynomial_quotient_ring

        def PolynomialQuotientRing_generic__factor_multivariate_polynomial(self, f, proof=True):
            from sage.structure.factorization import Factorization

            if f.is_zero():
                raise ValueError("factorization of 0 not defined")

            from_isomorphic_ring, to_isomorphic_ring, isomorphic_ring = self._isomorphic_ring()
            g = f.map_coefficients(to_isomorphic_ring)
            F = g.factor()
            unit = f.parent(from_isomorphic_ring(F.unit().constant_coefficient()))
            return Factorization([(factor.map_coefficients(from_isomorphic_ring), e) for factor, e in F], unit=unit)

        sage.rings.polynomial.polynomial_quotient_ring.PolynomialQuotientRing_generic._factor_multivariate_polynomial = PolynomialQuotientRing_generic__factor_multivariate_polynomial


Monkey().patch()
