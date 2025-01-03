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
    _trac = "https://trac.sagemath.org/ticket/26066"

    def _test(self):
        from sage.rings.rational_field import Q as QQ
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        from sage.rings.valuation.gauss_valuation import GaussValuation
        R = PolynomialRing(QQ, 'x')
        x = R.gen()
        v = QQ.valuation(2)
        v = GaussValuation(R, v).augmentation(x+1, QQ(1)/2)
        f = x**4 - 30*x**2 - 75
        v.mac_lane_step(f)

    def _patch(self):
        import patchy
        import sage.rings.valuation.inductive_valuation
        patchy.patch(sage.rings.valuation.inductive_valuation.NonFinalInductiveValuation.mac_lane_step, r"""
@@ -771,18 +780,6 @@ class NonFinalInductiveValuation(FiniteInductiveValuation, DiscreteValuation):
                 assert len(F) == 1
                 break

-            if phi == self.phi():
-                # a factor phi in the equivalence decomposition means that we
-                # found an actual factor of G, i.e., we can set
-                # v(phi)=infinity
-                # However, this should already have happened in the last step
-                # (when this polynomial had -infinite slope in the Newton
-                # polygon.)
-                if self.is_gauss_valuation(): # unless in the first step
-                    pass
-                else:
-                    continue
-
             verbose("Determining the augmentation of %s for %s"%(self, phi), level=11)
             old_mu = self(phi)
             w = self.augmentation(phi, old_mu, check=False)
        """)


Monkey().patch()
