# -*- coding: utf-8 -*-

#*****************************************************************************
#       Copyright (C) 2018 Julian Rüth <julian.rueth@fsfe.org>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
#*****************************************************************************

from .util import AbstractMonkey

class Monkey(AbstractMonkey):
    _trac = "https://trac.sagemath.org/ticket/25440"

    def _test(self):
        from sage.all import PolynomialRing, QQ, NumberField, GaussValuation, FunctionField
        R = PolynomialRing(QQ, 'x')
        x = R.gen()
        K = NumberField(x**6 + 126*x**3 + 126, 'pi')
        pi = K.gen()
        v = K.valuation(2)
        R = PolynomialRing(K, 'x')
        x = R.gen()
        v = GaussValuation(R, v).augmentation(x, QQ(2)/3)
        F = FunctionField(K, 'x')
        x = F.gen()
        v = F.valuation(v)
        S = PolynomialRing(F, 'y')
        y = S.gen()
        w0 = GaussValuation(S, v)
        G = y**2 - x**3 - 3
        w1 = w0.mac_lane_step(G)[0]
        w1.mac_lane_step(G)
    
    def _patch(self):
        # We are not actually fixing the underlying issue. This is just a
        # symptom fix.
        import patchy
        import sage.rings.valuation.augmented_valuation
        patchy.patch(sage.rings.valuation.augmented_valuation.NonFinalAugmentedValuation._residue_field_generator.f, r"""
@@ -1340,7 +1340,7 @@ class NonFinalAugmentedValuation(AugmentedValuation_base, NonFinalInductiveValua
         ret = self.residue_ring().base().gen()
 
     assert ret.parent() is self.residue_ring().base()
-    assert self.psi()(ret).is_zero()
+    assert (ret.is_one() and self.psi().degree() == 1 and self.psi()[0] == -ret) or self.psi()(ret).is_zero()
     return ret
        """)

Monkey().patch()
