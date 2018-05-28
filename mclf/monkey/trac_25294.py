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
    _trac = "https://trac.sagemath.org/ticket/25294"

    def _test(self):
        import sage.all
        K = sage.all.FunctionField(sage.all.QQ, 'x')
        x = K.gen()
        R = sage.all.PolynomialRing(K, 'y')
        y = R.gen()
        L = K.extension(y**3 - 1/x**3*y + 2/x**4, 'y')
        v = K.valuation(x)
        v.extensions(L)
    
    def _patch(self):
        import patchy
        import sage.rings.function_field.function_field_valuation
        patchy.patch(sage.rings.function_field.function_field_valuation.FunctionFieldValuationFactory.create_key_and_extra_args_from_valuation, r"""
@@ -310,7 +320,7 @@ class FunctionFieldValuationFactory(UniqueFactory):
             # and easier pickling) we need to find a normal form of
             # valuation, i.e., the smallest approximant that describes this
             # valuation
-            approximants = vK.mac_lane_approximants(domain.polynomial())
+            approximants = vK.mac_lane_approximants(domain.polynomial(), require_incomparability=True)
             approximant = vK.mac_lane_approximant(domain.polynomial(), valuation, approximants)
             return (domain, approximant), {'approximants': approximants}
         else:
        """)

        patchy.patch(sage.rings.function_field.function_field_valuation.DiscreteFunctionFieldValuation_base.extensions, r"""
@@ -544,7 +554,7 @@ class DiscreteFunctionFieldValuation_base(DiscreteValuation):
                     if type(y_to_u) == RingHomomorphism_im_gens and type(u_to_y) == RingHomomorphism_im_gens:
                         return [L.valuation((w, L.hom([M(y_to_u(y_to_u.domain().gen()))]), M.hom([L(u_to_y(u_to_y.domain().gen()))]))) for w in H_extensions]
                     raise NotImplementedError
-                return [L.valuation(w) for w in self.mac_lane_approximants(L.polynomial())]
+                return [L.valuation(w) for w in self.mac_lane_approximants(L.polynomial(), require_incomparability=True)]
             elif L.base() is not L and K.is_subring(L):
                 # recursively call this method for the tower of fields
                 from operator import add
        """)

Monkey().patch()
