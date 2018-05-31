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
    _trac = "https://trac.sagemath.org/ticket/25441"

    def _test(self):
        from sage.all import QQ, PolynomialRing, GaussValuation, FunctionField
        R = PolynomialRing(QQ, 'x')
        x = R.gen()
        v = GaussValuation(R, QQ.valuation(2))
        K = FunctionField(QQ, 'x')
        x = K.gen()
        v = K.valuation(v)
        K.valuation((v, K.hom(x/2), K.hom(2*x)))
    
    def _patch(self):
        import patchy
        import sage.rings.function_field.function_field_valuation
        patchy.patch(sage.rings.function_field.function_field_valuation.FunctionFieldValuationFactory.create_key_and_extra_args_from_valuation_on_isomorphic_field, r"""
@@ -361,13 +361,10 @@ class FunctionFieldValuationFactory(UniqueFactory):
         raise ValueError("from_valuation_domain must map from %r to %r but %r maps from %r to %r"%(valuation.domain(), domain, from_valuation_domain, from_valuation_domain.domain(), from_valuation_domain.codomain()))
 
     if domain is domain.base():
-        # over rational function fields, we only support the map x |--> 1/x with another rational function field
+        # over rational function fields, we only support the map x |--> 1/x
+        # with another rational function field for classical valuations
         if valuation.domain() is not valuation.domain().base() or valuation.domain().constant_base_field() != domain.constant_base_field():
             raise NotImplementedError("maps must be isomorphisms with a rational function field over the same base field, not with %r"%(valuation.domain(),))
-        if to_valuation_domain != domain.hom([~valuation.domain().gen()]):
-            raise NotImplementedError("to_valuation_domain must be the map %r not %r"%(domain.hom([~valuation.domain().gen()]), to_valuation_domain))
-        if from_valuation_domain != valuation.domain().hom([~domain.gen()]):
-            raise NotImplementedError("from_valuation_domain must be the map %r not %r"%(valuation.domain().hom([domain.gen()]), from_valuation_domain))
         if domain != valuation.domain():
             # make it harder to create different representations of the same valuation
             # (nothing bad happens if we did, but >= and <= are only implemented when this is the case.)
        """)

        patchy.patch(sage.rings.function_field.function_field_valuation.FunctionFieldValuationFactory.create_object, r"""
@@ -407,10 +404,12 @@ class FunctionFieldValuationFactory(UniqueFactory):
 
     if isinstance(valuation, tuple) and len(valuation) == 3:
         valuation, to_valuation_domain, from_valuation_domain = valuation
-        if domain is domain.base() and valuation.domain() is valuation.domain().base() and to_valuation_domain == domain.hom([~valuation.domain().gen()]) and from_valuation_domain == valuation.domain().hom([~domain.gen()]):
-            # valuation on the rational function field after x |--> 1/x
+        if domain is domain.base() and valuation.domain() is valuation.domain().base():
             if valuation == valuation.domain().valuation(valuation.domain().gen()):
-                # the classical valuation at the place 1/x
+                if to_valuation_domain != domain.hom([~valuation.domain().gen()]) or from_valuation_domain != valuation.domain().hom([~domain.gen()]):
+                    raise ValueError("the only allowed automorphism for classical valuations is the automorphism x |--> 1/x")
+                # valuation on the rational function field after x |--> 1/x,
+                # i.e., the classical valuation at infinity
                 return parent.__make_element_class__(InfiniteRationalFunctionFieldValuation)(parent)
 
             from sage.structure.dynamic_class import dynamic_class
        """)

Monkey().patch()
