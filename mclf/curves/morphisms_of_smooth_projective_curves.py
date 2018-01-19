r"""
Morphisms of smooth projective curves
=====================================




AUTHORS:

- Stefan Wewers (2018-1-1): initial version


EXAMPLES::

    sage: from mclf import *
    sage: FX.<x> = FunctionField(QQ)
    sage: R.<y> = FX[]
    sage: FY.<y> = FX.extension(y^2-x^3-1)
    sage: X = SmoothProjectiveCurve(FX)
    sage: Y = SmoothProjectiveCurve(FY)
    sage: phi = MorphismOfSmoothProjectiveCurves(Y, X)
    sage: phi
    morphism from the smooth projective curve with Function field in y defined by y^2 - x^3 - 1
    to the smooth projective curve with Rational function field in x over Rational Field,
    determined by inclusion of function fields
    sage: x0 = PointOnSmoothProjectiveCurve(X, FX.valuation(x-1))
    sage: phi.fiber(x0)
    [Point on the smooth projective curve with Function field in y defined by y^2 - x^3 - 1 with coordinates (1, u1).]


"""


#*****************************************************************************
#       Copyright (C) 2018 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.all import SageObject, Infinity, ZZ, PolynomialRing
from mclf.curves.smooth_projective_curves import PointOnSmoothProjectiveCurve



class MorphismOfSmoothProjectiveCurves(SageObject):
    r"""
    Return the morphism between two smooth projective curves corresponding
    to a given morphism of function fields.

    INPUT:

    - ``X``, ``Y`` -- two smooth projective curves; the constant base field of `Y`
      needs to be a subfield of the base field of `X`
    - ``phi`` -- a morphism from the function field of `Y` into the function
      field of `X`, or ``None`` (default: ``None``)

    OUTPUT: the morphism `f:X\to Y` corresponding to the given morphism of
    function fields.

    If no morphism of function fields is given then it is assumed that the
    function field of `Y` is a subfield of the function field of `X`, and
    the canonical embedding is taken. If this is not the case then an error
    is raised.

    NOTE:

    At the moment only the following two special cases are implemented:

    * `\phi` = ``None``, i.e. `F(Y)` is a subfield of `F(X)`
    * `F(X)` and `F(Y)` are rational function fields, and `\phi` is nonconstant

    EXAMPLES::

        sage: from mclf import *
        sage: FX.<x> = FunctionField(QQ)
        sage: FY.<y> = FunctionField(QQ)
        sage: X = SmoothProjectiveCurve(FX)
        sage: Y = SmoothProjectiveCurve(FY)
        sage: phi = FY.hom(x^2+1)
        sage: psi = MorphismOfSmoothProjectiveCurves(X, Y, phi)
        sage: psi
        morphism from the smooth projective curve with Rational function field in x over Rational Field
        to the smooth projective curve with Rational function field in y over Rational Field,
        determined by inclusion of function fields

        sage: P = PointOnSmoothProjectiveCurve(Y, FY.valuation(y-2))
        sage: psi.fiber(P)
        [Point on the smooth projective curve with Rational function field in x over Rational Field with coordinates (1,).,
         Point on the smooth projective curve with Rational function field in x over Rational Field with coordinates (-1,).]

    """

    def __init__(self, X, Y, phi=None):
        # assert phi==None, "parameter phi not implemented yet"
        assert Y.constant_base_field().is_subring(X.constant_base_field()), "the base field of Y has to be a subring of the base field of X"
        FX = X.function_field()
        FY = Y.function_field()
        self._X = X
        self._Y = Y
        if phi==None:
            assert FY.is_subring(FX), "the function field of Y has to be a subfield of the function field of X"
            self._phi = None
        else:
            self._phi = phi


    def __repr__(self):
        if self._phi == None:
            return "morphism from %s \nto %s,\ndetermined by inclusion of function fields"%(self.domain(), self.codomain())
        else:
            return "morphism from %s \nto %s,\ndetermined by %s"%(self.domain(), self.codomain(), self._phi)

    def domain(self):
        r""" Return the domain of this morphism.
        """
        return self._X


    def codomain(self):
        r""" Return the codomain of this morphism.
        """
        return self._Y


    def fiber(self, P):
        r"""
        Return the fiber of this map over the point `P` (without multiplicities).

        INPUT:

        - ``P`` -- a point on the curve `Y`, the target of this morphism

        OUTPUT: the fiber over `P`, as a list of points of `X` (the domain of this map)

        """
        X = self.domain()
        Y = self.codomain()
        assert P.curve()==Y, "P must be a point on the codomain of phi"
        FX = X.function_field()
        FY = self.codomain().function_field()
        v = P.valuation()
        if self._phi==None:
            # FY is a subfield of FX
            return [PointOnSmoothProjectiveCurve(self.domain(), w) for w in v.extensions(FX)]
        else:
            # FX, FY are rational function fields
            phi = self._phi
            if v(FY.gen()) >= 0:
                g = phi(v.uniformizer()).numerator()
                extensions = [FX.valuation(FX(h)) for h, m in g.factor()]
            else:
                f = phi(FY.gen())
                g = f.denominator()
                extensions = [FX.valuation(h) for h, m in g.factor()]
                if f.numerator().degree() > g.degree():
                    extensions.append(FX.valuation(FX,~FX.gen()))
            return [PointOnSmoothProjectiveCurve(X, w) for w in extensions]


    def fiber_degree(self, P):
        r"""
        Return the (absolute) degree of the fiber of this map over the point ``P``.

        INPUT:

        - ``P`` -- a point on the curve `Y` (the codomain of this morphism)

        OUTPUT: the fiber degree over `P`, the sum of the degrees of the
        points on `X` (the domain of this morphism) lying above `P`. Here
        *degree* means *absolute degree*, i.e. with respect to the
        constant base field of `X` (which may differ from the field of constants).

        """
        return sum([Q.absolute_degree() for Q in self.fiber(P)])
