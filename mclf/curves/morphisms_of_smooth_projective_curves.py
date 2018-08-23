r"""
Morphisms of smooth projective curves
=====================================

This module defines a class ``MorphismOfSmoothProjectiveCurves`` which realizes
finite and nonconstant morphism between smooth projective curves.

Let `Y` and `X` be smooth projective curves, with function fields `F_Y` and `F_X`,
respectively. Then a nonconstant morphism

.. MATH::

        f:Y\to X

is completely determined by the induced pullback map on the function fields,

.. MATH::

        \phi = f^*:F_X \to F_Y.

It is automatic that `F_Y` is a finite extension of `\phi(F_X)` and that
the morphism `\phi:Y\to X` is finite.


.. NOTE::

    For the time being, this module is in a very preliminary state. A morphism
    `\phi:Y\to X` as above can be constructed only in the following two special
    cases:

    * `X` and `Y` are two projective lines; then `F_X` and `F_Y` are rational
      function fields in one variable.
    * the map `f:Y\to X` is the *structure map* of the curve `Y`; by this we
      mean that `X` is the projective line `f` the canonical morphism realizing
      `Y` as a cover of `X`.

    Moreover, the role of the constant base fields of the two curves still needs
    to be clarified.



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
    determined by Coercion map:
      From: Rational function field in x over Rational Field
      To:   Function field in y defined by y^2 - x^3 - 1

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
#                  https://www.gnu.org/licenses/
#*****************************************************************************

from sage.all import SageObject
from mclf.curves.smooth_projective_curves import PointOnSmoothProjectiveCurve


class MorphismOfSmoothProjectiveCurves(SageObject):
    r"""
    Return the morphism between two smooth projective curves corresponding
    to a given morphism of function fields.

    INPUT:

    - ``Y``, ``X`` -- two smooth projective curves
    - ``phi`` -- a morphism from the function field of `X` into the function
      field of `Y`, or ``None`` (default: ``None``)

    OUTPUT: the morphism `f:Y\to X` corresponding to the given morphism of
    function fields.

    If no morphism of function fields is given then it is assumed that the
    function field of `X` is the canonical rational subfield of the function
    field of `Y`. This means that map `f:Y\to X` is the structure map of `Y` as
    a cover of the projective line. If this is not the case then an error
    is raised.

    .. NOTE::

        At the moment only the following two special cases are implemented:

        * the map `Y\to X` is equal to the structural morphism of `Y` as a cover
          of the projective line; in particular, `X` is a projective line
        * `X` and `Y` are both projective lines

    EXAMPLES:

    We define a rational map between two projective lines and compute the
    fiber of a point on the target: ::

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
        determined by Function Field morphism:
        From: Rational function field in y over Rational Field
        To:   Rational function field in x over Rational Field
        Defn: y |--> x^2 + 1

        sage: P = PointOnSmoothProjectiveCurve(Y, FY.valuation(y-2))
        sage: psi.fiber(P)
        [Point on the smooth projective curve with Rational function field in x over Rational Field with coordinates (1,).,
         Point on the smooth projective curve with Rational function field in x over Rational Field with coordinates (-1,).]

    The only other map that is allowed is the structure morphism of a curve
    as a cover of the projective line: ::

        sage: R.<x> = GF(2)[]
        sage: Y = SuperellipticCurve(x^4+x+1, 3)
        sage: phi = Y.structure_map()
        sage: X = phi.codomain()
        sage: X
        the smooth projective curve with Rational function field in x over Finite Field of size 2
        sage: P = X.random_point()
        sage: phi.fiber(P)  # random
        [Point on superelliptic curve y^3 = x^4 + x + 1 over Finite Field of size 2 with coordinates (0, 1).,
         Point on superelliptic curve y^3 = x^4 + x + 1 over Finite Field of size 2 with coordinates (0, u1).]
    """

    def __init__(self, Y, X, phi=None):
        FX = X.function_field()
        assert FX == X.rational_function_field(), "X must be a projective line"
        FY = Y.function_field()
        self._codomain = X
        self._domain = Y
        if phi==None:
            assert FX == Y.rational_function_field(), "Y be a cover of the projective line X."
            self._phi = FY.coerce_map_from(FX)
            self._is_structure_map = True
        else:
            assert phi.domain() is FX, "the domain of phi must be %s"%FX
            assert phi.codomain() is FY, "the codomain of phi must be %s"%FY
            self._phi = phi
            self._is_structure_map = ( phi(FX.gen()) == FY.base_field().gen())
            assert self._is_structure_map or FY == FY.rational_function_field()


    def __repr__(self):
        if self._phi == None:
            return "morphism from %s \nto %s,\ndetermined by inclusion of function fields"%(self.domain(), self.codomain())
        else:
            return "morphism from %s \nto %s,\ndetermined by %s"%(self.domain(), self.codomain(), self._phi)


    def is_structure_map(self):
        r""" Return ``True`` if this map is the structure map of the curve `Y`.

        EXAMPLES::

            sage: from mclf import *
            sage: F.<x> = FunctionField(QQ)
            sage: X = SmoothProjectiveCurve(F)
            sage: phi = F.hom(x^2+1)
            sage: f = MorphismOfSmoothProjectiveCurves(X, X, phi)
            sage: f.is_structure_map()
            False
            sage: phi = F.hom(x)
            sage: f = MorphismOfSmoothProjectiveCurves(X, X, phi)
            sage: f.is_structure_map()
            True

        """
        return self._is_structure_map


    def domain(self):
        r""" Return the domain of this morphism.
        """
        return self._domain


    def codomain(self):
        r""" Return the codomain of this morphism.
        """
        return self._codomain


    def pullback_map(self):
        r""" Return the induced inclusion of function fields.

        """
        return self._phi


    def pullback(self, f):
        r""" Return the pullback of a function under this morphism.

        """
        return self.pullback_map(f)


    def fiber(self, P):
        r"""
        Return the fiber of this map over the point `P` (without multiplicities).

        INPUT:

        - ``P`` -- a point on the curve `X`, the codomain of this morphism

        OUTPUT: the fiber over `P`, as a list of points of `Y` (the domain of this map)

        """
        Y = self.domain()
        X = self.codomain()
        assert P.curve()==X, "P must be a point on the codomain of phi"
        FX = X.function_field()
        FY = Y.function_field()
        phi = self.pullback_map()
        v = P.valuation()
        if self.is_structure_map():
            # FY is a finite simple extension of FX
            return [PointOnSmoothProjectiveCurve(self.domain(), w) for w in v.extensions(FY)]
        else:
            # FX, FY are rational function fields
            if v(FX.gen()) >= 0:
                g = phi(v.uniformizer()).numerator()
                extensions = [FY.valuation(FY(h)) for h, m in g.factor()]
            else:
                f = phi(FX.gen())
                g = f.denominator()
                extensions = [FY.valuation(h) for h, m in g.factor()]
                if f.numerator().degree() > g.degree():
                    extensions.append(FY.valuation(~FY.gen()))
            return [PointOnSmoothProjectiveCurve(Y, w) for w in extensions]


    def fiber_degree(self, P):
        r"""
        Return the (absolute) degree of the fiber of this map over the point ``P``.

        INPUT:

        - ``P`` -- a point on the curve `X` (the codomain of this morphism)

        OUTPUT: the fiber degree over `P`, the sum of the degrees of the
        points on `Y` (the domain of this morphism) lying above `P`. Here
        *degree* means *absolute degree*, i.e. with respect to the
        constant base field of `Y` (which may differ from the field of constants).

        """
        return sum([Q.absolute_degree() for Q in self.fiber(P)])
