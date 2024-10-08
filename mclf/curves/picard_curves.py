# -*- coding: utf-8 -*-
r"""
Picard curves
=============

A *Picard curve* is a smooth projective curve over a field `K` which
is given generically by an equation of the form

.. MATH::

    Y:\; y^3 = f(x),

where `f\in K[x]` is a separable polynomial over `K` of degree `4`. Then `Y` is
a smooth plane quartic; in particular, it has genus `3`. The defining equation
presents `Y` as a Kummer cover of `X=\mathbb{P}^1_K` of degree `3`.

In this module we define a class ``PicardCurve`` which is a subclasses
of ``SuperellipticCurve`` and whose objects represent Picard curves
as above.

AUTHORS:

- Stefan Wewers (2018-8-1): initial version


EXAMPLES::

    sage: from mclf import *
    sage: R.<x> = QQ[]
    sage: Y = PicardCurve(x^4-1)
    sage: Y
    Picard curve y^3 = x^4 - 1 over Rational Field


.. TODO::


"""

# ***************************************************************************
#       Copyright (C) 2016-2018 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ***************************************************************************

from sage.all import ZZ, FunctionField, PolynomialRing
from mclf.curves.superelliptic_curves import SuperellipticCurve


class PicardCurve(SuperellipticCurve):
    r"""
    Return the Picard curve with equation `y^3=f(x)`.

    INPUT:

    - ``f`` -- a nonconstant polynomial over a field `K`
    - ``name`` -- a string (default 'y')

    OUTPUT:

    the Picard curve `Y` over `K` given generically by the equation

    .. MATH::

        Y:\; y^3 = f(x).

    This means that the function field of `Y` is an extension of the rational
    function field in `x` generated by an element `y` (the Kummer generator)
    satisfying the above equation.

    It is assumed that `f` is separable of degree `4`. If this condition is not
    met, an error is raised. ``name`` is the name given to the Kummer generator
    `y`.

    """

    def __init__(self, f, name='y'):

        R = f.parent()
        assert R.variable_name() != name, "variable names must be distinct"
        k = R.base_ring()
        assert k.characteristic() != 3, \
            "the characteristic of the base field must not be 3"
        assert f.gcd(f.derivative()).is_one(), "f must be separable"
        self._n = 3
        self._f = f
        self._ff = f.factor()
        self._name = name
        FX = FunctionField(k, R.variable_name())
        S = PolynomialRing(FX, 'T')
        T = S.gen()
        FY = FX.extension(T**3 - FX(f), name)
        self._function_field = FY
        self._constant_base_field = k
        self._extra_extension_degree = ZZ(1)
        self._covering_degree = 3
        self._coordinate_functions = self.coordinate_functions()
        self._field_of_constants_degree = ZZ(1)
        self._is_separable = True

    def __repr__(self):
        return "Picard curve %s^3 = %s over %s" % (self.kummer_gen(),
                                                   self.polynomial(),
                                                   self.constant_base_field())
