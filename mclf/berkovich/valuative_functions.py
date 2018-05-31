r""" Harmonic functions on the Berkovich projective line.

Let `K` be a field and `v_K` a discrete valuation on `K`. Let `X=\mathbb{P}^1_K`
be the projective line over `K`. Let `X^{an}` denote the
`(K,v_K)`-analytic space associated to `X`. We call `X^{an}` the *Berkovich
line* over `K`.

According to [Ber1990], `X^{an}` is a simply connected quasi-polyhedron.
Basically, this means that any two points `\xi_1,\xi_2` are the endpoints
of a unique interval `[\xi_1,\xi_2]\subset X^{an}`. There is a canonical affine
and metric structure on these intervals. So `[\xi_1,\xi_2]\cong [a,b]` such
that '|a-b|' is independent of the choices (if `\xi_1` is a point of type I
then `a=-\infty`, and similar for `\xi_2` and `b`).

Let `T` be a *Berkovich tree* inside `X^{an}`, see ??. Then `T` spans a
metric tree `|T|` inside `X^{an}` (where 'metric' has to be understood properly;
the points of type I lie at 'infinity').  The `edges` of `|T|` are precisely
the intervals between the points corresponding to the adjacent vertices.
Therefore, the edges of `|T|` have a canonical affine structure.

Let `f in F=K(x)` be a nonzero rational function. We associate to `f`
the function

..MATH::    H_f:X^{an} \to \RR\cup\{\pm\infty\},  \xi \mapsto v_\xi(f).


**Definition:** A *valuative function* on `X^{an}` is a function of the form

..MATH::      H = a_0 + \sum_i a_i\cdot H_{f_i}

where `f_i` is an irreducible polynomial in the parameter `x`, and `a_i` is
a nonzero rational number.

Valuative functions are *harmonic* in the sense of [??]. In particular,
given a valuative function `H` on `X^{an}`, there always exists a Berkovich
tree `T` (see ??) such that `H` is an affine function on every edge of `|T|`.
Also, any refinement of `T` has the same property. We call `T` *compatible*
with `H`.

In this module we provide a class for working with harmonic functions on the
Berkovich line. Our main algorithms computes, from the input of a finite list
of harmonic functions, a Berkovich tree `T` compatible with all elements of the
list.

AUTHORS:

- Stefan Wewers (2017-02-13): initial version


EXAMPLES::

<Lots and lots of examples>
"""

#*****************************************************************************
#       Copyright (C) 2017 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
#*****************************************************************************

from sage.all import SageObject


class ValuativeFunction(SageObject):
    r""" A valuative function on the Berkovich line.

    INPUT:

    - ``X`` -- a Berkovich line
    - ``L`` -- a list of pairs consisting of
                  (i) an irreducible polynomial
                  (ii) a nonzero rational number
    - ``a`` -- a rational number

    OUTPUT:

    The harmonic function on X given by the datum (L, a).
    """

    def __init__(self, X, L, a):

        pass

    def X(self):

        return self._X

    def eval(self, xi):
        r""" Evaluate the function on the point `\xi`.

        INPUT:

        - ``xi`` -- a point of type I or II on the underlying Berkovic line

        OUTPUT:

        A rational number (or +/-Infinity).
        """

        pass

    def derivative(self, eta):
        r""" Return the derivative of the function with respect to a type V point.

        INPUT:

        - ``eta`` -- a point of type V on the underlying Berkovich line

        OUTPUT:

        A rational number, the value of the derivative of the function
        with respect to ``eta``.
        """

        pass

    def make_compatible(self, T):
        r"""
        Return a tree compatibel with the harmonic function.

        INPUT:

        - T -- a Berkovic tree on the same underlying Berkovic line

        OUTPUT:

        A refinement of T which is compatible with the harmonic function.
        """
        pass
        
