# -*- coding: utf-8 -*-
r"""
Berkovich curves
================

Let `K` be a `p`-adic number field and `X` a smooth projective curve over `K`.
Let `X^{\rm an}` denote the `K`-analytic space associated to `X``.
We call `X^{\rm an}` a *Berkovich curve* over `K`.

Recall that for us, a `p`-adic number field `K` is always realized as the
completion of an underlying global number field `K_0\subset K` with respect to a
discrete valuation `v_K`. We always require the curve `X` to be defined over
`K_0`. So the Berkovich curve `X^{\rm an}` is completely determined by a smooth
projective curve over `K_0` and the valuation `v_K`.

While working in the general framework of `K`-analytic geometry developed by
Berkovich, we systematically work with additive pseudo-valuations instead of
multiplicative seminorms. Thus, we identitfy a point `\xi\in X` with a (real
valued) pseudo-valuation `v_{\xi}` on the function field `F_X` of `X`,
extending the valuation `v_K`,

.. MATH::

    v_{\xi}:F_X \to \mathbb{R}\cup\{\pm \infty\},

as follows: the subring

.. MATH::

    \mathcal{O}_\xi := \{ f\in F_X \mid v_{\xi}(f) > -\infty \}

is a local subring of `F_X`, with maximal ideal

.. MATH::

    \mathfrak{m}_\xi := \{ f \in F \mid v_\xi(f) = \infty \}.

Then `v_\xi` induces a discrete valuation on the residue field

.. MATH::

    K(\xi) := \mathcal{O}_\xi/\mathfrak{m}_\xi.

There are only two kind of points which are relevant for us and which we can
represent and compute with:

- *points of type I*, which are moreover *algebraic*: these are the points
  `\xi\in X` such that `\bar{\xi}:=\pi(\xi)` is a closed point on the algebraic
  curve `X`. Then `\mathcal{O}_\xi` is the local ring and `K(\xi)` the residue
  field of `\bar{\xi}`. Since `K(\xi)/K` is a finite field extension, there are
  finitely many extensions of `v_K` to a discrete valuation on `K(\xi)`; the
  point `\xi\in\pi^{-1}(\bar{\xi})` corresponds precisely to the valuation
  induced by `v_\xi`.
- *points of type II*: these are the points `\xi` such that `v_\xi` is a discrete
  valuation on `F_X`. In particular, the local ring `\mathcal{O}_\xi` is equal to
  `F_X` and the image `\bar{\xi}:=\pi(\xi)` is the generic point of `X`.



AUTHORS:

- Stefan Wewers (2021-06-28): initial version


EXAMPLES::



"""

# *****************************************************************************
#       Copyright (C) 2021 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************


from sage.all import SageObject


class BerkovichCurve(SageObject):
    r""" The analytification of a smooth projective curve over a `p`-adic number field.

    INPUT:

    - `Y` - a smooth projective curve, defined over a number field

    - `K` - a `p`-adic number field.

    It is assumed that the constant base field of `Y` has a natural embedding into
    the number field `K_0` underlying `K`.

    """

    def __init__(self, Y, K):
        raise NotImplementedError()

    def __repr__(self):
        return "the analytification of {}, with respect to {}".format(self.curve(),
                                                                      self.base_valuation())

    def curve(self):
        r""" Return the algebraic curve underlying this Berkovich curve. """
        return self._curve

    def constant_base_field(self):
        r""" Return the p-adic number field which is the constant base field of
        this Berkovich curve. """
        return self._constant_base_field

    def base_valuation(self):
        r""" Return the canonical valuation on the constant base field of this
        Berkovich curve."""
        return self.constant_base_field().valuation()

    def berkovich_line(self):
        r""" Return the underlying Berkovich line of which this curve is a
        finite cover.

        """
        return self._berkovich_line

    def equation(self, inverse=False):
        r""" Return the polynomial equation defining this Berkovich curve.

        INPUT:

        - ``inverse`` -- a boolean (default: ``False``)

        OUTPUT: an irreducible polynomial `G` over the function field `F_X` of
        the underlying Berkovich line `X` such that

        .. MATH::

            F_Y \cong F_X[T]/(G).

        If ``inverse`` is ``False`` (the default) then the above isomorphism
        sends the standard generator `y` of the extension `F_Y/F_X` to the
        residue class of `T`. Otherwise (if ``inverse`` is ``True``), the inverse
        `y^{-1}` is send to `T`.

        """
        if inverse:
            return self._inverse_equation
        else:
            return self._equation

    def fiber(self, x, multiplicities=False):
        r""" Return the fiber of a point `\xi` on the Berkovich line.

        INPUT:

        - ``x`` -- a point on the Berkovich line `X`

        OUTPUT: a list of all points on this Berkovich curve lying over `x`.

        If ``multiplicities`` is ``True``, a list of pairs `(x,m)` is returned.
        Here `m` is the multiplicity of `x` as a point on the fibral divisor.

        """
        Y = self
        K = Y.constant_base_field()
        L = x.base_field()
        assert L.base_field() is K, "the base field of x must be an extension of the base field of Y"
        is_exact = L.embedding().is_exact()
        if multiplicities:
            # this option has not yet been implemented
            raise NotImplementedError()
        type = x.type()  # all points of the fiber have the same type as x
        k_x = x.valued_field()  # this still needs to be implemented!
        if type == "II":
            # k_x is the (fake) completion of F_X=K_0(t) wrt a geometric valuation v_x
            if is_exact:
                F_Y_L = Y.function_field(constant_base_field=L)
                fiber = [Y.type_II_point(k_y) for k_y in k_x.extensions(F_Y_L)]
            else:
                raise NotImplementedError()
        elif type == "I":
            if is_exact:
                algebraic_fiber = Y.curve(x.algebraic_point())
                fiber = [Y.type_I_point(y) for y in algebraic_fiber]
            else:
                raise NotImplementedError()
        else:
            raise NotImplementedError()
        return fiber

# -----------------------------------------------------------------------------


class PointOnBerkovichCurve(SageObject):
    r""" Return a point on a Berkovich curverkovich curve.

    This is the base class for points on a Berkovich curve `Y`.

    A point `y` on `Y` corresponds to a pseudovaluation

    .. MATH::

        v_y: F_Y \to \mathbb{R}\cup \{\pm\infty\},

    of one of the following types:

    - type I: a closed point `y` on the underlying algebraic curve corresponds
      to a valuation ring `\mathcal{O}_y\subset F_Y`. The residue field `k(y)`
      of `y` is a finite extension of the base field `K`. Since `K` is henselian,
      the base valuation on `K` extends uniquely to a discrete valuation on
      `k(y)`. The pseudovaluation `v_y` is obtained from the composition

      .. MATH::

          F_Y \supset \mathcal{O}_y \to k(y) \to \RR\cup\{\infty\}

      by setting `v_y(f):=-\infty` for $f\in F_Y\backslash\mathbb{O}_y.

    - type II: `v_y` is a discrete valuation on `F_Y`, and the residue field
      k(v_y) is an extension of the residue field `k` of `K` of transcendence
      degree one.

    Internally, the pseudovaluation `v_y` is realized as a pseudovaluation on
    a polynomial ring `F_X[T]`, where `F_X=K(x)` is the function field of the
    Berkovich line `X` of which `Y` is a finite cover und where

    .. MATH::

        F_Y \cong F_X[T]/(G)

    is a polynomial representation of the extension `F_Y/F_X`.

    Moreover, the representation of `v_y` on `F_X[T]` can be *exact* or
    *approximate*. The latter means that `v_y` is internally represented by an
    approximation, which can be improved to arbitrary precision.

    A point `y`on the Berkovich `Y` over a `p`-adic number field `K` may also have
    a base field `L` which is a nontrivial finite extension of `K`. This means
    that `y` is actually a point on the Berkovich curve `Y_L`. An important
    feature of this construction is that the extension `L/K` may be *approximate*,
    i.e. the embedding of `K` into `L` is not known exactly (i.e. it may not
    be induced from an embedding of the underlying number fields). If this is the
    case then the point `y` must be approximate, too.

    """

    def berkovich_curve(self):
        return self._berkovich_curve

    def curve(self):
        return self.berkovich_curve().curve()

    def type(self):
        r""" Return the type of this point, which is one of I, II, or V.

        """
        return self._type

    def base_field(self):
        r""" Return the base field of this point.

        """
        return self._base_field

    def residue_field(self):
        r""" Return the residue field of this point.

        OUTPUT: a field extension `k_y/k_x`. Here `k_y` is the
        residue field of this point `y`, and `k_x` is the residue field of the
        image `x` of `y` on the Berkovich line via the structure morphism.

        If this point `y` is of type I then `k_y/k_x` is an extension of
        `p`-adic number fields, i.e.\ an object of the class
        :class:`mclf.padic_extensions.padic_extensions.pAdicExtension`.

        If `y` is of type II, then `k_y/k_x` is an extension of function fields.

        If `y` is of type V, then `k_y/k_x` is an extension of valued function
        fields.

        """
        return self._residue_field

    def base_point(self):
        r""" Return the base point of this point.

        The base point is the image of this point on the Berkovich line, via
        the structure map.

        """
        return self._base_point

    def v(self, f):
        r""" Return the valuation of a rational function on this point.

        INPUT:

        - ``f`` -- an element of the function field of the Berkovich curve.

        OUTPUT: the valuation `v_y(f)`, where `v_y` is the discrete
        pseudovaluation corresponding to this point `y`. The value returned is
        thus an element of `\mathbb{Q}\cup\{\pm\infty\}`.

        This method has to be implemented by a child class.

        """
        raise NotImplementedError()

    def reduce(self, f):
        r""" Return the reduction of a rational function at this point.

        INPUT:

        - ``f`` -- an element of the function field of the Berkovich curve.

        OUTPUT: the image of `f` in the residue field of this point.

        This is well defined only if the valuation of `f` at this point is zero.
        Otherwise an error is raised.

        This method has to be implemented by a child class.

        """
        raise NotImplementedError()


class TypeIPointOnBerkovichCurve(PointOnBerkovichCurve):

    def type(self):
        return "I"


class TypeIIPointOnBerkovichCurve(PointOnBerkovichCurve):

    def type(self):
        return "II"


class TypeVPointOnBerkovichCurve(PointOnBerkovichCurve):

    def type(self):
        return "V"


# -----------------------------------------------------------------------------


class MorphismOfBerkovichCurves(SageObject):
    pass
