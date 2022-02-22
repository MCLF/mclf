# -*- coding: utf-8 -*-
r"""
Elements of p-adic number fields
================================

In this module we define classes whose objects are elements of p-adic number
fields. We do not intend to equip these elements with the usual arithmetic
operations `+` etc. Our modest goal is to able to perform the following tasks
with elements of a `p`-adic number field:

- compute valuations and distances (i.e. valuation of the difference of two
  elements),
- evaluate a polynomial with rational coefficients on an element,
- compute the minimal polynomial of algebraic elements,
- compute the image of a field element under an embedding of p-adic number
  fields.

Recall that for us, a p-adic number field `K` is given as the completion of
an absolute number field `K_0` with respect to a discrete valuation `v_K`, with
finite residue characteristic `p`. We assume that `v_K` is  the only extension
of the `p`-adic valuation from `\mathbb{Q}` to `K_0`; hence

.. MATH::

    [K:\mathbb{Q}_p] = [K_0:\mathbb{Q}].

Moreover, we assume that the powers of the standard generator of
`K_0/\mathbb{Q}` form an integral basis of `K/\mathbb{Q}_p`, so that

.. MATH::

    \mathcal{O}_K = \mathbb{Z}_p[\alpha],

where `\alpha` is the standard generator of `K_0/\mathbb{Q}`.

By an *element* of `K` we mean on of the following three types of objects:

- An *exact element*: this is just an element of the underlying number
  field `K_0`.
- An *approximate element*: this is an element of `K` only known up to some
  given precision. More precisely, it is a closed ball inside `K`.
- An *algebraic element*: an element of `K` which is algebraic over `\mathbb{Q}`;
  such an element can by specified by its minimal polynomial and a
  sufficiently good approximation in `K_0`.

Actually, we treat the first case as a boundary case of the second, where the
precision takes the value `\infty`.


AUTHORS:

- Stefan Wewers (2022-2-14): initial version


EXAMPLES::

    sage: from mclf import *
    sage: Q2 = pAdicNumberField(QQ, 2)
    sage: a = Q2.element(746); a
    746

    sage: a.parent()
    field of 2-adic numbers

    sage: a.is_exact()
    True

    sage: b = Q2.element(746, 3); b
    2 (mod 2^3)

    sage: b.is_exact()
    False

    sage: R.<x> = QQ[]
    sage: K = Q2.simple_extension(x^2+2, alpha)
    sage: alpha = K.algebraic_element(K.generator())
    sage: alpha
    alpha as algebraic element
    sage: alpha.minimal_polynomial()
    x^2 + 2

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

from sage.all import SageObject, QQ, Infinity
from mclf.padic_extensions.padic_number_fields import pAdicNumberField


def element_of_padic_number_field(K, *a):
    r""" Return an element of a p-adic number field.

    INPUT:

    - ``K`` -- a p-adic number field
    - ``a`` -- data defining an element of `K`

    The data ``a`` may be one of the following:

    - an element of the number field `K_0` underlying `K`,
    - a pair `a_0, s`, where `a_0` is an element of `K_0` and `s` is the
      precision (a positive ratinal number, or `\infty`),
    - a pair `a_0, f`; here `f` is a monic irreducible polynomial over the
      rationals, and `a_0` is an *approximate zero* of `f`. More precisely,
      `a_0` is an element of `K_0` which uniquely determines a zero of `f`
      in `K`.


    """
    assert isinstance(K, pAdicNumberField), "K must be a p-adic number field"
    if len(a) == 1:
        a = K.number_field()(a[0])
        return ElementOfpAdicNumberField(K, a)
    elif len(a) == 2:
        a_0 = K.number_field()(a[0])
        s = a[1]
        if s in QQ or s == Infinity:
            return ElementOfpAdicNumberField(K, a_0, s)
        else:
            f = a[1]
            return ElementOfpAdicNumberField_algebraic(K, a_0, f)
    else:
        raise AssertionError("wrong number of parameters")


def roots_of_rational_polynomial(K, f, approximations=None):
    r""" Return all the roots of a polynomial over a p-adic number field with
    given approximation.

    INPUT:

    - ``K`` -- a p-adic number field
    - ``f`` -- a nonzero univariate polynomial over the rationals
    - ``approximations`` -- a list of element of the number field underlying `K`,
                            or ``None`` (default: ``None``)

    OUTPUT:

    a list of all roots of `f` in `K`.

    If ``approximations`` is given, we only return those roots to which one of
    elements of this list is a *sufficient approximation*.

    Here we call an element `a_0\in K_0` a sufficient approximation to a root
    `a\in K` of `f` if `a_0` is stritly closer to `a` than to any other root
    of `f`.

    """
    from mclf.padic_extensions.approximate_factorizations import (
        approximate_factorization)
    # roots = []
    G = [g for g, _ in f.factor()]
    if approximations is None:

        for g in G:
            G = [g for g in approximate_factorization(K, f) if g.degree() == 1]

    raise NotImplementedError()


class ElementOfpAdicNumberField(SageObject):
    r""" A (possibly approximate) element of a `p`-adic number field `K`. It is
    represented by an element of the number field `K_0` underlying `K`,
    and its *precision*.

    INPUT:

    - ``K`` -- a p-adic number field
    - ``a`` -- an element of the number field `K_0` underlying `K`
    - ``s`` -- a positiv rational number, or ``Infinity``
               (default: ``Infinity``)

    OUTPUT: `a` as an approximate element of `K`, known with precision `s`.

    More precisely, the created object represents the closed ball

    .. MATH::

        D(a, s) := \{ a' \in K \mid v_K(a-a') \geq s \}.

    Any actual element of this ball is called an *approximation* of the
    element of `K` being represented.

    """

    def __init__(self, K, a, s=Infinity):
        assert isinstance(K, pAdicNumberField)
        self._parent = K
        a = K.number_field()(a)
        assert (s in QQ and s > 0) or s == Infinity, "s must be a positive\
            rational, or Infinity"
        self._is_exact = (s == Infinity)
        self._precision = s
        t = K.valuation()(a)
        assert t < s, "unsufficient precision for this element"
        self._valuation = t
        # reduce a to a potentially smaller element (if it is integral)
        if s < Infinity and t >= 0:
            self._approximation = K.approximation(a, s)
        else:
            self._approximation = a

    def __repr__(self):
        K = self.parent()
        if self.is_exact():
            return str(self.approximation())
        else:
            return "{} (mod {}^{})".format(self.approximation(), K.p(),
                                           self.precision())

    def parent(self):
        r""" Return the parent of this element, which is a p-adic number field.

        """
        return self._parent

    def padic_number_field(self):
        r"""  Return the parent of this element, which is a p-adic number field.

        This is the same as :meth:`parent`.
        """
        return self._parent

    def is_exact(self):
        r""" Return whether this element is exact.

        """
        return self._is_exact

    def precision(self):
        r""" Return the precision to which this element is known.

        This is a positive rational number `s`, or `\infty`. It has the
        following meaning: the 'element' which this object represents is
        actually the closed ball

        .. MATH::

             \{ a \in K \mid v_K(a-a_0) \geq s \}.

        Here `K` is the *parent* and `a_0` an *approximation* of this element.

        The precision `s` may take the value `\infty` if the element `a=a_0`
        is known exactly.

        """
        return self._precision

    def approximation(self, precision=None):
        r""" Return an approximation of this element.

        INPUT:

        - ``precision`` -- a positive rational, or ``None`` (default: ``None``)

        OUTPUT:

        an element `a_0` of the number field underlying the domain of this
        element `a` such that

        .. MATH::

            v_K(a-a_0) \geq s,

        where `s` is the precision of `a` or, or equal to ``precision``, if this
        value is given and is strictly smaller than the precision of `a`.

        If ``precision`` is given and is strictly larger than the precision of
        `a`, an error is raised.

        """
        if precision is not None:
            assert precision <= self.precision(), "insufficient precision"
            if precision == self.precision():
                return self._approximation
            elif precision < self.precision():
                K = self.parent()
                return K.approximation(self.approximation(), precision)
            else:
                raise AssertionError("insufficient precision")
        else:
            return self._approximation

    def polynomial(self, precision=None):
        r""" Return the polynomial representing this element of a p-adic number
        field.

        INPUT:

        - ``precision`` -- a positive rational, or ``None`` (default: ``None``)

        Let `K` be the parent of this element `a`, which is a p-adic number
        field. We choose an approximation `a_0` of `a`, which is an element
        of the number field `K_0` underlying `K`, such that the valuation
        `v_K(a-a_0)` is strictly less than the precision of `a`.

        We have a unique representation `a_0=g(\alpha)`, where
        `\alpha` is the canonical generator of `K_0/\mathbb{Q}` and `g` is
        a polynomial with rational coefficients, of degree `<[K:\mathbb{Q}_p]`.

        We return this polynomal `g \in \mathbb{Q}[x]`.

        If ``precision`` is given, then we choose our approximation ``a_0``
        with this precision, if possible.

        If the precision with which `a` is known is less then ``precision``,
        an error is returned.

        """
        from sage.all import PolynomialRing
        if self.parent().is_Qp():
            R = PolynomialRing(QQ, "x")
            return R(self.approximation(precision))
        else:
            return self.approximation(precision).polynomial()

    def valuation(self):
        r""" Return the valuation of this element of a p-adic number field.

        This is the canonical valuation `v_K` on the p-adic number field `K`,
        the parent of this element. It is normalized such that `v_K(p)=1`.

        """
        return self._valuation

    def distance(self, b):
        r""" Return the distance between this element and another one.

        INPUT:

        - ``b`` -- an element of the same p-adic number field `K`

        The element `b` may be given as an element of the underlying number
        field, or as an instance of :class:`ElementOfpAdicNumberField`.

        OUTPUT: the valuation of the difference between this element `a`
        and `b`.

        .. MATH::

            d(a,b):=v_K(a-b).

        Note that this is really minus the logarithm (to the base `p`, say) of
        the real distance. In particular, `d(a,b)` is large if `a` and `b` are
        close.

        Note also that `d(a,b)` is, by definition, less or equal to the minimum
        of the precisions with which `a` and `b` are known.

        EXAMPLES::

            sage: from mclf import *
            sage: Q2 = pAdicNumberField(QQ, 2)
            sage: a = element_of_padic_number_field(Q2, 2, 2); a
            2 (mod 2^2)

            sage: b = element_of_padic_number_field(Q2, 10); b
            10

            sage: c = element_of_padic_number_field(Q2, 6, 3); c
            6 (mod 2^3)

            sage: a.distance(b)
            2

            sage: a.distance(c)
            2

            sage: b.distance(c)
            2

        """
        a_0 = self.approximation()
        s1 = self.precision()
        if isinstance(b, ElementOfpAdicNumberField):
            b_0 = b.approximation()
            s2 = b.precision()
        else:
            b_0 = b
            s2 = Infinity
        t = self.parent().valuation()(a_0-b_0)
        return min(t, s1, s2)

    def evaluate_polynomial(self, f, precision=None):
        r""" Return the value of a polynomial on this element.

        INPUT:

        - ``f`` -- a univariate polynomial with rational coefficients
        - ``precision`` -- a positive integer, or ``None`` (default: ``None``)

        OUTPUT:

        The value `f(a)`, where `a` is this element of the p-adic number field
        `K`.

        Of course, the precision of `f(a)` depends on the precison of `a`, and
        on the polynomial `f`.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: Q2 = pAdicNumberField(QQ, 2)
            sage: a = element_of_padic_number_field(Q2, 2, 3); a
            2 (mod 2^3)

            sage: a.evaluate_polynomial(x^2 + 2)
            6 (mod 2^5)

        """
        from sage.all import PolynomialRing
        K = self.parent()
        v_K = K.valuation()
        R = PolynomialRing(QQ, "x")
        f = R(f)
        a = self.approximation()
        s = self.precision()
        b = f(a)
        if s == Infinity:
            return element_of_padic_number_field(K, b)
        else:
            # we have to compute the precision with which b is known;
            # it depends both on s and f
            n = f.degree()
            F = [f]
            for i in range(1, n + 1):
                F.append(F[i-1].derivative()/i)
            t = min([v_K(F[i](a)) + i*s for i in range(1, n + 1)])
            assert t > 0, "computed precision is not positiv"
            return element_of_padic_number_field(K, b, t)

    def rational_multiple(self, b):
        r""" Return the product of this element with a rational number.

        INPUT:

        - ``b`` -- a rational number.

        OUTPUT: the product `ab`, where `a` is this element of the p-adic number
        field `K`.

        """
        raise NotImplementedError()

    def power(self, k):
        r""" Return the `k`th of this element.

        INPUT:

        - ``k`` -- an integer

        OUTPUT: the element `a^k`, where `a` is this element of the p-adic
        number field `K`.

        """
        raise NotImplementedError()

    def minimal_polynomial(self):
        r""" Return the (approximate) minimal polynomial of this element.

        """
        raise NotImplementedError()

    def finite_representation(self, N):
        r""" Return the finite representation of this element.

        INPUT:

        - ``N`` -- a positive integer

        OUTPUT:

        The image of this element in the finite representation ring
        modulo `p^N`, which is a ring isomorphic to

        ..MATH::

            S_N = \mathcal{O}_K/(p^N).

        """
        raise NotImplementedError()


class ElementOfpAdicNumberField_algebraic(ElementOfpAdicNumberField):
    r""" An element of a `p`-adic number field `K` which is algebraic
    over `\mathbb{Q}`. It is specified by its (absolute) minimal polynomial
    and by a sufficiently good approximation (which is given by an
    approximate element of `K`).

    INPUT:

    - ``K`` -- a p-adic number field
    - ``a_0`` -- an element of the number field `K_0` underlying `K`
    - ``f`` -- a monic irreducible polynomial over `\mathbb{Q}`

    The element `a_0` must be a sufficiently good approximation of a zero
    `a` of `f` in `K`. Here 'sufficiently good' means that `a_0` is closer to
    `a` than to any other other zero of `f`.

    OUTPUT: the zero `a` of `f` as an algebraic element of `K`.


    EXAMPLES::

        sage: from mclf import *
        sage: Q2 = pAdicNumberField(QQ, 2)
        sage: R.<x> = QQ[]
        sage: f = x^2 + 7
        sage: a = Q2.algebraic_element(3, f)
        sage: a
        algebraic element approximated by 3 (mod 2^3)

        sage: a.minimal_polynomial()
        x^2 + 7

        sage: a.approximation()
        3

        sage: a.improve_approximation(5)
        sage: a
        algebraic element approximated by 11 (mod 2^5)

    """

    def __init__(self, K, a_0, f):
        a_0 = K.number_field()(a_0)
        s = K.precision_of_approximate_root(a_0, f)
        assert s > 0, "a_0 is not a good approximation of a root of f"
        self._parent = K
        self._approximation = a_0
        self._is_exact = True
        self._precision = s
        self._minpoly = f

    def __repr__(self):
        if self.precision() == Infinity:
            return "{} as algebraic element".format(self.approximation())
        else:
            return "algebraic element approximated by {} (mod {}^{})".format(
                self.approximation(), self.parent().p(), self.precision())

    def minimal_polynomial(self):
        r""" Return the absolute minimal polynomial of this algebraic element.

        """
        return self._minpoly

    def minpoly(self):
        r""" Return the absolute minimal polynomial of this algebraic element.

        This is identical to :meth:`minimal_polynomial`.
        """
        return self._minpoly

    def number_field_element(self):
        r""" Return this element as an element of an algebraic number field.

        """
        if not hasattr(self, "_number_field_element"):
            K = QQ.extension(self.minpoly(), "theta")
            return K.gen()

    def approximation(self, precision=None):
        r""" Return an approximation of this element.

        INPUT:

        - ``precision`` -- a positive rational, or ``None`` (default: ``None``)

        OUTPUT:

        an element `a_0` of the number field underlying the domain of this
        algebraic element `a` such that

        .. MATH::

            v_K(a-a_0) \geq s,

        where `s` is equal to ``precision``, if this value is given. If
        ``precision`` is not given, we return the approximation of `a` computed
        previously; it is guaranteed to be a *good approximation* of `a` as a
        root of its minimal polynomial.

        """
        if precision is not None:
            if precision == self.precision():
                return self._approximation
            elif precision < self.precision():
                K = self.parent()
                return K.approximation(self.approximation(), precision)
            else:
                self.improve_approximation(precision)
                return self._approximation
        else:
            return self._approximation

    def improve_approximation(self, s):
        r""" Improve the current approximation to a given precision.

        INPUT:

        - ``s`` -- a positive integer, strictly larger than the actual internal
                   precision

        When called, this methods improves the internal approximation of this
        algebraic element to precision `s`.

        """
        K = self.parent()
        self._approximation = K.approximate_root(self.minimal_polynomial(),
                                                 self._approximation, s)
        self._precision = s

    def evaluate_embedding(self, phi):
        r""" Return the image of this algebraic element under an embedding of
        p-adic number fields.

        INPUT:

        - ``phi`` -- an embedding `\varphi:K\to L` of p-adic number fields

        Here `K` must be equal to the parent of this algebraic element `a`.

        OUTPUT:

        the image `\varphi(a)\in L`, as an algebraic element.

        EXAMPLES::

            sage: from mclf import *
            sage: Q2 = pAdicNumberField(QQ, 2)
            sage: R.<x> = QQ[]
            sage: f = x^3 + 2
            sage: K = Q2.simple_extension(f)
            sage: g = approximate_factorization(K, f)[1]
            sage: L = g.stem_field()
            sage: phi = L.embedding()
            sage: a = K.algebraic_element(K.generator(), K.polynomial())
            sage: b = phi(a); b     # indirect doctest
            algebraic element approximated by 18*alpha6^5 + 21*alpha6^4 \
            + 22*alpha6^3 + 22*alpha6^2 + alpha6 + 30 (mod 2^16/3)

            sage: b.minimal_polynomial()
            x^3 + 2

        """
        K = self.parent()
        assert K.is_equal(phi.domain()), "the domain of phi must be equal to \
            the parent of this element"
        f = self.minimal_polynomial()
        L = phi.codomain()
        if self.precision() == Infinity:
            # this element is actually an element of the underlying nuber field
            # we may identify it with its approximation
            a = self.approximation()
            s = phi.precision()
            while True:
                b_0 = phi.evaluation(a, s)
                try:
                    return ElementOfpAdicNumberField_algebraic(L, b_0, f)
                except AssertionError:
                    s += 1
        else:
            while True:
                s = self.precision()
                b_0 = phi.evaluation(self.approximation(), s)
                try:
                    return ElementOfpAdicNumberField_algebraic(L, b_0, f)
                except AssertionError:
                    self.improve_approximation(s+1)

    def evaluate_polynomial(self, f, precision=None):
        r""" Return the value of a polynomial on this element.

        INPUT:

        - ``f`` -- a univariate polynomial with rational coefficients
        - ``precision`` -- a positive integer, or ``None`` (default: ``None``)

        OUTPUT:

        The value `f(a)`, where `a` is this element of the p-adic number field
        `K`, as an algebraic element of this p-adic number field `K`.

        If ``precision`` is given, then an element `b` of the underlying number
        field, which is an approximation of `f(a)` up to this
        precision, is returned.


        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: Q2 = pAdicNumberField(QQ, 2)
            sage: a = Q2.algebraic_element(3, x^2 + 7); a
            algebraic element approximated by 3 (mod 2^3)

            sage: a.evaluate_polynomial(x^3 + x + 1)
            algebraic element approximated by 15 (mod 2^4)

            sage: a.evaluate_polynomial(x^2+7)
            0 as algebraic element

        """
        if precision is not None:
            a_0 = self.approximation(precision)
            # this is not yet correct:
            return self.parent().approximate_evaluation(f, a_0, precision)
        else:
            # we compute the minimal polynomial of b=f(a)
            g = f(self.number_field_element()).minpoly()
            # now we have to compute an approximation of b=f(a) which is a
            # good approximation of g
            K = self.parent()
            while True:
                a_0 = self.approximation()
                s = self.precision()
                b_0 = self.parent().approximate_evaluation(f, a_0, s)
                try:
                    return ElementOfpAdicNumberField_algebraic(K, b_0, g)
                except AssertionError:
                    self.improve_approximation(s+1)

    def _required_precision(self, f, s):
        r""" Return the precision required to evaluate this element
        on a polynomial.

        INPUT:

        - ``f`` -- a polynomial with rational coefficients
        - ``s`` -- a positive rational number

        OUTPUT:

        a positive rational number `t` with the following property: if
        `a_0` is an approximation of this element `a` with precision `t` then
        the value `g(a_0)` will be an approximation of `f(a)` up to precision `s`.
        Or:

        .. MATH::

             v_K(a-a_0) \geg t \quad\Leftrightarrow\quad v_K(g(a)-g(a_0)).


        """
        raise NotImplementedError()

# ---------------------------------------------------------------------------

#                           helper functions
