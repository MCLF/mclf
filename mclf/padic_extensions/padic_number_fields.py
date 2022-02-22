# -*- coding: utf-8 -*-
r"""
p-adic number fields
====================


We represent an (absolute) `p`-adic number field `K` by a pair `(K_0, v_K)`,
where `K_0` is an (absolute) number field (i.e.\ a finite field extension of
`\mathbb{Q}`) and `v_K` is a nontrivial discrete valuation on `K_0` (and
therefore an extension to `K_0` of the `p`-adic valuation on `\mathbb{Q}`,
for some prime number `p`). Then `K` is identified with the completion of
`K_0` with respect to `v_K`.

The focus of this implementation is on computing extensions of p-adic number
fields, possibly of high degree, and on determining subfields. For instance,
given a polynomial `f\in\mathbb{Q}` and a prime number `p`, we may want to
compute the splitting field `L/\mathbb{Q}_p` of `f`, considered as a polynomial
over the field of `p`-adic numbers `\mathbb{Q}_p`. What we really compute is
a number field `L_0`, equipped with a discrete valuation `v_L` whose completion
is the splitting field `L/\mathbb{Q}_p` of `f`. For later applications in
{\sf MCLF} it is then sufficient to work with the pair `(L_0,v_L)`, e.g.
to compute the semistable reduction of a curve defined over `\mathbb{Q}`. We
remark that the number field `L_0` will typically be not at all the splitting
field of `f` over `\mathbb{Q}`. For instance, `L_0` may not contain any root of
`f`.

Elements of p-adic number fields
--------------------------------

For these reasons, we do not have plans to develop p-adic number fields as
*rings*, i.e. with element classes, arithmetic operations etc. Elements of
a p-adic number field `K` are usually just elements of the underlying number
field `K_0`. However, for certain taks it will be usuful to have the following
notion of elements of `K` available:

- An *approximate element* of `K` is defined as a closed ball inside `K`, i.e.
  a subset `B:=\{ a\in K \mid v_K(a-a_0) \geq s \}`, where `a_0\in K_0` and
  `s` is a positive rational number. Any element of `B\cap K_0`is called an
  *approximation* with *precison* `s`.
- An *algebraic element* of `K` is an element of `K` which is algebraic over
  `\mathbb{Q}`. Such an element `a\in K` can be represented by its minimal
  polynomial over `\mathbb{Q}` and a sufficietly good approximation `a_0\in K_0`.

The classes representing such elements are implemented in
:module:`elements_of_padic_number_fields<mclf.padic_extensions.\
elements_of_padic_number_fields`.

Embeddings of p-adic number fields
----------------------------------

Extensions of p-adic number fields
----------------------------------

Subfields of p-adic number fields
---------------------------------

Galois extensions
-----------------




AUTHORS:

- Stefan Wewers (2021-4-29): initial version


EXAMPLES:

We define the field of `2`-adic numbers::

    sage: from mclf import *
    sage: Q2 = pAdicNumberField(QQ, 2); Q2

Generally, p-adic number fields are represented by an *underlying number field*
equipped with a discrete (p-adic) valuation::

    sage: Q2.number_field()
    sage: Q2.valuation()


    sage: R.<x> = QQ[]
    sage: a = K.roots(x^2 + 7)[0]; a
    sage: a.minpoly()


    sage: f = x^4 + 2*x + 2
    sage: K, a = Q2.extension(f, "a"); K

    sage: K.number_field()
    sage: K.parent()

    sage: K.ramification_degree()

    sage: K.inertia_degree()

    sage: a = K.generator()
    sage: a.parent()

    sage: F = K.factor(f); F

    sage: g = F[0]
    sage: L =




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


from sage.all import (SageObject, ZZ, QQ, PolynomialRing, IntegerModRing,
                      vector, matrix, Infinity, GaussValuation)


class pAdicNumberField(SageObject):
    r""" An object representing an absolute p-adic number field.

    INPUT:

    - ``K_0`` -- an absolute number field
    - ``p`` -- a prime number, or a p-adic valuation on `K_0`
    - ``check`` -- a boolean (default: ``False``)

    If `p` is a prime number, then it is assumed that the `p`-adic valuation
    on `\mathbb{Q}` has a unique extension `v_K` to `K_0`. Similarly, if
    instead of `p` a discrete valuation `v_K` on `K_0` is given, it is assumed
    that `v_K` is the unique extension to `K_0` of the `p`-adic valuation of a
    prime number `p`.

    It is also assumed that the canonical generator of `K_0` is also an
    *integral generator*, i.e. a generator of the ring of integers of `K`.
    This is is checked only if ``check`` is ``True``.

    OUTPUT: the object representing the completion `K` of `K_0` with respect to `v_K`.


    """

    def __init__(self, K_0, p, check=False):
        assert K_0.is_absolute(), "K_0 must be an absolute number field"
        from sage.rings.valuation.valuation import DiscreteValuation
        if isinstance(p, DiscreteValuation):
            v_p = p
            p = v_p.p()
            assert v_p.domain().is_subring(K_0), "The domain of v_p must be a subfield of K_0"
        else:
            assert p.is_prime(), "p must be a prime number, or a `p`-adic valuation"
            v_p = QQ.valuation(p)
        V = v_p.extensions(K_0)
        assert len(V) == 1, "the p-adic valuation on QQ must have a unique extension to K_0"
        v_K = V[0]
        n = K_0.absolute_degree()
        if n > 1:
            alpha = K_0.gen()
            pi_K = v_K.uniformizer()
            e = ZZ(1/v_K(pi_K))
            F = v_K.residue_field()  # should be a finite field, therefore:
            f = F.cardinality().log(F.characteristic())  # should be the absolute degree of F
            # it is important to *not* use absolute_polynomial!
            P = K_0.gen().absolute_minpoly()
        else:
            K_0 = QQ
            pi_K = K_0(p)
            alpha = K_0.one()
            e = ZZ(1)
            f = ZZ(1)
            R = PolynomialRing(QQ, "x")
            P = R.gen() - alpha
        assert n == e*f
        self._number_field = K_0
        self._v_p = QQ.valuation(p)
        self._valuation = v_K
        self._p = p
        self._uniformizer = pi_K
        self._absolute_generator = alpha
        self._absolute_degree = n
        self._absolute_ramification_degree = e
        self._absolute_inertia_degree = f
        self._absolute_polynomial = P
        if check:
            self.check_integral_generator()

    def __repr__(self):
        if self.is_Qp():
            return "field of {}-adic numbers".format(self.p())
        else:
            return "{}-adic number field of degree {} in {}".format(
                self.p(), self.degree(), self.generator())

    def check_integral_generator(self):
        r""" Check if the canonical generator is also an integral generator.

        """
        from sage.all import GF
        n = self.degree()
        e = self.ramification_degree()
        f = self.inertia_degree()
        assert e*f == n, "v_K is not the extension of v_p to K_0"
        pi = self.uniformizer()
        if f == 1:
            intbasis = [pi**i for i in range(n)]
        else:
            v_K = self.valuation()
            zeta = v_K.lift(v_K.residue_field().gen())
            intbasis = []
            for i in range(e):
                for j in range(f):
                    intbasis.append(pi**i*zeta**j)
        A = matrix(QQ, n, [a.list() for a in intbasis])
        p = self.p()
        Ab = A.change_ring(GF(p))
        assert Ab.is_invertible(), (
            "the canonical generator is not an integeral generator")

    def base_field(self):
        r""" Return the 'base field', i.e. this p-adic number field itself.

        This method exists only for compatibility reasons.
        """
        return self

    def extension_field(self):
        r""" Return the 'extension_field', i.e. this p-adic number field itself.

        This method exists only for compatibility reasons.
        """
        return self

    def number_field(self):
        r"""Return the number field representing this p-adic extension.

        """
        return self._number_field

    def is_equal(self, K):
        r""" Return whether this p-adic number field is equal to another one.

        We need this mainly because we want to consider consider an extension
        of p-adic fields to be equal to its extension field.
        """
        return self.extension_field() == K.extension_field()

    def base_valuation(self):
        r"""
        Return the `p`-adic valuation, i.e. the restriction of `v_K` to `\mathbb{Q}`.
        """
        return self._v_p

    def valuation(self):
        r"""
        Return the valuation on the underlying number field of this p-adic extension.

        It is normalized such that `v_K(p)=1`.
        """
        return self._valuation

    def normalized_valuation(self):
        r"""
        Return the normalized valuation on this p-adic field.

        Here *normalized* means that the valuation takes the value `1` on a
        uniformizer.

        """
        v = self.valuation().scale(self.absolute_ramification_degree())
        assert v(v.uniformizer()) == 1
        return v

    def p(self):
        r"""
        Return the prime `p`.
        """
        return self._p

    def uniformizer(self):
        r"""
        Return the standard unifomizer of this p-adic number field.
        """
        return self._uniformizer

    def absolute_generator(self):
        r"""
        Return the standard absolute generator of this p-adic number field.
        """
        return self._absolute_generator

    def generator(self):
        r"""
        Return the standard absolute generator of this p-adic number field.
        """
        return self._absolute_generator

    def absolute_degree(self):
        r"""
        Return the degree of this p-adic field as an extension of `\mathbb{Q}_p`.

        """
        return self._absolute_degree

    def degree(self):
        r"""
        Return the degree of this p-adic number field as an extension of `\mathbb{Q}_p`.

        This is the same as :meth:`absolute_degree`.
        """
        return self._absolute_degree

    def ramification_degree(self):
        r"""
        Return the absolute ramification degree of this p-adic number .

        This is the same as :meth:`absolute_ramification_degree`.
        """
        return self._absolute_ramification_degree

    def absolute_ramification_degree(self):
        r"""
        Return the absolute ramification degree of this p-adic number field.

        This is the same as :meth:`ramification_degree`.
        """
        return self._absolute_ramification_degree

    def absolute_inertia_degree(self):
        r"""
        Return the absolute inertia degree of this p-adic number field.

        """
        return self._absolute_inertia_degree

    def inertia_degree(self):
        r"""
        Return the absolute inertia degree of this p-adic number field.

        This is the same as :meth:`absolute_inertia_degree`.

        """
        return self._absolute_inertia_degree

    def absolute_polynomial(self):
        r""" Return the absolute minimal polynomial of the standard generator of `K`.
        """
        return self._absolute_polynomial

    def polynomial(self):
        r"""
        Return the absolute minimal polynomial of the standard generator of `K`.

        This is the same as :meth:`absolute_polynomial`.
        """
        return self._absolute_polynomial

    def is_Qp(self):
        r"""
        Return ``True`` if this is the padic-completion of the field of rational numbers.
        """
        return self.degree() == 1

    def identity(self):
        r""" Return the identity morphism of this p-adic number field.

        """
        from mclf.padic_extensions.padic_embeddings import ExactpAdicEmbedding
        return ExactpAdicEmbedding(self, self)

    def embedding_of_Qp(self):
        r""" Return the identity map for this p-adic number field.

        """
        from mclf.padic_extensions.padic_embeddings import ExactpAdicEmbedding
        Q_p = pAdicNumberField(QQ, self.base_valuation())
        return ExactpAdicEmbedding(Q_p, self)

    def as_extension_of_Qp(self):
        r""" Return this `p`-adic number field as an extension of `\mathbb{Q}_p`.

        """
        from mclf.padic_extensions.padic_extensions import ExactpAdicExtension
        return ExactpAdicExtension(self.embedding_of_Qp())

    def as_identity_extension(self):
        r""" Return this p-adic number field as an extension of itself.

        """
        from mclf.padic_extensions.padic_extensions import ExactpAdicExtension
        return ExactpAdicExtension(self.identity())

    def simple_extension(self, f, name=None, exact_extension=False):
        r""" Return the extension of this p-adic number field defined by an irreducible polynomial.

        INPUT:

        - ``f`` -- a monic, integral and irreducible polynomial over this p-adic
                 number field `K`, or a Krasner equivalence class of such a polynomial
        - ``name`` -- an alphanumeric string, or ``None`` (default: ``None``)
        - ``exact_extension`` -- a boolean (default: ``False``)

        OUTPUT: the stem field `L=K[x]/(f)`, as an extension of `p`-adic number fields.

        By default, the output is an object of :class:`ApproximateExtension`.
        If ``exact_extension`` is ``True``, it is a object of :class:`ExactpAdicExtension`.

        If ``name`` is given, this will be the name of the canonical generator.

        """
        from mclf.padic_extensions.simple_extensions_of_padic_number_fields\
            import SimpleExtensionOfpAdicNumberField
        L = SimpleExtensionOfpAdicNumberField(self, f, name)
        if exact_extension:
            return L.exact_extension()
        else:
            return L.approximate_extension()

    def purely_ramified_extension(self, n):
        r""" Return a purely ramified extension of this p-adic number field with given
        ramification degree.

        """
        K0 = self.number_field()
        R = PolynomialRing(K0, "T")
        f = R.gen()**n - self.uniformizer()
        return self.simple_extension(f)

    def unramified_extension(self, n):
        r""" Return the unramified extension of this p-adic number field of given degree.

        """
        raise NotImplementedError()

    def splitting_field(self, f, roots=False):
        r""" Return the splitting field of a polynomial.

        INPUT:

        - ``f`` -- a univariate polynomial over the underlying number field `K_0`
        - ``roots`` -- a boolean (default: ``False``)

        OUTPUT:

        the splitting field `L/K` of `f` over this `p`-adic number field `K`.

        If ``root`` is ``True`` we return a list of the roots of `f`.

        .. NOTE::

            We have to make sure, that the result if a p-adic number field, as
            an *extension* of this field `K`.

        """
        raise NotImplementedError()

    def weak_splitting_field(self, f):
        r""" Return the weak splitting field of a polynomial.

        INPUT:

        - ``f`` -- a univariate polynomial over the underlying number field `K_0`

        OUTPUT: the weak splitting field of `f` over this `p`-adic number field.

        .. NOTE::

            We have to make sure, that the result if a p-adic number field, as
            an *extension* of this field `K`.

        """
        from mclf.padic_extensions.approximate_factorizations import (
            weak_splitting_field)
        return weak_splitting_field(self, f)

    # ------------------------------------------------------------------------

    #              functions on and for elements

    def element(self, a, s=Infinity):
        r""" Return the element of this p-adic number field corresponding to
        an element `a` of the underlying number field, up to precision `s`.

        INPUT:

        - ``a`` - an element of the underlying number field `K_0`
        - ``s`` - a positive rational number, or ``Infinity``
                  (default: ``Infinity)

        OUTPUT:

        the element of this p.adic number field corresponding to `a`, up to
        precision `s`.

        If `s=\infty` then we return an instance of
        ::class::`ElementOfpAdicNumberField_exact<mclf.padic_extensions.\\
        elements_of_padic_number_fields.ElementOfpAdicNumberField_exact>`.
        Otherwise, an instance of
        ::class::`ElementOfpAdicNumberField_exact<mclf.padic_extensions.\\
        elements_of_padic_number_fields.ElementOfpAdicNumberField_approximate>`.

        """
        from mclf.padic_extensions.elements_of_padic_number_fields import (
            element_of_padic_number_field)
        a = self.number_field()(a)
        return element_of_padic_number_field(self, a, s)
        raise NotImplementedError()

    def algebraic_element(self, a_0, f=None):
        r""" Return an algebraic element of this p-adic number field.

        INPUT:

        - ``a_0`` -- an element of the underlying number field
        - ``f`` -- a monic irreducible polynomial over the rationals, or ``None``
                   (default: ``None``)

        OUTPUT:

        If `f` is given, `a_0` must be good approximation of a zero `a` of `f`.
        Then we return the zero `a` of `f` approximated by `a_0`, as an
        algebraic element.

        If `f` is not given, we return the element `a_0`, considered as an
        algebraic element.
        """
        from mclf.padic_extensions.elements_of_padic_number_fields import (
            ElementOfpAdicNumberField_algebraic)
        if f is None:
            return ElementOfpAdicNumberField_algebraic(self, a_0, a_0.minpoly())
        else:
            return ElementOfpAdicNumberField_algebraic(self, a_0, f)

    def coefficients(self, a):
        r""" Return the coefficient list of this element.

        INPUT:

        - ``a`` -- an element of the underlying number field

        OUTPUT:

        the list of coefficients of the representation of `a` as a linear
        combination of the canonical integral basis.

        Since we assume that the canonical integral basis is the canonical
        power basis of the underlying number field, we can use the method
        ::meth::`list` on `a`.

        """
        a = self.number_field()(a)
        return list(a)

    def is_integral(self, a):
        r""" Return whether the element `a` is integral.

        INPUT:

        - ``a`` - an element of the underlying nuber field

        OUTPUT:

        whether `a` is an integral element of this `p`-adic number field.

        This is true if and only if the coefficients of `a` (with respect to
        the canonical integral basis) are integers.

        """
        v_p = self.base_valuation()
        return all(v_p(c) >= 0 for c in self.coefficients(a))

    def finite_quotient_ring(self, N=None):
        r""" Return a ring in which the finite representations of integral
        elements live.

        INPUT:

        - ``N`` - a positive integer, or ``None`` (default: ``None``)

        OUTPUT: the polynomial quotion ring

        .. MATH::

            S = (\mathbb{Z}/p^N\mathbbb{Z})[T]/(F_N),

        where `F_N` is the reduction mod `p^N` of the defining polynomial.

        Because of our assumption that the powers of the generator yield an
        integral basis, this ring is isomorphic to

        .. MATH::

            \mathcal{O}_K/p^N.

        If `N` is not given, we take least integer strictly greater than `s`,
        where `s` is the value specified by ::meth::`required_precision`.

        """
        if N is None and hasattr(self, "_finite_quotient_ring"):
            return self._finite_quotient_ring
        if N is None:
            N = self.required_precision().floor() + 1
        p = self.p()
        R = IntegerModRing(p**N)
        F_N = self.polynomial().change_ring(R)
        from sage.rings.polynomial.polynomial_quotient_ring import (
            PolynomialQuotientRing)
        return PolynomialQuotientRing(F_N.parent(), F_N)

    def finite_representation(self, a, N=None):
        r""" Return the finite representation of ``a`` modulo `p^N`.

        INPUT:

        - ``a`` -- an integral element of the underlying number field
        - ``N`` -- a positive integer, or ``None`` (default: ``None``)

        OUTPUT: an element of the approximation ring mod `p^N`

        """
        S = self.finite_quotient_ring(N)
        a = self.number_field()(a)
        assert self.is_integral(a), "a must be integral"
        return S(list(a))

    def element_from_finite_representation(self, ab):
        r""" Return a lift of an element of a finite representation ring.

        INPUT:

        - ``ab`` -- an element of a finite representation ring

        OUTPUT: a

        n integral element of the underlying number field,
        lifting the element `\bar{a}`.

        """
        return self.number_field()([ZZ(c) for c in list(ab)])

    def approximation(self, a, s=None):
        r""" Return an approximation of an element of the underlying number
        field.

        INPUT:

        - ``a`` - an integral element of the underlying number field
        - ``s`` -- a positive rational, or ``None`` (default: ``None``)

        OUTPUT:

        an integral element `a_0` of the underlying number field such that

        .. MATH::

            v_K(a - a_0) > s.

        The coefficients of `a_0` with respect to the canonical integral basis
        are the standard representatives of the coefficients of `a` mod `p^N`.

        """
        from sage.all import ceil
        assert self.is_integral(a), "the element a is not integral"
        if s is None:
            s = self.required_precision()
        N = ceil(s)
        K_0 = self.number_field()
        m = self.p()**N
        Zm = IntegerModRing(m)
        return K_0([ZZ(Zm(c)) for c in list(a)])

    def valuation_of_polynomial(self, f, a, precision=None):
        r""" Return the valuation of an element of this number field which is
        the evaluation of a polynomial.

        INPUT:

        - ``f`` -- a polynomial over a subfield of the underlying number field
        - ``a`` -- an element of the underlying number field
        - ``precision`` -- a positive rational, or ``None`` (default: ``None``)

        OUTPUT: the valuation `v_K(f(a))`.

        If ``precision`` is given, we return the minimum of `v_K(f(a))` and
        ``precision``. In large examples, this is much faster as we only have
        to evaluate `f(a)` up to this (finite) precision.

        For the moment, this is function evaluates `v_K(f(a))` in the obvious
        way. In the future, we can try to do something smarter which should
        be faster for large examples.

        """
        if precision is None:
            return self.valuation()(f(a))
        else:
            precision = max(0, precision)
            t = self.valuation()(self.approximate_evaluation(f, a, precision + 1))
            return min(t, precision)

    def root(self, f, a_0):
        r""" Return the root of a polynomial determined by an approximation.

        """
        raise NotImplementedError()

    def roots(self, f):
        r""" Return a list of all roots of a polynomial contained in this
        p-adic number field.

        """
        raise NotImplementedError()

    def integral_basis(self):
        r""" Return the fixed integral basis of this p-adic number field.

        OUTPUT: a list of elements of the number field `K_0` underlying this
        `p`-adic number field `K` which form an integral basis of the valuation
        ring of `v_K`.

        By our assumption, the powers of the canonical generator yield an
        integral basis.

        """

        if not hasattr(self, "_integral_basis"):
            alpha = self.generator()
            self._integral_basis = [alpha**i for i in range(self.degree())]
        return self._integral_basis

    def matrix(self, a):
        r"""
        Return the matrix representing the element ``a``.

        INPUT:

        - ``a`` -- an element of the underlying number field of this p-adic extension

        OUTPUT:

        The matrix representing the element `a` of the underlying number field
        `K`, with respect to the canonical integral basis.

        """
        assert a in self.number_field(), "a must be an element of the underlying number field"
        if self.is_Qp():
            return matrix([QQ(a)])
        else:
            a = self.number_field()(a)
            return a.matrix().transpose()

    def approximate_matrix(self, a, N):
        r""" Return an approximation of the matrix corresponding to an integral element.

        INPUT:

        - ``a`` -- an integral element of the number field underlying this
                   `p`-adic number fields
        - ``N`` -- a positive integer

        OUTPUT: a square matrix over `\mathbb{Z}/p^N` which is the reduction
        of the matrix representing `a`.

        """
        R = IntegerModRing(self.p()**N)
        return self.matrix(a).change_ring(R)

    def vector(self, a):
        r"""
        Return the vector corresponding to an element of the underlying number field.

        INPUT:

        - ``a`` -- an element of the number field `K_0` underlying this `p`-adic number field

        OUTPUT:

        the vector of coefficients corresponding to the representation
        of `a` as a linear combination of the integral basis of `K`.

        """
        if self.is_Qp():
            return vector([QQ(a)])
        else:
            a = self.number_field()(a)
            return a.vector()

    def element_from_vector(self, v):
        r"""
        Return the element corresponding to a given vector.

        INPUT:

        - ``v`` -- a vector of rational numbers with length equal to the degree of `K`

        OUTPUT:

        the linear combination of the canonical integral basis of `K`
        corresponding to `v`.

        """
        return self.number_field()(list(v))

    def element_from_approximate_matrix(self, A):
        r""" Return the element corresponding to an approximate matrix.

        INPUT:

        - ``A`` -- a square matrix over the ring `\mathbb{Z}/p^N`

        It is assume that `A` is the reduction of a matrix corresponding to an
        integral element `a` of the number field `K_0`.

        OUTPUT: an element of the congruence class of `a` modulo `p^N`.

        """
        return self.element_from_vector(A.column(0).change_ring(QQ))

    def difference_polynomial(self):
        r""" Return the difference polynomial of the polynomial defining this field.

        Let `\alpha` be the absolute generator of this `p`-adic number field and
        `f` its minimal polynomial over `\mathbb{Q}_p` (actually, `f` has integeral
        coefficients!). The *difference polynomial* is the polynomial

        .. MATH::

            \Delta := f(\alpha + x)/x \in \mathbb{Z}[x].

        Note that the zeroes of `\Delta` are the differences `\alpha-\beta`,
        where `\beta` runs over the roots of `f` distinct from `\alpha`,
        whence the name.

        If this `p`-adic number field is `\mathbb{Q}_p` then we set
        `\Delta := 1`

        """
        if not hasattr(self, "_difference_polynomial"):
            f = self.polynomial()
            x = f.parent().gen()
            alpha = self.generator()
            self._difference_polynomial = f(x + alpha).shift(-1)
        return self._difference_polynomial

    def difference_newton_polygon(self):
        r""" Return the Newton polygon of the difference polynomial.

        """
        from sage.geometry.newton_polygon import NewtonPolygon
        if not hasattr(self, "_difference_newton_polygon"):
            v_K = self.valuation()
            Delta = self.difference_polynomial()
            self._difference_newton_polygon = NewtonPolygon(
                [(i, v_K(Delta[i])) for i in range(1, Delta.degree() + 1)])
        return self._difference_newton_polygon

    def required_precision(self):
        r""" Return the precision required to approximate the generator of this
             `p`-adic number field.

        OUTPUT: a positive rational number `s` with the following property. Let
        `\alpha` denote the absolute generator of this `p`-adic number field `K`,
        and let `f` be its absolute minimal polynomial. Let `L/K` be a finite
        extension and `\beta\in L`. If `v_L(\alpha-\beta) > s` then

        .. MATH::

            K\subset \mathbb{Q}_p(\beta)`.

        If this `p`-adic number field is `\mathbb{Q}_p` then we set
        `s := 0`.


        """
        if not hasattr(self, "_required_precision"):
            if self.is_Qp():
                s = QQ.zero()
            else:
                slopes = self.difference_newton_polygon().slopes()
                if len(slopes) == 0:
                    s = QQ.zero()
                else:
                    s = -slopes[0]
            self._required_precision = s
        return self._required_precision

    def approximate_evaluation(self, f, a, s):
        r""" Return the approximate value of a polynomial.

        INPUT:

        - ``f`` -- a polynomial with integeral coefficients
        - ``a`` -- an element of the number field underlying this `p`-adic field
        - ``s`` -- a positive rational number, or ``Infinity``

        OUTPUT: the value `f(a)`, up to precision `s`.

        """
        assert s > 0, "s must be positive"
        if s == Infinity:
            return f(a)
        N = QQ(s+1).floor()
        if self.is_Qp():
            return self.approximation(f(a), N)
        else:
            f = f.change_ring(ZZ)
            ab = self.finite_representation(a, N)
            return self.element_from_finite_representation(f(ab))

    def is_approximate_root(self, a0, f):
        r""" Return whether a p-adic element is an approximate root of a
        polynomial.

        """
        return self.precision_of_approximate_root(self, a0, f) > 0

    def precision_of_approximate_root(self, a0, f):
        r""" Return the precision of an approximate root.

        INPUT:

        - ``a0`` -- an element of the underlying number field
        - ``f`` -- a polynomial over a subfield of the underlying number field

        OUTPUT:

        If `a_0` is a good approximation to a root `a` of `f`, then we return
        `v_K(a-a_0)` (which is then positive).

        Otherwise we return `0`. So this method can be used to test whether
        `a_0` is an approximate root.

        """
        # we compute the Newton polygon of f(a_0+x)
        F = [f]
        n = f.degree()
        for i in range(1, n + 1):
            F.append(F[i-1].derivative()/i)
        v0 = self.valuation_of_polynomial(F[0], a0)
        if v0 == Infinity:
            return Infinity
        v1 = self.valuation_of_polynomial(F[1], a0)
        s = v0 - v1
        if s <= 0:
            return QQ.zero()
        else:
            for i in range(2, min(n, (v0*s**(-1)).ceil()) + 1):
                t_i = v0 - i*s
                if self.valuation_of_polynomial(F[i], a0, precision=t_i) <= t_i:
                    return QQ.zero()
            return s

    def approximate_root(self, f, a0, s):
        r""" Return an approximate root of a polynomial.

        INPUT:

        - ``f`` -- a polynomial with integral coefficients
        - ``a0`` -- an element of the number field underlying this `p`-adic field
        - ``s`` -- a positive rational number

        It is assumed that `a_0` is integral and a sufficient approximation of
        some root `a` of `f`. Here *sufficient* means that `a_0` is strictly
        closer to `a` than to any other root.

        OUTPUT: an element `a_1` such that `v_K(a - a_1) \geq s`.

        """
        v_K = self.valuation()
        f = f.change_ring(ZZ)
        fx = f.derivative()
        fa0 = self.approximate_evaluation(f, a0, s)
        fxa0 = self.approximate_evaluation(fx, a0, s)
        t0 = v_K(fa0)
        t1 = v_K(fxa0)
        N = QQ(s+1).floor()
        while t0 < Infinity and t0 < s + t1:
            # we have v_K(a-a_1) = t0 - t1, so this is the condition to stop
            if t0 > 2*t1:
                # under this condition, we can use Newton approximation
                a0 = self.approximation(a0 - fa0/fxa0, N)
            else:
                # we have to use another method
                R = f.change_ring(self.number_field()).parent()
                x = R.gen()
                v0 = GaussValuation(R, self.valuation())
                t = t0 - t1
                phi = x - a0
                v = v0.augmentation(phi, t)
                while t <= s:
                    # this only works if f is monic
                    V = v.mac_lane_step(f)
                    assert len(V) == 1
                    v = V[0]
                    t = v(v.phi())
                a0 = -v.phi()[0]
            fa0 = self.approximate_evaluation(f, a0, s)
            fxa0 = self.approximate_evaluation(fx, a0, s)
            t0 = v_K(fa0)
            t1 = v_K(fxa0)
        return self.approximation(a0, s)
