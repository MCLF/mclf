# -*- coding: utf-8 -*-
r"""
Simple extensions of p-adic number fields
=========================================

In this module we implement a constructor class for finite simple extensions
of p-adic number fields.

Let `K` be a p-adic number field and `f\in K[x]` be a monic, irreducible and
integral polynomial. We wish to construct the stem field

.. MATH::

    L:= K(\alpha) \cong K[x]/(f)

of `f`, as a p-adic number field, and as an extension of `K`.

Recall that a p-adic number field `K` is represented as a pair `(K_0,v_K)`,
where `K_0` is a number field and `v_K` a p-adic valuation on `K_0`, such that
`K` is the completion of `K_0` with respect to `v_K`. As `K_0` is dense in `K`,
we may assume that `f\in K_0[x]` (actually, the polynomial `f` represents a
*Krasner class*, see :module:`approximate_factorizations<mclf.padic_extensions.\
approximate_factorizations>`). This suggests defining `L` as the pair
`(L_0, v_L)`, where

.. MATH::

    L_0 := K_0[x]/(f)

is the stem field of `f` and `v_L` is the unique extension of `v_K` to `L_0`
(the uniqueness is guaranteed since `f` is irreducible over `K` by assumption).

However, there are serious drawbacks of this naive approach. For one thing,
working with relative number fields of high degree in Sage is prohibitively
slow. Also, the construction of `L_0` as a stem field of `f` over `K_0` will
typically violate the condition (imposed in :module:`padic_number_fields\
<mclf.padic_extensions.padic_number_fields>`) that the canonical generator
of `L_0` is also an integral generator with respect to `v_L`.

We offer two different solutions to these problems. The first one, the result
of which we call the **exact extension** is as follows. We start by finding
a polynomial in `K_0[x]` (of small degree) whose image `\beta'` in
`L_0':=K_0[x]/(f)` is an (absolute) integral `p`-adic generator. The existence
of such an element is guaranteed by Lemma II.10.4 in Neukirch's book, and the
proofs gives a simple recipe for finding it. Then we compute the absolute
minimal polynomial `g\in\mathbb{Q}[x]` of `\beta'` and set

.. MATH::

    L_0 := \mathbb{Q}(\beta) = K_0[x]/(g).

By construction, `L_0` has a unique `p`-adic valuation `v_L` and the canonical
generator `\beta` is an integral generator w.r.t. `v_L`. Therefore, we can
define the completion `L` of `L_0` at `v_L` as a p-adic number field. Moreover,
the isomorphism `L_0'=K_0[x]/(f)\cong L_0`, sending `\beta'` to `\beta`,
defines an embedding of number fields `K_0\hookrightarrow L_0` which in turn
induces an embedding of p-adic number fields `K\hookrightarrow L`.

It turns out that this approach is still feasible for moderate degrees but is
too slow for large degrees. The problem is that the coefficients of the polynomial
`g` defining `L_0`, and the coefficients defining the embedding of `K_0` into
`L_0` become too large. The actual bottleneck is .... (find out!).

The second solution, which is the prefered one, is called the **approximate
extension**. We roughly proceed as above, but we compute the minimal polynomial
`g` of `\beta'` only *approximately*. If this approximation is sufficiently
sharp, the resulting p-adic number field `L` still has an embedding
`\varphi:K\hookrightarrow L` such that the resulting extension `L/K` is a stem
field for `f`. However, this embedding will typically not be induced by an
embedding of the underlying number fields.

In this second approach, the two most expensive computations, which are

- computing the characteristic polynomial of the matrix representing the
  element `\beta'` (in order to find the polynomial `g`), and
- solving a linear equation `A\cdot x = v` (in order to find the embedding of
  `K_0` into `L_0`)

are done over a quotient ring `\mathbb{Z}/p^s\mathbb{Z}`, where `s` is a
(small) positive integer (called the *precision*). So the speed-up compared
to the first approach is entirely due to the prevention of coefficient growth.

.. NOTE::

    Currently, we work with a fixed precision `s:=5`, and this seems to work in
    all examples considered so far. What is still missing is the automatism of
    increasing the precision if the computation fails or, better, an a priori
    estimate of a sufficient precision. So our current implementation may fail
    to compute the extensions, but if it doesn't the result is provably correct.


.. TODO::

    - make sure that we work with sufficient precision
    - also compute a root `\alpha\in L` of `f` along the way


EXAMPLES:



AUTHORS:

- Stefan Wewers (2022-2-22): initial version



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


from sage.all import (SageObject, QQ, NumberField, IntegerModRing,
                      vector, matrix, Infinity, GaussValuation)


class SimpleExtensionOfpAdicNumberField(SageObject):
    r""" A constructor class for a finite simple extension of a p-adic number field.

    INPUT:

    - ``K`` -- a p-adic number field
    - ``f`` -- a monic, integral and irreducible polynomial over `K`, or a
               Krasner class of such polynomials
    - ``name`` -- an alphanumeric string, or ``None`` (default: ``None``)

    OUTPUT: a constructor for the finite extension `L:=K[x]/(f)`.

    The main function of this object is to create an (absolute) p-adic number
    field `L` together with an embedding `K\hookrightarrow L` such that
    `L/K` is generated by an element with minimal polynomial `f`.


    """

    def __init__(self, K, f, name=None):
        from mclf.padic_extensions.approximate_factorizations import ApproximatePrimeFactor
        K_0 = K.number_field()
        if isinstance(f, ApproximatePrimeFactor):
            f = f.approximate_polynomial()
        f = f.change_ring(K_0)
        self._base_field = K
        self._polynomial = f
        # this is a preliminary and ad hoc  choice; in an improved version, the precision
        # should be chosen automatically to be 'just enough':
        self._precision = 5
        if name is None:
            self.name = "alpha{}".format(self.absolute_degree())
        else:
            self.name = name

    def __repr__(self):
        return "constructor for a finite extension of {} with equation {}".format(self.base_field(), self.polynomial())

    def base_field(self):
        return self._base_field

    def polynomial(self):
        r""" Return the polynomial defining this extension.

        OUTPUT: the polynomial `f\in K_0[x]` defining this extension `L=K[x]/(f)`.

        """
        return self._polynomial

    def degree(self):
        r""" Return the degree of this extension `L/K`.
        """
        return self.polynomial().degree()

    def absolute_degree(self):
        r""" Return the degree of the extension field as an absolute p-adic
        number field.
        """
        return self.degree()*self.base_field().absolute_degree()

    def precision(self):
        return self._precision

    def pseudovaluation(self):
        r""" Return the pseudovaluation corresponding to the equation defining this extension.

        OUTPUT: the infinite pseudovaluation `v_f` on `K_0[x]` extending `v_K`
        such that `v_f(f)=\infty`.

        Here `K_0` is the number field underlying the base field `K` and `f` is
        the equation defining this extension `L=K[x]/(f)`.

        """
        if not hasattr(self, "_pseudovaluation"):
            K = self.base_field()
            v_K = K.valuation()
            f = self.polynomial()
            v = GaussValuation(f.parent(), v_K)
            while v(f) < Infinity:
                V = v.mac_lane_step(f)
                assert len(V) == 1, "f is not irreducible"
                v = V[0]
            self._pseudovaluation = v
        return self._pseudovaluation

    def relative_number_field(self):
        r""" Return the relative number field of this extension,
        as a polynomial quotient ring.

        """
        from sage.all import PolynomialQuotientRing
        if not hasattr(self, "_relative_number_field"):
            f = self.polynomial()
            self._relative_number_field = PolynomialQuotientRing(f.parent(), f, "T")
        return self._relative_number_field

    def integral_generator(self):
        r""" Return an equation for a integral generator.

        OUTPUT:

        a polynomial `g\in K_0[x]` such that `\beta:=g(\alpha)` is an
        absolute integral generator for this simple extension `L=K[\alpha]`
        (here integral means that its powers yield an integral basis)


        ALGORITHM:

        We use the trick from the proof of Lemma II.10.4 from Neukirch's book.

        """
        if not hasattr(self, "_integral_generator"):
            L0 = self.relative_number_field()
            v = self.pseudovaluation()
            if v.residue_field().is_prime_field():
                beta = L0(v.uniformizer())
            else:
                pi = v.uniformizer()
                k = v.residue_field()
                thetab = v.residue_field().gen()
                theta = v.lift(thetab)
                if hasattr(k, "base_field"):
                    # this probably means that k is not a true finite field
                    from mclf.curves.smooth_projective_curves import make_finite_field
                    _, phi, _ = make_finite_field(k)
                    thetab = phi(thetab)
                h = thetab.minpoly().change_ring(QQ)
                if v(h(theta)) == v(pi):
                    beta = L0(theta)
                else:
                    beta = L0(theta + pi)
            self._integral_generator = beta
        return self._integral_generator

    def matrix_of_integral_generator(self):
        r""" Return a matrix representing the absolute integral generator.

        Let `\beta` be the (absolute) integral generator of this extension `L/K`.
        We return a square matrix, with `p`-integral rational numbers as entries,
        representing the action of `\beta` on the absolute extension
        `L/\mathbb{Q}_p`.

        """
        if not hasattr(self, "_matrix_of_integral_generator"):
            K = self.base_field()
            n = K.absolute_degree()
            m = self.degree()
            N = n*m
            alpha = K.generator()
            beta = self.integral_generator()
            g = beta.minpoly()
            # we initialize b_i such that beta^m = sum_j b_i[j]*beta^j
            # in each iteration of the i-loop below, we multiply the entries
            # with alpha, so that alpha^i*beta^m = sum_j b_i[j]*beta^j
            b_i = [-g[j] for j in range(m)]
            B = matrix(QQ, N)
            for i in range(n):
                for j in range(m):
                    k = i + n*j
                    # the k-th column of B represents alpha^i*beta^(j+1)
                    if j < m-1:
                        B[k+n, k] = QQ.one()
                    else:
                        # this is alpha^i*beta^m = sum_nu alpha^i*b_nu*beta^nu
                        #        = sum_{mu, nu} b_i[mu,nu]*alpha^mu*beta^nu
                        for mu in range(n):
                            for nu in range(m):
                                r = mu + n*nu
                                B[r, k] = B[r, k] + b_i[nu][mu]
                for j in range(m):
                    b_i[j] = b_i[j]*alpha

            self._matrix_of_integral_generator = B
        return self._matrix_of_integral_generator

    def exact_extension_field(self):
        r""" Return the exact extension field.

        """
        if not hasattr(self, "_exact_extension_field"):
            B = self.matrix_of_integral_generator()
            F = B.charpoly()
            L = NumberField(F, self.name)
            self._exact_extension_field = L
        return self._exact_extension_field

    def relative_base_change_matrix(self):
        r""" Return the relative base change matrix.

        We return the inverse of the matrix `T` whose columns are the coordinate
        vectors of the powers `1,\beta,\ldots,\beta^{m-1}`, with respect to the
        standard basis of this relative extension `L/K`.

        """
        if not hasattr(self, "_relative_base_change_matrix"):
            m = self.degree()
            K = self.base_field()
            L = self.relative_number_field()
            beta = self.integral_generator()
            intbasis = []
            b = L.one()
            for i in range(m):
                intbasis.append(b)
                if i < m-1:
                    b = b*beta
            # we create a matrix whose columns correspond to the
            # elements of the integral basis; this is the inverse of S
            T = matrix(K.number_field(), m)
            for i in range(m):
                for j in range(m):
                    T[i, j] = intbasis[j][i]
            self._inverse_relative_base_change_matrix = T
            self._relative_base_change_matrix = T.inverse()
        return self._relative_base_change_matrix

    def inverse_relative_base_change_matrix(self):
        r""" Return the relative inverse base change matrix.

        """
        if not hasattr(self, "_inverse_relative_base_change_matrix"):
            self.relative_base_change_matrix()
        return self._inverse_relative_base_change_matrix

    def coordinate_vector(self, a):
        r""" Return the coordinate vector corresponding to an element of this
        extension.

        INPUT:

        - ``a`` -- an element of the relative nuber field representing this extension

        OUTPUT:

        The coordinate vector of `a` with respect to the first integral basis
        (see definition below).

        Let `L/K` be this extension, `\alpha` the canonical integral generator
        of `K` and `\beta` be the new integral generator of `L`.
        Let `n=[K:\mathbb{Q}_p]` and `m=[L_K]`.

        The *first integral basis* consists of the elements

        .. MATH::

            `\alpha^i\beta^j`,

        where `i=0,\ldots,n-1` and `j=0,\ldots,m-1.

        """
        from sage.all import vector
        K = self.base_field()
        n = K.degree()
        L0 = self.relative_number_field()
        a = L0(a)
        rel_vector = self.relative_base_change_matrix()*vector(a.list())
        m = L0.degree()
        v = []
        for j in range(m):
            for i in range(n):
                v.append(rel_vector[j][i])
        return vector(v)

    def exact_transition_matrix(self):
        r""" Return the exact transition matrix.

        Let `L/K` be this extension, `\alpha` the canonical integral generator
        of `K` and `\beta` be the new integral generator of `L`.
        Let `n=[K:\mathbb{Q}_p]` and `m=[L_K]`.

        Then we have two integral bases for `L`:

        - the basis with elements `\alpha^i\beta^j`, where `i=0,\ldots,n-1`
          and `j=0,\ldots,m-1`, and
        - the basis with elements `\beta^k`, where `k=0,\ldots,nm-1`.

        The *transition matrix* is the matrix of the base change from the first
        to the second basis. This means that the columns consist of the elements
        of the second basis, written as coordinate vectors wrt the first basis.

        """
        from sage.all import GF
        if not hasattr(self, "_exact_transition_matrix"):
            N = self.absolute_degree()
            B = self.matrix_of_integral_generator()
            v = vector(QQ, N)
            v[0] = QQ.one()
            cols = []
            for i in range(N):
                cols.append(v)
                v = B*v
            A = matrix(QQ, N, cols).transpose()
            # we test whether A is unimodular
            p = self.base_field().p()
            Ab = A.change_ring(GF(p))
            assert Ab.is_invertible(), "something is wrong: A is not unimodular"
            self._exact_transition_matrix = A
        return self._exact_transition_matrix

    def exact_extension(self):
        r""" Return the exact extensions represented by this constructor.

        OUTPUT: an object of the class :class:`ExactpAdicExtension`, representing
        this simple extension `L/K`.

        This means that the number field `L_0` underlying `L` is a (simple)
        extension of `K_0`, the number field underlying `K`.

        .. NOTE::

            At the moment, there is an error in this construction: the absolute
            number field `L_0` constructed below may not satisfy the condition
            that its generator generates the ring of integers of its p-adic
            completion.

        """
        if hasattr(self, "_exact_extension"):
            return self._exact_extension
        from mclf.padic_extensions.padic_number_fields import pAdicNumberField
        from mclf.padic_extensions.padic_embeddings import ExactpAdicEmbedding
        from mclf.padic_extensions.padic_extensions import ExactpAdicExtension

        K = self.base_field()
        K_0 = K.number_field()
        L_0 = self.exact_extension_field()
        v_p = self.base_field().base_valuation()
        v_L = v_p.extension(L_0)
        L = pAdicNumberField(L_0, v_L)

        # we find the embedding of K_0 into L_0
        alpha = K.generator()
        A = self.exact_transition_matrix()
        v = A.solve_right(self.coordinate_vector(alpha))
        N = L.absolute_degree()
        beta = L.generator()
        beta_k = L_0.one()
        alpha_0 = L_0.zero()
        for k in range(N):
            alpha_0 += v[k]*beta_k
            beta_k = beta_k*beta
        phi = K_0.hom(alpha_0, L_0)
        L = ExactpAdicExtension(ExactpAdicEmbedding(K, L, phi))
        self._exact_extension = L
        return L

    # ------------------------------------------------------------------------
    #           methods for computing the approximate extension

    def approximate_extension(self):
        r""" Return the approximate extensions represented by this constructor.

        OUTPUT: an object of the class :class:`ExactpAdicExtension`, representing
        this simple extension `L/K`.

        This means that the number field `K_0` underlying `K` will probably not
        be a subfield of `L_0`, the number field underlying `L`. Therefore,
        we do not have an exact embedding of `K` into `L`, but only an
        *approximate* embedding.

        """
        if hasattr(self, "_approximate_extension"):
            return self._approximate_extension
        from mclf.padic_extensions.padic_extensions import ApproximatepAdicExtension
        phi = ApproximatepAdicExtension(self.approximate_embedding())
        self._approximate_extension = phi
        return phi

    def approximate_extension_field(self):
        r""" Return the approximate extension field, as an absolute
        p-adic number field.

        """
        from mclf.padic_extensions.padic_number_fields import pAdicNumberField
        if not hasattr(self, "_approximate_extension_field"):
            p = self.base_field().p()
            Bbar = self.approximate_matrix_of_integral_generator()
            fbar = Bbar.charpoly()
            f = fbar.change_ring(QQ)
            L_0 = NumberField(f, self.name)
            v_L = QQ.valuation(p).extension(L_0)
            self._approximate_extension_field = pAdicNumberField(L_0, v_L)
        return self._approximate_extension_field

    def approximate_embedding(self):
        r""" Return the embedding of the base field into the extension field.

        OUTPUT: the canonical embedding `\phi:K\hookrightarrow L` of absolute
        `p`-adic number fields, where `K` is the base field and `L` the extension
        field.

        """
        from mclf.padic_extensions.padic_embeddings import pAdicEmbedding
        from mclf.padic_extensions.elements_of_padic_number_fields import (
            ElementOfpAdicNumberField_algebraic)
        if hasattr(self, "_approximate_embedding"):
            return self._approximate_embedding

        K = self.base_field()
        L = self.approximate_extension_field()
        alpha = K.generator()

        # we find the embedding of K into L; this means finding an
        # element in L "close to alpha"
        # we do this calculation modulo p^s, where s is the current precision
        A = self.approximate_transition_matrix()       # entries in ZZ/p^s
        v = A.solve_right(self.approximate_coordinate_vector(alpha))
        N = L.absolute_degree()
        beta = L.generator()
        beta_a = L.finite_representation(beta, self.precision())  # in O_L/p^s
        L_a = beta_a.parent()
        beta_k = L_a.one()  # is beta_a^k in the k-loop below
        alpha_a = L_a.zero()
        for k in range(N):
            alpha_a += v[k]*beta_k
            beta_k = beta_k*beta_a
        alpha_0 = L.element_from_finite_representation(alpha_a)
        # it is not at all transparent to which precision the matrix A
        # has been computed; the required precision depends, it seems, only on
        # the polynomial defining K, and could be computed in advance

        alpha = ElementOfpAdicNumberField_algebraic(L, alpha_0, K.polynomial())
        phi = pAdicEmbedding(K, L, alpha)
        self._approximate_embedding = phi
        return phi

    def approximate_coordinate_vector(self, a):
        r""" Return the coordinate vector of an approximate element of the
        relative number field of this extension, with respect to the integral
        basis.

        INPUT:

        - ``a`` -- an element of the relative number field

        """
        from sage.all import vector
        K = self.base_field()
        s = self.precision()
        R = IntegerModRing(K.p()**s)
        n = K.degree()
        L0 = self.relative_number_field()
        a = L0(a)
        rel_vector = self.relative_base_change_matrix()*vector(a.list())
        m = L0.degree()
        v = []
        for j in range(m):
            for i in range(n):
                v.append(R(rel_vector[j][i]))
        return vector(v)

    def approximate_transition_matrix(self):
        r""" Return the approximate transition matrix.

        Let `L/K` be this extension, `\alpha` the canonical integral generator
        of `K` and `\beta` be the new integral generator of `L`.
        Let `n=[K:\mathbb{Q}_p]` and `m=[L_K]`.

        Then we have two integral bases for `L`:

        - the basis with elements `\alpha^i\beta^j`, where `i=0,\ldots,n-1`
          and `j=0,\ldots,m-1`, and
        - the basis with elements `\beta^k`, where `k=0,\ldots,nm-1`.

        The *transition matrix* is the matrix of the base change from the first
        to the second basis. This means that the columns consist of the elements
        of the second basis, written as coordinate vectors wrt the first basis.

        We return the transition matrix modulo `p^s`, where `s` is the current
        precision.

        """
        from sage.all import GF
        if not hasattr(self, "_exact_transition_matrix"):
            N = self.absolute_degree()
            Bbar = self.approximate_matrix_of_integral_generator()
            R = Bbar.base_ring()
            v = vector(R, N)
            v[0] = R.one()
            cols = []
            for i in range(N):
                cols.append(v)
                v = Bbar*v
            Abar = matrix(R, N, cols).transpose()
            # we test whether Abar is unimodular
            p = self.base_field().p()
            A0 = Abar.change_ring(GF(p))
            assert A0.is_invertible(), "something is wrong: A is not unimodular"
            self._approximate_transition_matrix = Abar
        return self._approximate_transition_matrix

    def approximate_transition_matrix_old(self):
        r""" Return the approximate transition matrix.

        Let `L/K` be this extension, `\alpha` the canonical integral generator
        of `K` and `\beta` be the new integral generator of `L`.
        Let `n=[K:\mathbb{Q}_p]` and `m=[L_K]`.

        Then we have two integral bases for `L`:

        - the basis with elements `\alpha^i\beta^j`, where `i=0,\ldots,n-1`
          and `j=0,\ldots,m-1`, and
        - the basis with elements `\beta^k`, where `k=0,\ldots,nm-1`.

        The *transition matrix* is the matrix of the base change from the first
        to the second basis. This means that the columns consist of the elements
        of the second basis, written as coordinate vectors wrt the first basis.

        We return the transition matrix modulo `p^s`, where `s` is the current
        precision (a positiv integer).

        """
        from sage.all import GF
        if not hasattr(self, "_approximate_transition_matrix"):
            p = self.base_field().p()
            s = self.precision()
            N = self.absolute_degree()
            rows = []
            beta = self.integral_generator()
            gamma = self.relative_number_field().one()
            for k in range(N):
                rows.append(self.approximate_coordinate_vector(gamma))
                gamma = gamma*beta
            R = IntegerModRing(p**s)
            A = matrix(R, N, rows).transpose()
            # we test whether A is unimodular
            Ab = A.change_ring(GF(p))
            assert Ab.is_invertible(), "something is wrong: A is not unimodular"
            self._approximate_transition_matrix = A
        return self._approximate_transition_matrix

    def approximate_matrix_of_integral_generator(self):
        r""" Return an approximate matrix representing the absolute integral generator.

        Let `\beta` be the (absolute) integral generator of this extension `L/K`.
        We return a square matrix, with entrie in `\mathbb{Z}/p^s`,
        representing the action of `\beta` on the absolute extension
        `L/\mathbb{Q}_p`, module `p^s`. Here `s` is the current precision
        (a positive integer).

        """
        if not hasattr(self, "_approximate_matrix_of_integral_generator"):
            s = self.precision()
            p = self.base_field().p()
            R = IntegerModRing(p**s)
            B = self.matrix_of_integral_generator()
            self._approximate_matrix_of_integral_generator = B.change_ring(R)
        return self._approximate_matrix_of_integral_generator
