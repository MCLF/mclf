# -*- coding: utf-8 -*-
r"""
Standard fields
===============

We call a field `K` a *standard field* if `K` is of one of the following types:

1. `K` is a *finite field*,
2. `K` is a *number field* (i.e. a finite extension of \mathbb{Q}),
3. `K` is a *function field*, i.e. `K` is a finitely generated extension of
   transcendence degree one of a subfield `k`, which is itself either a finite
   field or a number field.

Basically all calculations done in this project involve calculations with such
standard fields.

One problem is that is that in Sage standard fields sometimes do not occur in
a any kind of standard form, which makes it hard to deal with
them in a systematic way. For instance, a number field may be represented as
an absolute number field, or as a tower of relative number fields.

To solve this problem, we create a class
:class:`StandardField`. An object of this class represents a standard field
`K`, which may be given in any form which provides internal access to a
standard model of `K`.


.. TODO::

    Many things, e.g.

    - the method :meth:`hom` should have a unfied way of specifying the
      parameters. For instance, K.hom(L) should always work if K is a
      subfield of the original model of L


EXAMPLES::

    sage: from mclf import *
    sage: k0.<a> = GF(4)
    sage: R.<t> = k0[]
    sage: k1.<t> = k0.extension(t^3 + t^2 + t + a); k1
    Univariate Quotient Polynomial Ring in t over Finite Field in a of size 2^2
    with modulus t^3 + t^2 + t + a

This is the kind of fields that can make trouble. For instance, the method
:meth:`is_perfect` is not implemented, and therefore many algorithms involving
function fields over `k` do not work. We therefore compute its
standard model.::

    sage: k = standard_field(k1); k
    Finite Field in z6 of size 2^6 as a standard field

This new object contains the original field, and a standard model.::

    sage: k.original_model()
    Univariate Quotient Polynomial Ring in t over Finite Field in a of size 2^2
    with modulus t^3 + t^2 + t + a
    sage: k.standard_model()
    Finite Field in z6 of size 2^6

We can coerce elements of the original field into its standard model.::

    sage: k(a+t)
    z6^3 + z6^2

It works similarly for number fields and function fields.::

    sage: F0.<x> = FunctionField(k1)
    sage: R.<y> = F0[]
    sage: F.<y> = F0.extension(y^2+x^3+a); F
    Function field in y defined by y^2 + x^3 + a
    sage: standard_function_field(F)
    Function field in y_ defined by y_^3 + x_^2 + z6^3 + z6^2 + z6
    as standard function field

We can replace the constant base field of a standard function field.::

    sage: standard_function_field(F, k0)
    # doesn't work yet!

"""

from sage.all import SageObject, lcm
from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing


def is_standard_field(K):
    r""" Return whether `K` is a standard field.

    INPUT:

    - ``K`` -- a field

    OUTPUT:

    Whether `K` is a standard field; this means that `K` is of one of the
    following types:

    1. `K` is a finite field
    2. `K` is a number field
    3. `K` is a function field, and the constant base field is either finite or
       a number field

    EXAMPLES::

        sage: from mclf import *
        sage: is_standard_field(QQ)
        True
        sage: is_standard_field(RR)
        False

    """
    from sage.categories.number_fields import NumberFields
    from sage.categories.function_fields import FunctionFields
    assert K.is_field(), "K must be a field"
    if K.is_finite() or K in NumberFields:
        return True
    elif K in FunctionFields:
        k = K.constant_base_field()
        return k.is_finite() or k in NumberFields
    else:
        return False


def standard_field(K):
    r""" Return the standard form of this field.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    the object representing `K` and its normal model.

    EXAMPLES::

        sage: from mclf import *
        sage: standard_field(QQ)
        Rational Field as a standard field

        sage: R.<x> = GF(2)[]
        sage: k.<z> = GF(2).extension(x^3+x^2+1)
        sage: k = standard_field(k); k
        Finite Field in z of size 2^3 as a standard field
        sage: k.generator()
        z+1
        sage: k.polynomial()
        z3^3 + z3 + 1

        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^2+x+1)
        sage: L.<b> = K.extension(x^3+a*x+1)
        sage: LL = standard_field(L)
        sage: LL.underlying_field()
        Number Field in b with defining polynomial x^3 + a*x + 1 over its base
            field
        sage: LL.standard_model()
        Number Field in b with defining polynomial
            x^6 - x^4 + 2*x^3 + x^2 - x + 1
        sage: LL.from_original_model()(b)
        b
        sage: LL.generator()
        b
        sage: LL.polynomial()
        x^6 - x^4 + 2*x^3 + x^2 - x + 1

        sage: k0 = GF(2)
        sage: K0.<x> = FunctionField(k0)
        sage: R.<y> = K0[]
        sage: K.<y> = K0.extension(y^2+y+x^3+1)
        sage: S.<z> = K[]
        sage: L.<z> = K.extension(z^3 +y*z - x^2)
        sage: F = standard_field(L); F
        Function field in z defined by z^3 + y*z + x^2, as a standard field
        sage: F.standard_model()
        Function field in z defined by z^6 + z^4 + (x^3 + 1)*z^2 + x^2*z + x^4
        sage: F.from_original_model()(y)
        1/x^2*z^5 + 1/x^2*z^3 + z^2 + ((x^3 + 1)/x^2)*z + 1

    """
    from sage.categories.number_fields import NumberFields
    assert K.is_field(), "K must be a field"
    if K.is_finite():
        return StandardFiniteField(K)
    elif K in NumberFields:
        return StandardNumberField(K)
    else:
        return standard_function_field(K)


def standard_rational_function_field(k, var_name="xx"):
    r""" Return the standard rational function field with given
    constant base field.

    INPUT:

    - ``k`` - a finite field or a number field
    - ``var_name`` -- an alphanumeric string (default: "xx")

    OUTPUT:

    The rational function field `k(x)`, as a standard field, and with
    variable name ``var_name``.

    EXAMPLES::

        sage: from mclf import *
        sage: standard_rational_function_field(QQ)
        Rational function field in xx over Rational Field
        as standard rational function field

    """
    if isinstance(k, StandardField):
        assert k.is_finite() or k.is_number_field()
        k = k.standard_model()
    else:
        k = standard_field(k).standard_model()
    F = FunctionField(k, var_name)
    return StandardFunctionField(F)


def standard_function_field(K, k=None):
    r""" Return the standard model of this function field.

    INPUT:

    - ``K`` -- a function field
    - ``k`` -- a subfield of `K`, or ``None`` (default: ``None``)

    Alternatively, the function field `K` can also be given as an irreducible
    bivariate polynomial `f` over a finite field or a number field `k`.
    In this case, we set `K:=k(x,y \mid f(x,y)=0)`.

    The subfield `k` may be given either as a field with a natural
    coercion into `K`, or as an embedding of fields `\phi:k\to K`.

    OUTPUT:

    the object representing the function field `K/k` and its normal model.

    .. NOTE::

        At the moment, a standard model may be an extension of `k(x)` of degree
        one; in this case, it would be better to replace it with `k(x)` itself.


    EXAMPLES:

        sage: from mclf import *
        sage: k0 = GF(2)
        sage: R.<t> = k0[]
        sage: k.<a> = k0.extension(t^2+t+1)
        sage: F0.<x> = FunctionField(k0)
        sage: S.<y> = F0[]
        sage: F.<y> = F0.extension(y^2+y+1)
        sage: phi = k.hom([y], F)
        sage: F = standard_function_field(F, phi); F
        Function field in y defined by y^2 + y + 1, as a standard field

    The standard model of `F` is a simple extension of `k(x)` of degree one.::

        sage: F.standard_model()
        Function field in y defined by y + a

    Actually, the standard model should be `k(x)``!

        sage: F.generators()
        (x, y)
        sage: F.polynomial()
        y + a
        sage: F.minimal_polynomial(y+x)
        T + x + a

    """

    from sage.categories.fields import Fields

    if K not in Fields:
        # we assume that K is a bivariate polynomial
        f = K
        A = f.parent()
        K0 = FunctionField(A.base_ring(), A.variable_names()[0])
        R = PolynomialRing(K0, A.variable_names()[1])
        G = R(f(K0.gen(), R.gen()))
        assert G.degree() > 0, "the polynomial f must have positive degree in y"
        assert G.is_irreducible(), "the polynomial F must be irreducible"
        K = K0.extension(G.monic(), A.variable_names()[1])
    F = StandardFunctionField(K)
    if k is None or k is F.constant_base_field():
        return F
    elif k in Fields and k.is_subring(F.constant_base_field()):
        #
        return F.with_smaller_constant_base_field(k)
    elif k in Fields and k.is_subring(F.original_model()):
        k = k.hom(F.original_model()).post_compose(F.from_original_model())
    elif hasattr(k, "domain"):
        pass
    else:
        raise ValueError("k is not of the right form")
    # now k is given by an embedding k-->K
    # we define u as the composition u:k->K->F
    u = k.post_compose(F.from_original_model())
    k1, k1_to_k, k_to_k1 = common_subfield(u)
    F1 = F.with_smaller_constant_base_field(k1)
    return F1.base_change(k1_to_k, u)[0]


class StandardField(SageObject):

    def original_model(self):
        r""" Return the *original model* of this standard field.

        This is the field from which this standard field was originally
        constructed.

        """
        return self._original_model

    def underlying_field(self):
        r""" Return the field underlying this object.

        .. NOTE::

            This method has changed and now returns the *standard model*
            of this field, not the *original model*. It is kept mainly for
            backward compatibility, but its use should be replaced by the
            method :meth:`standard_model`.

        """
        return self._standard_model

    def is_finite(self):
        r""" Return whether this is a finite field.

        This method must be implemented by the appropriate subclass.

        """
        raise NotImplementedError()

    def is_number_field(self):
        r""" Return whether this is a number field.

        This method must be implemented by the appropriate subclass.

        """
        raise NotImplementedError()

    def is_function_field(self):
        r""" Return whether this is a function field.

        This method must be implemented by the appropriate subclass.

        """
        raise NotImplementedError()

    def characteristic(self):
        r""" Return the characteristic of this standard field.

        """
        return self.standard_model().characteristic()

    def cardinality(self):
        r""" Return the cardinality of this standard field.

        """
        return self.standard_model().cardinality()

    def is_prime_field(self):
        r""" Return whether this standard field is a prime field,
        i.e. either the field of rational numbers, or a field with `p`
        elements, for a prime `p`.

        """
        return self.standard_model().is_prime_field()

    def standard_model(self):
        r""" Return the standard model of this field.

        The *standard model* of a standard field `K` is a field `K'`,
        isomorphic to `K`, whose internal representation is of the following
        form:

        - the field ``GF(q)``, where `q` is the cardinality of `K`,
          if `K` is finite,
        - an absolute number field, i.e. a simple extension of `\mathbb{Q}`,
          if `K` is a number field,
        - a finite, simple and separable extension of a rational function field
          `k(x)`, where `k` is the constant base field of `K`.

        """
        return self._standard_model

    def from_original_model(self):
        r""" Return the distinguished isomorphism from the original model of
        this field to its standard model.

        """
        return self._from_original_model

    def to_original_model(self):
        r""" Return the distinguished isomorphism from the standard model
        of this field to its original model.

        """
        return self._to_original_model

    def __call__(self, a):
        r""" coerce an element into this field.

        INPUT:

        - ``a`` -- a field element, either from the original model, or
                   coercible into the standard model

        OUTPUT:

        If `a` is an element of the original model, then we return in image
        in the standard model. Otherwise, we try to coerce `a` into the
        standard model.

        """
        if a.parent().is_subring(self.original_model()):
            return self.from_original_model()(a)
        else:
            return self.standard_model()(a)

    def polynomial_generator(self, var_name):
        r""" Return the generator of a univariate  polynomial ring
        over this field.

        INPUT:

        - ``var_name`` -- an alphanumeric string

        OUTPUT:

        the generator of the univariate polynomial ring over this field with
        the given variable name.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: K.polynomial_generator("x")
            x

        """
        from sage.all import PolynomialRing
        R = PolynomialRing(self.standard_model(), var_name)
        return R.gen()

    def polynomial_generators(self, var_names):
        r""" Return generators of a polynomial ring over this field.

        INPUT:

        - ``varnames`` -- a list of alphanumeric strings

        OUTPUT:

        the list of generators of the polynomial ring over this field with
        the given variable names.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: K.polynomial_generators(["x", "y"])
            (x, y)

        """
        from sage.all import PolynomialRing
        R = PolynomialRing(self.standard_model(), var_names)
        return R.gens()

    def change_coefficients(self, f):
        r""" Return the base change of a polynomial to this standard field.

        INPUT:

        - ``f`` -- a polynomial over a subring of this field

        OUTPUT:

        the base change of `f` to this standard field.

        This means that the base ring of the returned polynomial is the
        standard model of this standard field.

        """
        return f.map_coefficients(self, self.standard_model())

    def roots(self, f):
        r""" Return the roots of a polynomial over this standard field.

        INPUT:

        - ``f`` -- a univariate nonzero polynomial over this standard field

        OUTPUT:

        The list of of roots of `f` (in this standard field).

        """
        assert not f.is_zero(), "f must not be zero"
        if f.degree() == 0:
            return []
        f = self.change_coefficients(f)
        if self.is_function_field() and not self.is_rational_function_field():
            from mclf.standard_fields.factor_polynomial_over_function_field \
                import roots_of_polynomial_over_function_field
            roots_of_f = roots_of_polynomial_over_function_field(
                self.standard_model(), f)
        else:
            roots_of_f = [alpha for alpha, _ in f.roots()]
        return roots_of_f

    def prime_factors(self, f):
        r""" Return the list of irreducible factors of a polynomial.

        INPUT:

        - ``f`` -- a univariate polynomial over a subring of this field.

        OUTPUT:

        The list of monic irreducible factors of the base change of `f`
        to this standard field.

        """
        f = self.change_coefficients(f)
        return [g for g, _ in f.factor()]

    def extension(self, f):
        r""" Return the finite extension of this field given by an irreducible
        polynomial.

        INPUT:

        - ``f`` -- an irreducible univariate polynomial over this field.

        OUTPUT:

        The finite simple extension `L/K` given by `f`. This is an object of
        :class:`StandardFiniteFieldExtension`


        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: x = K.polynomial_generator("alpha")
            sage: K.extension(x^2+2)
            Number Field in alpha with defining polynomial alpha^2 + 2
            as a standard field

        """
        # we make sure the base ring of f is the standard model
        if f.base_ring() is self.original_model():
            f = f.map_coefficients(self.from_original_model(),
                                   self.standard_model())
        else:
            f = f.change_ring(self.standard_model())

        # for the moment, we avoid this test because factoring may not be
        # implemented for the base field of f:
        # assert len(f.factor()) == 1, "f must be irreducible"
        from mclf.standard_fields.finite_field_extensions import (
            finite_field_extension)
        return finite_field_extension(self, f)

    def inclusion(self, L):
        r""" Return the inclusion of this standard field into `L`.

        INPUT:

        ``L`` -- another standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this standard field `K` into
        `L`, provided there is one. If not, an error is raised.

        This must be realized by the subclass.

        """
        print("K = ", self)
        print("parent: ", self.parent())
        print("L = ", L)
        raise NotImplementedError()


class StandardFiniteField(StandardField):

    def __init__(self, K):

        # if K is already an instance of StandardField, we simply
        # make a copy
        if isinstance(K, StandardFiniteField):
            self._original_model = K._original_model
            self._standard_model = K._standard_model
            self._from_original_model = K._from_original_model
            self._to_original_model = K._to_original_model
            self._generator = K._generator
            self._polynomial = K._polynomial
        else:
            from sage.categories.rings import Rings
            assert K in Rings and K.is_field(), "K must be a field"
            assert K.is_finite(), "K must be a finite field"
            self._original_model = K
            # compute the normal form of K
            # for finite field, our normal form is created with GF(q)
            # GF's docstring warns that creating a finite field like this,
            # without giving a variable name comes with a speed penalty for
            # large finite fields. We accept this since we mainly work with
            # small finite fields
            from sage.all import GF
            Ks = GF(K.cardinality())
            zs = Ks.gen()
            f = zs.minpoly()
            assert f(zs).is_zero()
            z = f.roots(K)[0][0]
            Ks_to_K = Ks.hom([z])
            K_to_Ks = inverse_of_field_isomorphism(Ks_to_K)
            self._standard_model = Ks
            self._from_original_model = K_to_Ks
            self._to_original_model = Ks_to_K
            self._generator = K_to_Ks(z)
            self._polynomial = f

    def _repr_(self):
        if self.is_prime_field():
            return "the standard field with {} elements".format(
                self.characteristic())
        else:
            return "{} as a standard field".format(self.standard_model())

    def is_finite(self):
        r""" Return whether this is a finite field.

        """
        return True

    def is_number_field(self):
        r""" Return whether this is a number field.

        """
        return False

    def is_function_field(self):
        r""" Return whether this is a function field.

        """
        return False

    def generator(self):
        r""" Return the standard generator of this finite field.

        """
        return self._generator

    def generators(self):
        r""" Return the standard generators of this finite field.

        Since there is only one generator, we return a tuple with one element.

        """
        return (self._generator, )

    def polynomial(self):
        r""" Return the minimal polynomial of the standard generator over the
        prime field.

        """
        return self._polynomial

    def as_polynomial(self, a):
        r""" Return the polynomial representing the field element `a`.

        INPUT:

        - ``a`` -- an element of this finite field `K`

        OUTPUT:

        a polynomial `f` over the prime field of `K` such that
        `a=f(z)`, where `z` is the standard generator of `K`.

        """
        return self(a).polynomial()

    def hom(self, L, *a):
        r""" Return a homomorphism from this finite field to another standard
        field.

        INPUT:

        - ``L`` -- a standard field
        - ``a`` -- an element of `L` (optional)

        OUTPUT:

        The embedding `\phi:K\to L` sending the standard generator of `K`
        to `a`. If no such embedding exists, an error is raised.

        If `a` is not given, there must be a canonical embedding of `K`
        into `L`. If not, an error is raised.

        The result is an instance of the class :class:`EmbeddingOfFiniteField`.
        """
        if not isinstance(L, StandardField):
            assert is_standard_field(L), "L must be a standard field"
            L = standard_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if len(a) == 0:
            assert self.standard_model().is_subring(L.standard_model())
            a = L(self.generator())
        elif len(a) == 1:
            a = a[0]
        else:
            raise ValueError("wrong number of arguments")
        return EmbeddingOfFiniteField(self, L, a)

    def inclusion(self, L):
        r""" Return the inclusion of this finite field into `L`.

        INPUT:

        ``L`` -- a standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this finite field `K` into
        `L`, provided there is one. If not, an error is raised.

        EXAMPLES:

            sage: from mclf import *
            sage: K = standard_field(GF(4))
            sage: L = standard_field(GF(16))
            sage: K.inclusion(L)
            the embedding of Finite Field in z2 of size 2^2 into Finite Field
            in z4 of size 2^4, sending z2 to z4^2 + z4

        """
        if not isinstance(L, StandardField):
            L = standard_field(L)
        assert self.standard_model().is_subring(L.standard_model())
        phi = self.standard_model().hom(L.standard_model())
        return self.hom(L, phi(self.generator()))


class StandardNumberField(StandardField):

    def __init__(self, K):
        # if K is already an instance of StandardField, we simply
        # make a copy
        if isinstance(K, StandardNumberField):
            self._original_model = K._original_model
            self._standard_model = K._standard_model
            self._from_original_model = K._from_original_model
            self._to_original_model = K._to_original_model
            self._generator = K._generator
            self._polynomial = K._polynomial
        else:
            from sage.all import QQ
            from sage.categories.number_fields import NumberFields
            assert K in NumberFields, "K must be a number field"
            self._original_model = K
            # compute the normal form of K
            if K is QQ:
                self._standard_model = K
                self._from_original_model = identity_map(K)
                self._to_original_model = identity_map(K)
                self._generator = K.one()
                R = PolynomialRing(K, "T")
                self._polynomial = R.gen() - K.one()
            elif K.is_absolute():
                self._standard_model = K
                self._from_original_model = identity_map(K)
                self._to_original_model = identity_map(K)
                self._generator = K.gen()
                self._polynomial = K.polynomial()
            else:
                Ka = K.absolute_field(K.variable_name())
                Ka_to_K, K_to_Ka = Ka.structure()
                self._standard_model = Ka
                self._from_original_model = K_to_Ka
                self._to_original_model = Ka_to_K
                self._generator = Ka_to_K(Ka.gen())
                self._polynomial = Ka.polynomial()

    def _repr_(self):
        return "{} as a standard field".format(self.standard_model())

    def is_finite(self):
        r""" Return whether this is a finite field.

        """
        return False

    def is_number_field(self):
        r""" Return whether this is a number field.

        """
        return True

    def is_function_field(self):
        r""" Return whether this is a function field.

        """
        return True

    def generator(self):
        r""" Return the standard generator of this number field.

        """
        return self._generator

    def generators(self):
        r""" Return the standard generators of this number field.

        Since there is only one generator, we return a list with one element.

        """
        return [self._generator]

    def polynomial(self):
        r""" Return the minimal polynomial of the standard generator over the
        prime field.

        """
        return self._polynomial

    def as_polynomial(self, a):
        r""" Return the polynomial representing the field element `a`.

        INPUT:

        - ``a`` -- an element of this number field `K`

        OUTPUT:

        a polynomial `f` over `\mathbb{Q}` such that
        `a=f(z)`, where `z` is the standard generator of `K`.

        """
        if self.is_prime_field():
            R = PolynomialRing(self.standard_model(), "T")
            return R(a)
        else:
            return self(a).polynomial()

    def hom(self, L, *a):
        r""" Return a homomorphism from this number field to another standard
        field.

        INPUT:

        - ``L`` -- a standard field
        - ``a`` -- an element of `L` (optional)

        OUTPUT:

        The embedding `\phi:K\to L` sending the standard generator of `K`
        to `a`. If no such embedding exists, an error is raised.

        If `a` is not given, there must be a canonical embedding of `K`
        into `L`. If not, an error is raised.

        The result is an instance of the class :class:`EmbeddingOfNumberField`.
        """
        if not isinstance(L, StandardField):
            assert is_standard_field(L), "L must be a standard field"
            L = standard_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if len(a) == 0:
            assert self.standard_model().is_subring(L.standard_model())
            a = L(self.generator())
        elif len(a) == 1:
            a = self(a[0])
        else:
            raise ValueError("wrong number of arguments")
        return EmbeddingOfNumberField(self, L, a)

    def inclusion(self, L):
        r""" Return the inclusion of this number field into `L`.

        INPUT:

        ``L`` -- a standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this number field `K` into
        `L`, provided there is one. If not, an error is raised.

        EXAMPLES:

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = NumberField(x^2+2, "a")
            sage: L = K.extension(x^2-K.gen(), "b")
            sage: K = standard_field(K)
            sage: K.inclusion(L)
            the embedding of Number Field in a with defining polynomial x^2 + 2
            into Number Field in b with defining polynomial x^4 + 2,
            sending a to b^2

        """
        if not isinstance(L, StandardField):
            L = standard_field(L)
        # assert self.standard_model().is_subring(L.standard_model())
        return EmbeddingOfNumberField(self, L, L(self.generator()))


class StandardFunctionField(StandardField):
    r""" A function field over a finite field or a number field.

    INPUT:

    - ``K`` -- a function field `k` whose constant base field is finite
               or a number field

    OUTPUT:

    An object representing the function field `K`.

    This means firstly that `K` is a *standard field*, i.e. has two *models*,
    the *original model* (given by the function argument ``K``) and the
    *standard model*.

    The original model is the Sage field `K` was originally constructed from;
    the standard model is a field which is isomorphic to the original field,
    but has a certain standardized form, which is a finite, simple and
    separable extension of a rational function field `k(x)`, where `k` is a
    finite field or a number field which is also in standard form.

    The subfield `k` is called the *constant base field* of `K`.

    Note that if we are given the original model `K`, the corresponding Sage
    object has a method :meth:`constant_base_field` and therefore there is
    a canonical choice for the constant base field. However, from a
    purely mathematical point, there is no natural choice for `k`.
    It is possible to choose a different constant base field with the method
    :meth:`with_new_constant_base_field`.

    """

    def __init__(self, K):

        # if K is already an instance of StandardField, we simply
        # make a copy
        if isinstance(K, StandardFunctionField):
            self._original_model = K._original_model
            self._constant_base_field = K._constant_base_field
            self._standard_model = K._standard_model
            self._from_original_model = K._from_original_model
            self._to_original_model = K._to_original_model
            self._is_rational_function_field = K._is_rational_function_field
            self._generators = K._generators
            self._polynomial = K._polynomial
            self._bivariate_polynomial = K._bivariate_polynomial
            self._rational_base_field = K._rational_base_field
        else:
            if is_standard_function_field(K):
                # take K as the standard model
                F = K
                F_to_K = identity_map(K)
                K_to_F = identity_map(K)
            else:
                F, K_to_F, F_to_K = standard_model_of_function_field(K)

            k = F.constant_base_field()
            self._original_model = K
            self._constant_base_field = k
            self._standard_model = F
            self._from_original_model = K_to_F
            self._to_original_model = F_to_K
            if F.base_field() is F:
                self._is_rational_function_field = True
                self._rational_base_field = F
                self._generators = [F_to_K(F.gen())]
            else:
                self._is_rational_function_field = False
                x = F_to_K(F.base_field().gen())
                y = F_to_K(F.gen())
                self._rational_base_field = F.base_field()
                self._polynomial = F.polynomial()
                self._bivariate_polynomial = make_bivariate(self._polynomial)
                self._generators = [x, y]

    def __repr__(self):
        if self.is_rational_function_field():
            return "{} as standard rational function field".format(
                self.standard_model())
        else:
            return "{} as standard function field".format(
                self.standard_model())

    def is_finite(self):
        r""" Return whether this is a finite field.

        """
        return False

    def is_number_field(self):
        r""" Return whether this is a number field.

        """
        return False

    def is_function_field(self):
        r""" Return whether this is a function field.

        """
        return True

    def is_rational_function_field(self):
        r""" Return whether this field is a rational function field.

        This means that the standard model of this field is of the form
        `k(x)`, where `k` is the constant base field.

        """
        return self._is_rational_function_field

    def constant_base_field(self):
        r""" Return the constant base field of this function field.

        """
        return self._constant_base_field

    def rational_base_field(self):
        r""" Return the rational base field of this  function field.

        """
        return self._rational_base_field

    def generators(self):
        r""" Return the standard generators of this function field.

        In its standard form, this function field `K/k` is of the form
        `K=k(x)[y \mid f(y)=0]`. The *standard generators* of `K/k` is the
        pair of elements `x,y\in K`.

        If `K` is a rational function field, i.e.\ its standard form is
        `k(x)`, then we only return the standard generator `x`.

        """
        return self._generators

    def generator(self):
        r""" Return the standard generator of this function field.

        OUTPUT:

        If this function field `K=k(x)` is rational, we return `x`. Otherwise,
        the standard form is `K=k(x)[y \mid f(y)=0]`, and then we return `y`.

        """
        if self.is_rational_function_field():
            return self.generators()[0]
        else:
            return self.generators()[1]

    def variable_names(self):
        r""" Return the name of the standard generators.

        """
        if self.is_rational_function_field():
            return [self.rational_base_field().variable_name()]
        else:
            return list(
                self.polynomial(bivariate=True).parent().variable_names())

    def variable_name(self):
        r""" Return the name of the standard generator of this function field.

        OUTPUT:

        If this function field `K=k(x)` is rational, we return the name of `x`.
        Otherwise, the standard form is `K=k(x)[y \mid f(y)=0]`, and then we
        return the name of `y`.

        """
        if self.is_rational_function_field():
            return self.variable_names()[0]
        else:
            return self.variable_names()[1]

    def polynomial(self, bivariate=False):
        r""" Return the minimal polynomial of the standard generator over the
        rational base field.

        This is the irreducible, monic and univariate polynomial `f` over the
        rational function field `k(x)` such that the standard form of this
        function field is `F = k(x)[y\mid f(y)=0]`.

        If `K` is a rational function field, then an error is raised.

        If ``bivariate`` is ``True`` an irreducible bivariate polynomial
        `g` is returned such that `g(x,y)=0`.

        """
        if self.is_rational_function_field():
            raise AssertionError("K is a rational function field")
        if bivariate:
            return self._bivariate_polynomial
        else:
            return self._polynomial

    def as_polynomial(self, f, bivariate=False):
        r""" Return the polynomial representing the field element `f`.

        INPUT:

        - ``f`` -- an element of this function field `K`
        - ``bivariate`` -- a boolean (default: ``False``)

        OUTPUT:

        a polynomial `\tilde{f}` over the rational base field `k(x)` of `K`
        such that `f=\tilde{f}(y)`, where `y` is the standard generator of `K`
        over `k(x)`.

        If `K=k(x)` is a rational function field then we simply return `f`,
        which we may consider as a constant polynomial.

        """
        if self.is_rational_function_field():
            # we consider f as a constant polynomial
            return self(f)
        else:
            R = self.polynomial().parent()
            ft = R(self.from_original_model()(f).list())
            if bivariate:
                ft = make_bivariate(ft)
            return ft

    def as_rational_function(self, f):
        r""" Return the representation of `f` as a bivariate rational function.

        INPUT:

        - ``f`` -- an element of this function field `K`

        OUTPUT:

        a pair `(g, h)` of bivariate polynomials over the constant base field
        `k` of `K` such that `f=g(x,y)/h(x,y)`, where `x, y` are the standard
        generators of `K` over `k`.

        If `K=k(x)` is a rational function field then `g,h` are univariate
        polynomials such that `f=g(x)/h(x)`, where `x` is the standard
        generator of `K/k`.

        EXAMPLES::

            sage: from mclf import *
            sage: K0.<x> = FunctionField(QQ)
            sage: R.<y> = K0[]
            sage: K.<y> = K0.extension(y^2-x^3-1)
            sage: K = standard_field(K)
            sage: K.as_rational_function(x+y/x)
            (x^2 + y, x)

        """
        if self.is_rational_function_field():
            f = self(f)
            return (f.numerator(), f.denominator())
        else:
            f = self.as_polynomial(f)
            # now f is a polynomial over the rational function field k(x)
            R = f.parent()
            K0 = R.base_ring()
            k = K0.constant_base_field()
            A = PolynomialRing(k, [K0.variable_name(), R.variable_name()])
            x, y = A.gens()
            h = lcm([f[i].denominator() for i in range(f.degree() + 1)])
            f = h*f
            g = sum(f[i].numerator()(x)*y**i for i in range(f.degree() + 1))
            return (g, h(x))

    def is_constant(self, a):
        r""" Return whether the element `a` is a constant element
        of this function field.

        By definition, `a` is a constant element of the function field `F/k`
        if `a` is algebraic over the constant base field `k`.

        """
        # the element is constant if and only if the minimal polynomial of a
        # over the rational base field k(x) is constant, i.e has coefficients
        # in k
        f = self.minimal_polynomial(a)

        def rational_function_is_constant(g):
            return (g.numerator().degree() == 1
                    and g.denominator().degree() == 1)

        return all(rational_function_is_constant(f[i])
                   for i in range(f.degree()+1))

    def is_transcendential(self, t):
        r""" Return whether this element is transcendental over the constant
        base field.


        """
        return not self.is_constant()

    def minimal_polynomial(self, t, var_name="T"):
        r""" Return the minimal polynomial of this element over the base field.

        INPUT:

        - `t` -- an element of this function field `F`

        OUTPUT:

        The minimal polynomial of `t` over the base field `k(x)` of `F`.

        Note that the base field `k(x)` is a subfield of the standard model of
        this function field, which may not be a subfield of `F` itself.

        """
        return self(t).minpoly(var_name)

    def norm(self, t):
        r""" Return the norm of this element over the base field.

        INPUT:

        - `t` -- an element of this function field `F`

        OUTPUT:

        The norm of `t` over the base field `k(x)` of `F`.

        Note that the base field `k(x)` is a subfield of the standard model of
        this function field, which may not be a subfield of `F` itself.

        """
        return self(t).norm()

    def field_of_constants(self):
        r""" Return the field of constants of this function field.

        Let `F/k` be this function field, with constant base field `k`.
        The *field of constants* is the algebraic closure `k_1` of `k` in `F`.
        It is easy to see that `k_1/k` is a finite simple extension.

        OUTPUT:

        a pair `(k_1,\iota)`, where `k_1/k` is a finite simple extension and
        `\iota:k_1\to F` is a `k`-linear embedding whose image is the
        field of constants of `F/k`.

        """
        raise NotImplementedError()

    def field_of_constants_degree(self):
        r""" Return the degree of the field of constants
        of this function field.

        Let `F/k` be this function field, with constant base field `k`.
        The *field of constants* is the algebraic closure `k_1` of `k` in `F`.
        It is easy to see that `k_1/k` is a finite simple extension.

        OUTPUT:

        the degree `[k_1:k]`.

        """
        raise NotImplementedError()

    def algebraic_relation(self, x, y):
        r""" Return an algebraic relation between two elements of this
        function field.

        INPUT:

        - ``x``, ``y`` -- two elements of this function field `F/k`,

        OUTPUT:

        an irreducible bivariate polynomial `f` over `k` such that
        `f(x,y)=0`.

        EXAMPLES::

            sage: from mclf import *
            sage: K0.<x> = FunctionField(GF(2))
            sage: R.<y> = K0[]
            sage: K.<y> = K0.extension(y^2+x^3+1)
            sage: algebraic_relation(K, x, y)
            x^3 + y^2 + 1
            sage: S.<z> = K[]
            sage: L.<z> = K.extension(z^2+z+x+y)
            sage: algebraic_relation(L, z+1, y)
            x^6 + x^5 + x^4*y + x^4 + x^2*y^2 + x^3 + x^2*y + x*y^2 + y^3 + y^2 + 1

        """
        K = self
        K0 = K.rational_base_field()
        k = K0.constant_base_field()
        f = minimal_polynomial(x, K0)
        g = minimal_polynomial(y, K0)
        A = PolynomialRing(k, "X, Y, T")
        X, Y, T = A.gens()
        F = make_bivariate(f)(T, X)
        G = make_bivariate(g)(T, Y)
        B = PolynomialRing(k, "x, y")
        X, Y = B.gens()
        h = F.resultant(G, T)(X, Y, 0).radical()
        assert len(h.factor()) == 1, "h should be irreducible!?"
        assert h(x, y).is_zero()
        return h

    def hom(self, L, image_of_gens, *args):
        r""" Return a homomorphism from this function field to another function
        field.

        INPUT:

        - ``L`` -- a standard function field
        - ``image_of_gens`` -- a list of elements of `L`
        - ``phi0`` -- an embedding of a subfield of `K` into `L` (optional)

        1. If `K` is a rational function field, then ``image_gens`` must
        contain exactly one element, and the domain of `\psi_0:k\to L` must be
        the constant base field of `K`.

        2. Otherwise, ``image_gens`` may contain one or two elements. In the
        first case, the domain of `\psi_0` must be the rational base field of
        `L`, in the second case it must be the constant base field.

        If `\psi_0` is not given, we assume that there is a natural embedding
        of `k` into `L`, which we then call `\psi_0`.

        OUTPUT:

        The embedding `\phi:K\to L` extending `\phi_0` and sending the standard
        generators of `K` to the elements of specified by ``image_of_gens``
        (and possibly `\psi_0`). More precisely, if `x` resp. `x, y` are the
        standard generators of `K`, and `u` resp. `u, v` are the elements of
        ``image_of_gens``, then

        1. We have `\phi(x)=u` if `K=k(x)` is a rational function field,
        2. We have `\phi(x)=u` and `\phi(y)=v` if `K` is not a rational
           function field and `u, v` are given,
        3. We have `phi=psi_0` on `k(x)` and `phi(y)=u` otherwise.

        If no such embedding exists, an error is raised.

        If `\phi_0` is not given, we assume that we are in Case 1 or 2, and
        that there is a canonical embedding of the constant base field `k`
        into `L`.  If not, an error is raised.

        The result is an instance of :class:`EmbeddingOfFunctionField`.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(FunctionField(QQ, "x"))
            sage: x = K.generator()
            sage: phi = K.hom(K, [x^2 + x]); phi
            the embedding of Rational function field in x over Rational Field
            as standard rational function field into Rational function field
            in x over Rational Field as standard rational function field,
            sending x to (x^2 + x,)
            sage: phi(x^3)
            x^6 + 3*x^5 + 3*x^4 + x^3

            sage: y = K.polynomial_generator("y")
            sage: K.extension(y^2 + x^3 +1)
            Function field in y1 defined by y1^2 + x^3 + 1,
            as finite extension of Rational function field in x over
            Rational Field

        """
        K = self
        K0 = K.rational_base_field()
        k = K.constant_base_field()
        if not isinstance(L, StandardFunctionField):
            L = standard_function_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if len(args) == 0:
            assert k.is_subring(L.standard_model())
            phi0 = k.hom(L.standard_model())
            if len(image_of_gens) == 1:
                assert K.is_rational_function_field(), "wrong input"
        elif len(args) == 1 and len(image_of_gens) == 1:
            phi0 = args[0]
            assert phi0.codomain().is_subring(L.standard_model())
            if not K.is_rational_function_field():
                image_of_gens = [phi0(K0.gen())] + image_of_gens
        elif len(args) == 1 and len(image_of_gens) == 2:
            phi0 = args[0]
            assert k.is_subring(phi0.domain())
        else:
            raise ValueError("wrong type of arguments")
        return EmbeddingOfFunctionField(self, L, image_of_gens, phi0)

    def with_smaller_constant_base_field(self, k0):
        r""" Return this standard function field as a function field
        with smaller constant base field.

        INPUT:

        - ``k0`` -- a subfield of the constant base field `k` of this `F`

        OUTPUT:

        a tripel `(F_0, t, s)`, where

        - `F_0` is a standard function field with constant base field `k_0`
        - `t:F\to F_0` is an isomorphism inducing the identity on `k_0`
        - `s:F_0\to F` is the inverse of `t`

        .. WARNING::

            The resulting standard function field has in general a different
            original model! This may lead to problems and should be changed
            at some point.

        .. TODO::

            Make sure the resulting standard function field has the same
            original model.

        EXAMPLES::

            sage: from mclf import *
            sage: A.<x,y> = GF(4)[]
            sage: F = standard_function_field(y^2+x^3+1)
            sage: F.with_smaller_constant_base_field(GF(2))

        """
        from mclf.standard_fields.finite_field_extensions import (
            finite_field_extension)
        F = self
        Fb = F.rational_base_field()
        k = F.constant_base_field()

        # the new cbf is a subfield of k; we need an equation for the
        # relative extensin k/k_0
        k_k0 = finite_field_extension(k0.hom(k))
        print("k_k0 = ", k_k0)
        f = k_k0.relative_polynomial()
        print("f = ", f)
        alpha = k_k0.relative_generator()

        F00 = standard_rational_function_field(k0)
        F01 = F00.extension(f)

        # now F01 is isomorphic to Fb; we construct the isomorphism
        # in two steps
        F00_to_Fb = F00.hom(Fb, [Fb.gen()], k_k0.embedding())
        F01_to_Fb = F01.relative_hom(Fb, alpha, F00_to_Fb)

        # now we need the inverse isomorphism
        k_to_F01 = k_k0.relative_hom(F01, F01.relative_generator())
        Fb_to_F01 = homomorphism_on_standard_field(
            Fb, F01, F00.generator(), k_to_F01)
        Fb_to_F01 = embedding_of_standard_fields(Fb_to_F01)

        # finally, we construct the new ff F0 as an extension of F01,
        # isomorphic to F/Fb
        G = F.polynomial()
        G_F01 = G.map_coefficients(Fb_to_F01, F01.standard_model())
        F0 = F01.extension(G_F01)
        F0_to_F = F0.relative_hom(F, F.generator(), F01_to_Fb)
        try:
            Fb_to_F0 = Fb_to_F01.post_compose(F0.embedding())
        except ValueError:
            print()
            print("Fb_to_F01 = ", Fb_to_F01)
            print()
            print("F0.embedding() = ", F0.embedding())
            print()
            raise AssertionError()

        F_to_F0 = F.hom(F0, [F0.generator()], Fb_to_F0)
        return F0, F0_to_F, F_to_F0

    def base_change(self, phi, u=None):
        r""" Return the base change of this function field via `\phi`.

        INPUT:

        - ``phi`` -- a field embedding `\phi:k\to K`, where k is the
                     constant base field of this function field `F`, and
                     `K/k` is a finite field extension
        - ``u`` -- a `k`-linear embedding `u:K\to F`, or ``None``
                   (default: ``None``)

        OUTPUT:

        A list of  pairs `(F_K, s)` where `F_K/K` is a standard
        function field and `s:F\to F_K` is an embedding extending `\phi`.

        The fields `F_K` are the irreducible factors of the finite
        `K`-algebra

        .. MATH::

                F\otimes_k K.

        If `u:K\to F` is given, then instead we return a tripel
        `(F_K, s, t)` where `t:F\to F_K` is a `k`-linear isomorphism and
        `t:F_K\to F` is the inverse of `s`, such that `t` extends `u`.
        Note that this triple exists and is uniquely determined by `u`.

        .. WARNING::

            The resulting standard function field has in general a different
            original model! This may lead to problems and should be changed
            at some point.

        .. TODO::

            Make sure the resulting standard function field has the same
            original model.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_field(GF(3))
            sage: x, y = k.polynomial_generators(["x", "y"])
            sage: F = standard_function_field(x^2 + y^2)
            sage: t = k.polynomial_generator("t")
            sage: K = k.extension(t^2 + 1)
            sage: phi = k.hom(K)
            sage: F.base_change(phi)[0][0]
            Function field in y defined by y + t*x as standard function field

            sage: x = F.generators()[0]
            sage: y = F.generators()[1]
            sage: u = K.hom(F, [x/y - 1])
            sage: F.base_change(phi, u)[0]
            Function field in y defined by y + 2*t*x as standard function field

        """
        from sage.all import FunctionField
        F = self
        k = F.constant_base_field()
        assert phi.domain() is k, "the domain of phi\
            has to be the constant base field of F"
        K = phi.codomain()
        if F.is_rational_function_field():
            raise NotImplementedError()
        else:
            F0 = F.rational_base_field()
            f = F.polynomial()
            # f should be an irreducible polynomial over F0
            F0_K = standard_field(FunctionField(K, F0.variable_name()))
            psi = standard_field(F0).hom(F0_K, F0_K.generators(), phi)
            f_K = f.map_coefficients(psi, F0_K.underlying_field())
            if u is None:
                ret = []
                for g, _ in f_K.factor():
                    F_K = F0_K.extension(g)
                    ret.append((F_K, F.hom(F_K, F_K.generators(), phi)))
                return ret
            else:
                ut = F0_K.hom(F, [F(F0.gen())], u)
                for g, _ in f_K.factor():
                    g_F = g.map_coefficients(ut, F.underlying_field())
                    if g_F(F.generator()).is_zero():
                        F_K = F0_K.extension(g)
                        F_to_F_K = F.hom(F_K, F_K.generators(), phi)
                        F_K_to_F = F_K.hom(F, F.generators(), u)
                        return F_K, F_to_F_K, F_K_to_F
                # if we get here, something is wrong
                raise AssertionError("couldn't fing the right factor")

    def inclusion(self, L):
        r""" Return the inclusion of this function field into `L`.

        INPUT:

        ``L`` -- a standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this number field `K` into
        `L`, provided there is one. If not, an error is raised.

        EXAMPLES:

            sage: from mclf import *
            sage: F0.<x> = FunctionField(QQ)
            sage: R.<y> = F0[]
            sage: F = F0.extension(y^2-x^3-1, "y")
            sage: F0 = standard_field(F0)
            sage: F0.inclusion(F)
            the embedding of Rational function field in x over Rational Field
            into Function field in y defined by y^2 - x^3 - 1,
            sending [x] to [x]

        """
        if not isinstance(L, StandardField):
            L = standard_field(L)
        k = self.constant_base_field()
        phi0 = k.hom(L.constant_base_field())
        image_of_gens = [L(a) for a in self.generators()]
        return EmbeddingOfFunctionField(self, L, image_of_gens, phi0)


# ---------------------------------------------------------------------------


def embedding_of_standard_fields(*args):
    r""" Return the embedding of standard fields defined by the input.

    INPUT:

    the input tuple ``args`` can be of the following form:

    - ``phi`` -- a morphism of fields  `\phi:K\to L`
    - `(K, L, \phi)` -- `K` and `L` are fields and `\phi` is a morphism of
                        fields defined on an overfield of `K` such that
                        `\phi(K)` is contained in `L`

    Here `K` and `L` must be Sage fields, and `\phi` a Sage morphism.

    EXAMPLES::

        sage: from mclf import *
        sage: k0 = GF(4)
        sage: R.<x> = k0[]
        sage: k1.<a> = k0.extension(x^3+x+1)
        sage: phi = k0.hom(k1)
        sage: embedding_of_standard_fields(phi)
        the embedding of Finite Field in z2 of size 2^2 as a standard field
        into Univariate Quotient Polynomial Ring in a over Finite Field in z2
        of size 2^2 with modulus a^3 + a + 1 as a standard field, sending z2 to
        z2
        sage: embedding_of_standard_fields(GF(2), k0, phi)
        the embedding of the field with 2 elements, as a standard field into
        Finite Field in z2 of size 2^2 as a standard field, sending 1 to 1

    """
    if len(args) == 1:
        phi = args[0]
        K = standard_field(phi.domain())
        L = standard_field(phi.codomain())
    elif len(args) == 3:
        K = standard_field(args[0])
        L = standard_field(args[1])
        phi = args[2]
    else:
        raise ValueError("input doesn't have the right form")

    if K.is_finite():
        return EmbeddingOfFiniteField(K, L, phi(K.generator()))
    elif K.is_number_field():
        return EmbeddingOfNumberField(K, L, phi(K.generator()))
    elif K.is_function_field():
        phi0 = embedding_of_standard_fields(
            K.constant_base_field(), L.standard_model(), phi)
        if K.is_rational_function_field():
            x = phi(K.generator())
            return EmbeddingOfFunctionField(K, L, [x], phi0)
        else:
            x = phi(K.generators()[0])
            y = phi(K.generators()[1])
            return EmbeddingOfFunctionField(K, L, [x, y], phi0)
    else:
        raise NotImplementedError()


class EmbeddingOfStandardFields(SageObject):
    r""" Base class for an embedding `\phi:K\to L` of standard fields.

    The domain `K` and the codomain `L` may be either a Sage field, i.e.
    objects of the the Sage category ``Fields``, or instance of the class
    :class:`StandardField`. In the formeer case, `K` and `L` must be in
    standard form.

    """

    def domain(self):
        r""" Return the domain of this embedding.

        The returned value is a field in standard form.

        """
        return self._domain.standard_model()

    def base_field(self):
        return self._domain

    def codomain(self):
        r""" Return the codomain of this embedding.

        The returned value is a field in standard form.

        """
        return self._codomain.standard_model()

    def extension_field(self):
        return self._codomain

    def prime_field(self):
        r""" Return the common prime field of domain and codomain of this
        embedding.

        """
        return self.domain().prime_field()

    def precompose(self, psi):
        r""" Return the composition of `\psi` with this embedding.

        INPUT:

        - ``psi`` -- an embedding `\psi:M\to K` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\phi\circ\psi:M\to L`.

        """
        return psi.post_compose(self)

    def is_standard_simple_extension(self):
        r""" Return whether this embedding is the standard form of a finite
        simple extension.

        A positive means that the original model `M` of the extension field
        `L` of this embedding `\phi:K\to L` is a finite simple extension of
        `K`.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K.<alpha> = NumberField(x^2+2)
            sage: phi = embedding_of_standard_fields(QQ.hom(K))
            sage: phi.is_standard_simple_extension()
            True

        """
        K = self.domain()           # this is the base field as a bare field
        L = self.extension_field()
        M = L.original_model()
        return (hasattr(M, "base_field") and hasattr(M, "polynomial") and
                M.base_field() is K)

    # the following methods have to be implemented by the appropriate subclass

    def __call__(self):
        raise NotImplementedError()

    def post_compose(self, psi):
        raise NotImplementedError()

    def inverse(self):
        raise NotImplementedError()

    def is_finite(self):
        raise NotImplementedError()

    def finite_extension(self):
        raise NotImplementedError()

    def common_subfield(self):
        r""" Return a common subfield of the domain and codomain
        of this embedding.

        .. TODO::

            Provide a precise description of the desired result.
            It is used in
            `standard_model_of_finite_extension_of_function_fields`,
            so maybe we only need it for function fields.

        """
        raise NotImplementedError()


class EmbeddingOfFiniteField(EmbeddingOfStandardFields):
    r""" Return an embedding of a finite field into another field.

    INPUT:

    - ``K``, ``L`` -- fields, where `K` is finite
    - ``a`` -- an element of `L`

    The fields `K,L` must be given as objects of the class
    :class:`StandardField`.

    OUTPUT:

    the unique embedding `\phi:K\to L` sending the standard generator of `K`
    to `a\in L`.

    If such an embedding does not exist, an error is raised.
    """

    def __init__(self, K, L, a):

        from sage.categories.fields import Fields
        if K in Fields:
            assert K.is_finite()
            K = standard_field(K)
            a = K(a)
        else:
            assert isinstance(K, StandardFiniteField)
        if L in Fields:
            L = standard_field(L)
        else:
            assert isinstance(L, StandardField)

        assert K.polynomial()(a).is_zero()
        self._domain = K
        self._codomain = L
        self._image_of_generator = a

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.domain().gen(),
            self.image_of_generator())

    def image_of_generator(self):
        return self._image_of_generator

    def __call__(self, a):
        r""" Return the value of this embedding on the element `a`.

        INPUT:

        - ``a`` -- an element of the domain `K` of this embedding

        If `a` is an element of the original model of `K`, we corce it into
        the standard model.

        OUTPUT:

        the element `\phi(a)\in L`, where `\phi:K\to L` is this embedding.

        """
        # this may lead to an infinite loop; is it necessary?
        # a = self(a)
        return self.base_field().as_polynomial(a)(self.image_of_generator())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`.

        """
        # assert (self.codomain().is_subring(psi.domain())), "the codomain of \
        #     self must be a subfield of the domain of psi"
        if not self.image_of_generator() in psi.domain():
            print()
            print("self = ", self)
            print("im_gen = ", self.image_of_generator())
            print()
            print("psi = ", psi)
            print()
            raise AssertionError()
        assert self.image_of_generator() in psi.domain(), (
            "im_gen = {} is no in {}".format(
                self.image_of_generator(), psi.domain()))
        a = psi(self.image_of_generator())
        return EmbeddingOfFiniteField(self._domain, psi._codomain, a)

    def inverse(self):
        r""" Return the inverse of this embedding of finite fields.

        If ``self`` is not invertible, an error is raised.

        """
        phi = self
        K = phi.base_field()
        L = phi.extension_field()
        assert K.cardinality() == L.cardinality(), (
            "the embedding is not invertible")
        alpha = L.generator()
        f = L.polynomial()
        for beta in K.roots(f):
            if phi(beta) == alpha:
                return L.hom(K, [beta])
        # if we get here, something went wrong
        raise AssertionError()


class EmbeddingOfNumberField(EmbeddingOfStandardFields):
    r""" Return an embedding of a number field into another field.

    INPUT:

    - ``K``, ``L`` -- standard fields, where `K` is a number field
    - ``a`` -- an element of `L`

    Here `K` and `L` must be either Sage fields in standard form, or instances
    of :class:`StandardField`.

    OUTPUT:

    the unique embedding `\phi:K\to L` sending the standard generator of `K`
    to `a\in L`.

    If such an embedding does not exist, an error is raised.
    """

    def __init__(self, K, L, a):
        from sage.categories.fields import Fields
        if K in Fields:
            K = standard_field(K)
        assert isinstance(K, StandardNumberField)
        if L in Fields:
            L = standard_field(L)
            a = L(a)
        assert K.polynomial()(a).is_zero()
        self._domain = K
        self._codomain = L
        self._image_of_generator = a

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.base_field().generator(),
            self.image_of_generator())

    def image_of_generator(self):
        return self._image_of_generator

    def __call__(self, a):
        r""" Return the value of this embedding on the element `a`.

        INPUT:

        - ``a`` -- an element of the domain `K` of this embedding

        OUTPUT:

        the element `\phi(a)\in L`, where `\phi:K\to L` is this embedding.

        """
        return self.base_field().as_polynomial(a)(self.image_of_generator())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of standard fields.

        Here `\phi:K\to L` is this embedding.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`.

        """
        assert self.codomain() is psi.domain(), (
            "the codomain of self and the domain of psi must be equal")
        a = psi(self.image_of_generator())
        return EmbeddingOfNumberField(self._domain, psi._codomain, a)

    def inverse(self):
        r""" Return the inverse of this embedding of number fields.

        If ``self`` is not invertible, an error is raised.

        """
        phi = self
        K = phi.base_field()
        L = phi.extension_field()
        alpha = L.generator()
        f = L.polynomial()
        for beta in K.roots(f):
            if phi(beta) == alpha:
                return L.hom(K, [beta])
        # if we get here, phi is not invertible
        raise ValueError("phi is not invertible")


class EmbeddingOfFunctionField(EmbeddingOfStandardFields):
    r""" Return an embedding of a function field into another function field.

    INPUT:

    - ``K``, ``L`` -- function fields
    - ``image_of_gens`` -- a list of elements of `L`
    - ``phi0`` -- an embedding of standard fields

    Here ``image_of_gens`` must contain exactly one element if `K` is a
    rational function field, and exactly two elements otherwise.

    It is assumed that `\phi_0:k\to l` is an embedding of the constant base
    field `k` of `K` into a subfield of `L` (which may not be equal to the
    constant base field).

    OUTPUT:

    the unique embedding `\phi:K\to L` restricting to `\phi_0` on `k` and
    sending the standard generators of `K` to the elements of
    ``image_of_gens``.

    If such an embedding does not exist, an error is raised.
    """

    def __init__(self, K, L, image_of_gens, phi0):
        from sage.categories.fields import Fields
        if K in Fields:
            K = standard_function_field(K)
        else:
            assert isinstance(K, StandardFunctionField)
        if L in Fields:
            L = standard_function_field(L)
            image_of_gens = [L(a) for a in image_of_gens]
        else:
            assert isinstance(L, StandardFunctionField)
        if isinstance(phi0, EmbeddingOfStandardFields):
            assert K.constant_base_field().is_subring(phi0.domain())
            assert phi0.codomain().is_subring(L.standard_model())
        else:
            assert phi0.domain() is K.constant_base_field()
            assert phi0.codomain().is_subring(L.standard_model())
            phi0 = embedding_of_standard_fields(phi0)

        self._domain = K
        self._codomain = L
        self._embedding_of_constant_base_field = phi0

        if K.is_rational_function_field():
            assert len(image_of_gens) == 1, "K is a rational function field,\
                so image_of_gens must have exactly one element"
            self._image_of_generators = [image_of_gens[0]]
        else:
            f = K.polynomial(bivariate=True).map_coefficients(
                phi0, L.standard_model())
            assert len(image_of_gens) == 2, "K is not a rational function\
                field, so image_of_gens must have exactly two elements"
            x = image_of_gens[0]
            y = image_of_gens[1]
            try:
                f(x, y)
            except TypeError:
                print()
                print("x = ", x)
                print("in ", x.parent())
                print("y = ", y)
                print("in ", y.parent())
                print()
                print("f = ", f)
                print("in ", f.parent())
                print()
            assert f(x, y).is_zero()
            self._image_of_generators = [x, y]

    def __repr__(self):
        return "the embedding of {} into {}, sending {} to {}".format(
            self.domain(), self.codomain(), self.base_field().generators(),
            self.image_of_generators())

    def image_of_generators(self):
        return self._image_of_generators

    def embedding_of_constant_base_field(self):
        return self._embedding_of_constant_base_field

    def __call__(self, f):
        r""" Return the value of this embedding on the element `f`.

        INPUT:

        - ``f`` -- an element of the domain `K` of this embedding

        OUTPUT:

        the element `\phi(f)\in L`, where `\phi:K\to L` is this embedding.

        """
        K = self.base_field()
        L = self.extension_field()
        phi0 = self.embedding_of_constant_base_field()
        if K.is_rational_function_field():
            f = K(f)
            num = f.numerator().map_coefficients(phi0, L.standard_model())
            denom = f.denominator().map_coefficients(phi0,
                                                     L.standard_model())
            x = self.image_of_generators()[0]
            if denom(x).is_zero():
                print("K = ", K)
                print("f = ", f)
                print("phi0 = ", phi0)
                print("x = ", x)
                print("num = ", num)
                print("denom = ", denom)
                raise AssertionError()
            return num(x)/denom(x)
        else:
            num, denom = K.as_rational_function(f)
            num = num.map_coefficients(phi0, L.standard_model())
            denom = denom.map_coefficients(phi0, L.standard_model())
            return num(self.image_of_generators())/denom(
                self.image_of_generators())

    def post_compose(self, psi):
        r""" Return the composition of this embedding with `\psi`.

        INPUT:

        - ``psi`` -- an embedding `\psi:L\to M` of function fields.

        Here `\phi:K\to L` is this embedding. The embedding `\psi` may be
        given as a Sage morphism, or as an instance of
        :class:`EmbeddingOfStandardFields`.

        OUTPUT:

        the embedding `\psi\circ\phi:K\to M`, as an instance of
        :class:`EmbeddingOfFunctionField`.

        """
        # we don't perform any explicit consistency check; the composition
        # is well defined if the following commands do not produce an error.
        tau0 = self.embedding_of_constant_base_field().post_compose(psi)
        image_of_gens = [psi(a) for a in self.image_of_generators()]
        return EmbeddingOfFunctionField(self.base_field(), psi.codomain(),
                                        image_of_gens, tau0)

    def inverse(self):
        r""" Return the inverse of this embedding of function fields.

        If ``self`` is not invertible, an error is raised.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<a> = QQ[]
            sage: k.<a> = NumberField(a^2+1)
            sage: A.<x,y> = k[]
            sage: F = standard_function_field(x^4+y^4+1)
            sage: x, y = F.generators()
            sage: phi = F.hom(F , [-a*y, a*x])
            sage: phi.inverse()

        """
        return self.inverse_on_subfield(self.codomain())

    def inverse_on_subfield(self, M):
        r""" Return a right inverse to this embedding, defined on a subfield.

        INPUT:

        - ``M`` -- a subfield of `L`, where `\phi_K\to L` is this embedding.


        OUTPUT:

        An embedding `\psi:M\to K` such that `\phi\circ\psi:M\to L`
        is the canonical embedding of the subfield `M\subset L`.

        We actually demand that `M\subset L` is a *natural subfield*. Since
        `L` is a function field, with standard model `k(x)[y\mid f(y)=0]`,
        `M` must be equal to `k`,  `L_0:=k(x)` or `L`.

        """
        phi = self
        K = phi.base_field()
        L = phi.extension_field()
        k = L.constant_base_field()
        L0 = L.rational_base_field()
        if M is k:
            # k must be GF(q) or an absolute number field
            if k.is_prime_field():
                return embedding_of_standard_fields(k.hom(K.standard_model()))
            else:
                alpha = k.gen()
                f = k.polynomial()
                for beta in K.roots(f):
                    if phi(beta) == alpha:
                        return embedding_of_standard_fields(k.hom([beta]))
                # if we get here, the partial inverse does not exist
                raise ValueError("the partial inverse does not exist")
        elif M is L0:
            psi0 = phi.inverse_on_subfield(k)
            if K.is_rational_function_field():
                x = phi(K.generator())
                g = L.as_polynomial(x)
                # we have x = g(y), where L=L0[y].
                # By assumption, x is in L0, so g must be constant
                assert g.degree() == 1, "the partial inverse does not exist"
                beta = -g[0]/g[1]
                psi = L0.hom([beta], base_map=psi0)
                assert psi(x) == K.generator(), "something went wrong!"
                return embedding_of_standard_fields(psi)
            else:
                t = L0.gen()       # we have L0=k(t)
                x = K.generator()  # we have K/k0(x)
                x1 = phi(x)
                f = L.algebraic_relation(x1, t)
                # now f(phi(x), t) = 0
                f_K = f.map_coefficients(psi0, K.standard_model())
                _, T = f_K.parent().gens()
                g = f_K(K.generator(), T).polynomial(T)
                # now g(alpha) = 0 if phi(alpha)=t
                roots_of_g = K.roots(g)
                for alpha in roots_of_g:
                    if phi(alpha) == t:
                        # we define psi:L0-->K st psi(t)=alpha
                        psi = L0.hom([alpha], psi0)
                        assert psi(x1) == K.generator(
                        ), "something went wrong!"
                        return embedding_of_standard_fields(psi)
                # if we get here, something went wrong
                raise AssertionError("could not find the correct root of g")
        elif M is L.standard_model():
            psi0 = phi.inverse_on_subfield(L0)
            alpha = L.generator()
            f = L.polynomial().map_coefficients(psi0, K.standard_model())
            roots_of_f = K.roots(f)
            for beta in roots_of_f:
                if phi(beta) == alpha:
                    return L.hom(K, [beta], psi0)
            # if we get here, the partial inverse does not exist
            raise ValueError("the partial inverse does not exist")
        else:
            raise ValueError("M is not a natural subfield of the codomain L")


# ----------------------------------------------------------------------------

#                       helper functions, new version

def standard_model_of_function_field(K):
    r""" Return a standard model of a function field.

    INPUT:

    - ``K`` -- a function field over a finite or a number field

    `K` must be an object of the category ``Fields``.

    OUTPUT:

    A triple `(F, s, t)`, where `F` is a function field in standard form,
    `s:K\to F` is an isomorphism of fields and `t:F\to K` is the inverse
    of `s`.

    EXAMPLES::

        sage: from mclf import *
        sage: k.<a> = GF(8)
        sage: K0.<x> = FunctionField(k)
        sage: R.<y> = K0[]
        sage: K1.<y> = K0.extension(y^2+x^3+a)
        sage: S.<z> = K1[]
        sage: K2.<z> = K1.extension(z^3+y+x^2+1)
        sage: F, s, t = standard_model_of_function_field(K2)
        sage: F
        Function field in z_ defined by z_^4 + z_^3 + x_^6 + z3 + 1
        sage: s(z)
        x_
        sage: t(s(z))
        z
        sage: s(t(F.gen()))
        z_

    """
    if is_standard_function_field(K):
        return K, identity_map(K), identity_map(K)
    # we first compute a simple  model of K
    F1, F1_to_K, K_to_F1 = K.simple_model()
    F10 = F1.base_field()
    k1 = F1.constant_base_field()
    f1 = F1.polynomial()
    x = F1_to_K(F10.gen())
    y = F1_to_K(F1.gen())
    # now K=k1(x,y | f1(x,y))
    # the next step is to compute the standard model k of the constant base
    # field and to make a copy F2 of F1 with this new constant base field
    k = standard_field(k1)
    k1_to_k = k.from_original_model()
    F20 = FunctionField(k.standard_model(), F10.variable_name())
    F10_to_F20 = F10.hom([F20.gen()], k1_to_k)
    f2 = f1.map_coefficients(F10_to_F20, F20)

    # we define F2, the copy of F1 with cbf k
    F2 = F20.extension(f2, F1.variable_name())
    F1_to_F2 = F1.hom([F2.gen()], F10_to_F20)
    K_to_F2 = K_to_F1.post_compose(F1_to_F2)
    F20_to_K = F20.hom([x], k.to_original_model())
    F2_to_K = F2.hom([y], F20_to_K)

    # if F2 is separable over its rational base field, we are done
    if F2.is_separable():
        return F2, K_to_F2, F2_to_K
    else:
        # compute a separable model
        F3, F3_to_F2, F2_to_F3 = F2.separable_model()
        K_to_F3 = K_to_F2.post_compose(F2_to_F3)
        F3_to_K = F3_to_F2.post_compose(F2_to_K)
        return F3, K_to_F3, F3_to_K


def inverse_of_field_isomorphism(phi):
    r""" Return the inverse of a given field isomorphism.

    INPUT:

    - ``phi`` -- a homomorphism of fields `\phi:K\to L` which is bijective

    We assume that the domain `K` is a field in standard form. In particular,
    both `K` and `L` are standard fields.

    OUTPUT:

    the homomorphism `\psi:L\to K` which is the inverse of `\phi`.

    """
    return inverse_of_field_isomorphism_on_subfield(phi, phi.codomain())


def inverse_of_field_isomorphism_on_subfield(phi, L1):
    r""" Return the restriction of the inverse of a given field isomorphism
    to a subfield.

    INPUT:

    - ``phi`` -- a homomorphism of fields `\phi:K\to L` which is bijective
    - ``L1`` -- a subfield of `L`

    OUTPUT:

    the embedding `\psi:L_1\to K` such that `\phi\circ\psi` is the natural
    inclusion `L_1\to L`.

    """
    from sage.categories.function_fields import FunctionFields
    K = phi.domain()
    L = phi.codomain()
    assert L1.is_subring(L)
    if L1.is_prime_field():
        # there is a canonical embedding of L1 into K
        return L1.hom(K)
    elif hasattr(L1, "base_field") and L1.base_field() is L1:
        # this should only happen if L1 is a rational function field
        assert L1 in FunctionFields
        raise NotImplementedError()
    else:
        # now L1 should be a simple finite extension of its base field
        beta = L1.gen()
        f = beta.minpoly()
        L0 = f.base_ring()
        assert L0.is_subring(L1)
        psi0 = inverse_of_field_isomorphism_on_subfield(phi, L0)
        f_K = f.map_coefficients(psi0, K)
        for alpha, _ in f_K.roots():
            if phi(alpha) == L(beta):
                if L0.is_prime_field():
                    psi = L1.hom([alpha])
                else:
                    psi = L1.hom([alpha], base_map=psi0)
                return psi
        # if we get here, something was wrong
        raise AssertionError("couldn't find the inverse of beta")


def homomorphism_on_standard_field(K, L, *args):
    r""" Return the homomorphism between fields determined by the
    input data.

    INPUT:

    - ``K``, ``L`` -- two fields

    - ``args`` -- optional additional arguments, of the following form:

    1. an element `\alpha\in L`,
    2. a list `[\alpha, \beta]` of two elements of `L`,
    3. an element `\alpha\in L`, and a field homorphism `\phi_0:K_0\to L`,
       defined on a certain subfield of `K`,
    4. a list `[\alpha, \beta]` of two elements of `L`, and a field homorphism
       `\phi_0:K_0\to L`, defined on a certain subfield of `K`.

    OUTPUT:

    the homomorphism `\phi:K\to L determined by ``args``.

    The rules that determine `\phi` are as follows:

    - If `K` is a subfield of `L`, then the extra arguments may be omitted, and
      then `\phi` is the natural inclusion `K\subset L`.
    - If one element `\apha\in L` is given, then `K` must be a simple extension
      of its base field `K_0`; we then try to find a homomorphism `\phi:K\to L`
      sending the canonical generator of `K/K_0` to `\alpha`. The restriction
      of `\phi` to `K_0` is either the homomorphism `\phi_0:K_0\to L` given as
      the fourth argument, or the natural inclusion `K_0\subset L`.
    - If a list of two elements `\alpha,\beta\in L` is given, then `K` must be
      a function field in standard form, i.e. a simple finite extension
      `K/K_0`, where `K_0=k(x)` is a rational function field and `y\in K` is a
      generator of `K/K_0`. In this case, we try to find a homomorphism
      `\phi:K\to L` with `\phi(x)=\alpha` and `\phi(y)=beta`. The restriction
      of `\phi` to `k`is either the homomorphism `\phi_0:k\to L` given as
      the fourth argument, or the natural inclusion `k\subset L`.

      The necessity of such a function stems from the inconsistent way
      arguments are processed bythe method :meth:`hom` attached to various kind
      of fields and rings in Sage. By implementing this funciton we hope to
      provide a more uniform way of defining homomorphisms on the kind of
      fields occuring in this project.

    """
    from sage.categories.rings import Rings
    assert K in Rings and K.is_field(), (
        "K = {} with base field {} must be a field".format(K, K.base_field()))
    # get some easy cases out of the way
    if len(args) == 0:
        assert K.is_subring(L), "if no further arguments are given, K = {} \
            must be a subfield of L = {}".format(K, L)
        return K.hom(L)
    if K.is_prime_field():
        # there can be only one homomorphism; we ignore the other arguments
        assert K.characteristic() == L.characteristic, "there is no \
            homomorhism from K = {} to L = {}.".fomat(K, L)
        return K.hom(L)

    image_gens = args[0]
    if not type(image_gens) is list:
        image_gens = [L(image_gens)]
    else:
        assert len(image_gens) == 1 or len(image_gens) == 2, (
            "wrong type of arguments!")
        image_gens = [L(alpha) for alpha in image_gens]
    # now image_gens is a list with exactly one or two elements
    # and these are elements of L

    if len(image_gens) == 2:
        K0 = K.base_field()
        k = K0.constant_base_field()
        assert K0 is not K0, "wrong type of arguments!"
        if len(args) == 2:
            phi0 = args[1]
            assert k.is_subring(phi0.domain()), "phi0 must be defined on the \
                constant base field of K"
        else:
            assert k.is_subring(L), "the constant base field of K must be \
                a subfield of L"
            phi0 = k.hom(L)
        return K.hom(image_gens, L, base_morphism=phi0)
    if hasattr(K, "base_field"):
        K0 = K.base_field()
        if K is K0:
            # now K is a rational function field, so the "base field"
            # should be the constant base field
            K0 = K0.constant_base_field()
    else:
        K0 = K.prime_subfield()
    # phi0 should be defined on K0
    if len(args) == 2:
        phi0 = args[1]
        assert K0.is_subring(phi0.domain()), "phi0 must be defined on the \
            base field K0 = {} of K = {}".format(K0, K)
    else:
        assert K0.is_subring(L), "the base field K0 = {} of K must be \
            a subfield of L = {}".format(K0, L)
        phi0 = K0.hom(L)
    if K.is_finite():
        return K.hom(image_gens, L)
    else:
        # we need to specify the codomain! It should be L
        return K.hom(image_gens, base_morphism=phi0)

# ----------------------------------------------------------------------------

#                       helper functions, old version
#                         consider this as outdated


def is_standard_function_field(F):
    r""" Return whether `F` is a standard function field.

    INPUT:

    - ``F`` -- a function field, with a constant base field `k`

    OUTPUT:

    whether `F/k` is in standard form, i.e. `F` is a separable, monogetic
    extension of the rational field field over `k`.

    """
    return F.rational_function_field() is F.base_field() and (
        F.rational_function_field() is F or F.is_separable())


def is_separable_over_rational_function_field(F):
    r""" Return whether F is a separable extension of the rational function
    field.

    INPUT:

    - ``F`` -- a function field

    So `F` is a finite extension of a rational function field `k(x)`

    OUTPUT:

    whether the extension `F/k(x)` is separable.

    """
    from sage.rings.function_field.function_field import RationalFunctionField
    if isinstance(F, RationalFunctionField):
        return True
    else:
        return (F.is_separable()
                and is_separable_over_rational_function_field(F.base_field()))


def common_subfield(phi):
    r""" Return a common subfield of the domain and the codomain of a field
    embedding.

    INPUT:

    - ``phi`` -- an embedding of fields `\phi:K\to L`

    It is assumed that `K` and `L` are standard fields.

    OUTPUT:

    a tripel `(k, s, t)`, where `k` is a subfield of `L`, `s:k\to K` is an
    embedding and `t:k\to L` is the natural inclusion.

    For the moment, we choose for `k` the common prime field of `K` and `L`.
    But it would be better to try to find the largest common subfield instead.

    """
    K = phi.domain()
    L = phi.codomain()
    k = L.prime_subfield()
    return k, k.hom(K), k.hom(L)


def smaller_constant_base_field(F, K):
    r""" Return the standard function field `F` as a function field with
    constant base field `K`.

    INPUT:

    - ``F`` -- a standard function field

    """

    raise NotImplementedError()


def base_change_of_standard_function_field(F, phi, u=None):
    r""" Return the base change of the standard function field `F` wrt `\phi`.

    INPUT:

    - ``F`` -- a standard function field
    - ``phi`` -- an embedding `\phi:k\to K`
    - ``u`` -- a `k`-linear embedding `u:K\to F`, or ``None``
               (default: ``None``)

    It is assumed that `k` is the constant base field of `F` and that `K/k`
    is finite.

    OUTPUT:

    (if `u` is not given) a pair `(F_K,s)`, where `F_K/K` is a standard
    function field and `s:F\to F_K` is an embedding which identifies `F_K/K`
    with the base change of `F/k` to `K`,

    or

    (if `u` is given) a tripel `(F_K,s, t)`, where `F_K/K` is a standard
    function field, `s:F\to F_K` is an isomorphism which identifies `F_K/K`
    with the base change of `F/k` to `K`, and `t` is the inverse of `s`.

    """
    k = phi.domain()
    K = phi.codomain()
    assert k is F.constant_base_field(), (
        "the domain of phi has to be the constant base field of F")
    F0 = F.base_field()
    f = F.polynomial()
    # f should be an irreducible polynomial over F0
    F0_K = FunctionField(K, F0.variable_name())
    psi = F0.hom([F0_K.gen()], phi)
    f_K = f.map_coefficients(psi, F0_K)
    if u is None:
        g = f_K.factor()[0][0]
        F_K = F0_K.extension(g, F.variable_name())
        return F_K, F.hom([F_K.gen()], psi)
    else:
        ut = F0_K.hom([F(F0.gen())], u)
        for g, _ in f_K.factor():
            if g.map_coefficients(ut, F)(F.gen()).is_zero():
                F_K = F0_K.extension(g, F.variable_name())
                F_to_F_K = F.hom([F_K.gen()], psi)
                F_K_to_F = F_K.hom([F.gen()], ut)
                return F_K, F_to_F_K, F_K_to_F
        # if we get here, something was wrong
        raise AssertionError()


def identity_map(K):
    r""" Return the identity map for a standard field `K`.

    """
    from sage.categories.homset import Hom
    return Hom(K, K).identity()


def is_rational_function_field(L, K):
    r""" Return whether `L` is a rational function field over K.

    """
    return L.rational_function_field() is L and L.constant_base_field() is K


def extend_standard_extension(K, k, g):
    r""" Return a finite extension of a standard extension.

    INPUT:

    - ``K`` -- a field
    - ``k`` -- a subfield of `K` such that `K/k` is a standard extension
    - ``g`` -- an irreducible polynomial over `K`

    OUTPUT:

    a tupel `(K_1,\iota, \beta)`, where

    - `K_1/k` is a standard extension,
    - `\iota:K\to K_1` is an embedding,
    - `\beta\in K_1` is such that `K_1=\iota(K)[\beta]` and `g^\iota(\beta)=0`.


    EXAMPLES::

        sage: from mclf import *
        sage: R.<x> = QQ[]
        sage: K.<theta> = NumberField(x^3 + x + 1)
        sage: g = x^2 + theta*x + 1
        sage: g.factor()
        x^2 + theta*x + 1
        sage: extend_standard_extension(K, QQ, g)
        (Number Field in theta with defining polynomial T^6 + 4*T^4 - T^3
          + 4*T^2 + 1,
         Ring morphism:
           From: Number Field in theta with defining polynomial x^3 + x + 1
           To:   Number Field in theta with defining polynomial T^6 + 4*T^4
                   - T^3 + 4*T^2 + 1
           Defn: theta |--> theta^5 + 4*theta^3 - theta^2 + 3*theta,
         theta)

    """
    from mclf.standard_fields.finite_field_extensions import (
        is_finite_extension)
    phi = k.hom(K)
    if is_finite_extension(phi):
        # K/k should be simple
        assert K.base_field() is k
        if K is k:
            L = k.extension(g, "T")
            return L, k.hom(L), L.gen()
        h = K.polynomial()
        beta = K.gen()
        assert h(beta).is_zero()
        K1 = K.extension(g, "T1")
        gamma = K1.primitive_element()
        f = minimal_polynomial(gamma, k)
        L = k.extension(f, K.variable_name())
        for beta_L, _ in h.roots(L):
            try:
                iota = K.hom([beta_L], k.hom(L))
            except:
                iota = K.hom([beta_L], L)
            g_L = g.map_coefficients(iota, L)
            roots = g_L.roots()
            if len(roots) > 0:
                return L, iota, roots[0][0]
        # if we get here, something went wrong
        raise AssertionError()
    else:
        assert is_standard_function_field(K)
        # K/k is a function field, so K1 should be a finite simple extension
        # of the rational subfield K0 = k(x)
        K0 = K.rational_function_field()
        return extend_standard_extension(K, K0, g)


def algebraic_relation(K, x, y):
    r""" Return an algebraic relation between `x` and `y`.

    INPUT:

    - ``K`` -- a function field, with constant base field `k`
    - ``x,y`` -- elements of `K`

    OUTPUT:

    an irreducible bivariate polynomial `f` over `k` such that `f(x,y)=0`.

    EXAMPLES::

        sage: from mclf import *
        sage: K0.<x> = FunctionField(GF(2))
        sage: R.<y> = K0[]
        sage: K.<y> = K0.extension(y^2+x^3+1)
        sage: algebraic_relation(K, x, y)
        x^3 + y^2 + 1
        sage: S.<z> = K[]
        sage: L.<z> = K.extension(z^2+z+x+y)
        sage: algebraic_relation(L, z+1, y)
        x^6 + x^5 + x^4*y + x^4 + x^2*y^2 + x^3 + x^2*y + x*y^2 + y^3 + y^2 + 1

    """
    K0 = K.rational_function_field()
    k = K0.constant_base_field()
    f = minimal_polynomial(x, K0)
    g = minimal_polynomial(y, K0)
    A = PolynomialRing(k, "X, Y, T")
    X, Y, T = A.gens()
    F = make_bivariate(f)(T, X)
    G = make_bivariate(g)(T, Y)
    B = PolynomialRing(k, "x, y")
    X, Y = B.gens()
    h = F.resultant(G, T)(X, Y, 0).radical()
    assert len(h.factor()) == 1, "h should be irreducible!?"
    assert h(x, y).is_zero()
    return h


def make_bivariate(f):
    r"""

    INPUT:

    - ``f`` -- an univariate polynomial over a rational function field `K=k(t)`

    OUTPUT:

    The bivariate polynomial `F\in k[t, x]` obtained from `f` by clearing the
    denominators of the coefficients of `f`.


    EXAMPLES::

        sage: from mclf import *
        sage: K.<t> = FunctionField(QQ)
        sage: R.<x> = K[]
        sage: make_bivariate(x^3/t + (t+1)*x + t*(t-2))
        t^3 + t^2*x + x^3 - 2*t^2 + t*x

    """
    R = f.parent()
    K = R.base_ring()
    k = K.constant_base_field()
    A = PolynomialRing(k, [K.variable_name(), R.variable_name()])
    t, x = A.gens()
    d = lcm([f[i].denominator() for i in range(f.degree() + 1)])
    f = d*f
    F = sum(f[i].numerator()(t)*x**i for i in range(f.degree() + 1))
    return F


def minimal_polynomial(alpha, K):
    r""" Return the minimal polynomial of `\alpha` over the field `K`.

    INPUT:

    - ``alpha`` -- an elemenent of a field `L`
    - ``K`` -- a subfield of `L` over which `alpha` is algebraic

    OUTPUT: the minimal polynomial of `\alpha` over `K`.

    """
    L = alpha.parent()
    assert K.is_subring(L), "K must be a subfield of L"
    if K == L:
        from sage.rings.polynomial.polynomial_ring_constructor import (
            PolynomialRing)
        A = PolynomialRing(K, 'T')
        return A.gen() - alpha
    elif L.base_ring() == K:
        return alpha.minpoly('T')
    else:
        A = matrix_of_extension_element(alpha, K)
        f = A.minimal_polynomial('T')
        assert f(alpha) == 0, "Error!"
        return f


def matrix_of_extension_element(alpha, K):
    r""" Return the matrix corresponding to this element
    of the field extension.

    """
    L = alpha.parent()
    M = L.base_ring()
    if M == K:
        return alpha.matrix()
    assert K.is_subring(M), "K must be a subring of M"
    A = alpha.matrix()
    n = A.nrows()
    D = {}
    for i in range(n):
        for j in range(n):
            D[(i, j)] = matrix_of_extension_element(A[i, j], K)
    m = D[(0, 0)].nrows()
    N = n*m
    from sage.matrix.constructor import matrix
    B = matrix(K, N, N)
    for i in range(n):
        for j in range(n):
            for k in range(m):
                for ell in range(m):
                    B[i*m+k, j*m+ell] = D[(i, j)][k, ell]
    return B
