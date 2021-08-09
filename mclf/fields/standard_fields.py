# -*- coding: utf-8 -*-
r"""
Standard fields
===============

We call a field `K` a *standard field* if `K` is of one of the following types:

1. `K` is a *finite field*,
2. `K` is a *number field* (i.e. a finite extension of `\mathbb{Q}`),
3. `K` is a *function field*, i.e. `K` is a finitely generated extension of
   transcendence degree one of a subfield `k`, which is itself either a finite
   field or a number field.

Basically all calculations done in this project involve calculations with such
standard fields.

One problem is that in Sage such fields do not occur in
any kind of standard form, which makes it hard to deal with
them in a systematic way. For instance, a number field may be represented as
an absolute number field, or as a tower of relative number fields. Depending
on which form the field is in, many operations (e.g. defining a homomorphism)
require very different forms of input.

To solve this problem, we create a class :class:`StandardField`.
An instance of this class represents a standard field `K`, which provides
internal access to a standard model of `K`. So if `K` is a standard field
(given as an object of the Sage category ``Rings`` such that ``K.is_field()``
is ``True``), we can define a new object ``Ks`` with the command::

    sage: Ks = standard_field(K)

The new object ``Ks`` represents the field `K` in two ways: firstly, its
**original model** and secondly its **standard model**. Here the standard model
of `K` is a field which is isomorphic to `K` and is given in *standard form*.

For a field `K` to be in **standard form** means the following:

- If `K` is a finite field with `q` elements, then `K` is in standard form if
  it is identical to the result of the Sage command ``GF(q)``.
  Note that this means that the standard model of `K` is a unique object only
  depending on the cardinality `q` of `K`.
- If `K` is a number field, it is in standard form if it is an absolute number
  field.
  In particular, if `K` is already realized as an absolute number field then
  its standard form is the field `K` itself. Note that, unlike for finite
  fields, there is no unique standard form of `K`.
- If `K` is a function field with constant base field `k`, then it is in
  standard form if `K` is either a rational function field `k(x)`, or a finite,
  simple and separable extension of `k(x)`, where `k` is a finite field or a
  number field in standard form.

We note that the constant base field `k` of a function field `K` is part of the
data on which the standard model of `K` depends.

In general, our aim is to make sure that replacing any standard field `K`
by the object ``Ks``, and then ignoring the internal realization (i.e. the
distinction between the original model and the standard model), does not lead
to confusion or an error.

For instance, if `a` is a field element which can be coerced into the original
model of `K`, then the command::

    sage: Ks(a)

coerces `a` into the standard model of `K`. Moreover, for any function `f`
defined in this module (including the methods attached to the classes defined
in this module), the test

    sage: f(a) == f(Ks(a))

should return ``True``. Similarly, if `f` is a function receiving as input
a standard field `K`, then

    sage: f(K) == f(standard_field(K))

should also return ``True``.

Operations on field elements should be perfomed via methods attached to the
object ``Ks``. For instance, if `K` is a number field and `a` is an element of
(the original model or the standard model), then the command::

    sage: f = Ks.polynomial(a)

returns a polynomial `f` with rational coefficients such that::

    sage: f(Ks.gen()) == Ks(a)

returns ``True``.

A special role is played by the method :meth:`hom`. If `K` and `L` are
standard fields, and at least `K` is represented by an instance of
:class:`StandardField`, we can define a field homomorphism `\phi:K\to L`
with the command::

    sage: phi = K.hom(L, image_gens, phi0)

Here ``image_gens`` is an element of `L` (or a list of one or two elements of
`L`) specifying the image under `\phi` of the generator(s) of the standard
model of `K`, and `\phi_0` is the *base morphism*, i.e. the restriction of
`\phi` to the natural subfield `K_0\subset K` such that `K/K_0` is generated
by ``image_gens``. If `K` is a finite or a number field, then `K_0` is
the prime subfield of `K` (so `K_0=\mathbb{F}_p` or `K_0=\mathbb{Q}`), and
`\phi_0` is uniquely determined and may be omitted. If `K` is a function field,
then `K_0` is either the constant base field, or the rational function field
`k(x)`, both of which a part of the standard model of `K`.

The output of the method :meth:`hom` is an instance of the class
:class:`EmbeddingOfStandardFields <mclf.fields.embeddings_of_standard_fields.EmbeddingOfStandardFields>`
and represents **embedding**, i.e. an
(automatically injective) field homomorphism `\phi:K\to L`.


.. TODO::

    Many things, e.g.



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
    sage: F = standard_function_field(F); F
    Function field in y_ defined by y_^3 + x_^2 + z6^3 + z6^2 + z6
    as standard function field

We can replace the constant base field of a standard function field.::

    sage: F_k0, _, _ = F.with_new_constant_base_field(k0); F_k0
    Function field in y_ defined by y_^9 + y_^8 + (x_0^2 + 1)*y_^6
      + (x_0^2 + 1)*y_^4 + (x_0^4 + (z2 + 1)*x_0^2)*y_^3
      + (x_0^4 + z2*x_0^2 + 1)*y_^2 + (x_0^4 + (z2 + 1)*x_0^2 + 1)*y_
      + x_0^6 + (z2 + 1)*x_0^2 + 1 as standard function field
    sage: F_k0.constant_base_field()
    Finite Field in z2 of size 2^2 as a standard field

"""

from sage.all import SageObject, lcm
from sage.categories.rings import Rings
from sage.categories.fields import Fields
from sage.categories.number_fields import NumberFields
from sage.categories.function_fields import FunctionFields
from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing


# ---------------------------------------------------------------------------

#                    test functions


def is_standard_field(K):
    r""" Return whether `K` is a standard field.

    INPUT:

    - ``K`` -- a Sage object

    OUTPUT:

    Whether `K` is a standard field; this means that `K` is of one of the
    following types:

    1. `K` is a finite field
    2. `K` is a number field
    3. `K` is a function field, and the constant base field is either finite or
       a number field

    If the input ``K`` is an instance of :class:`StandardField`, we also return
    ``True``.

    EXAMPLES::

        sage: from mclf import *
        sage: is_standard_field(QQ)
        True
        sage: is_standard_field(RR)
        False

    """
    if isinstance(K, StandardField):
        return True
    if K not in Fields and (K not in Rings or not K.is_field()):
        return False
    if K.is_finite() or K in NumberFields:
        return True
    elif K in FunctionFields:
        k = K.constant_base_field()
        return k.is_finite() or k in NumberFields
    else:
        return False


def is_in_standard_form(K):
    r""" Return whether the field `K` is in standard form.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    whether `K` is in standard form; this means the following:

    - if `K` is finite, then `K` is the uniquely determined field with `q=|K|`
      elements, which results from the command ``GF(q)``,
    - if `K` is a finite field extension of `\mathbb{Q}`, then `K` is
      actually an absolute number field,
    - if `K` is a function field, then there are two cases:

      1. `K` is a rational function field over a finite or number field
      which is itself in standard form

      2. `K` is a finite, simple and separable extension of degree `> 1` of
      a rational function field in standard form.

    If `K` is given as an instance of the class :class:`StandardField`
    we return ``True`` as well.

    The result should be equivalent to::

        sage: K is standard_field(K).standard_model()

    EXAMPLES::

        sage: from mclf import *

    A finite field is in standard form iff it is given by ``GF(q)``.::

        sage: is_in_standard_form(GF(4))
        True

    If other options are passed to ``GF``, the result is not in standard form::

        sage: is_in_standard_form(GF(4, "z"))
        False

    Number fields are in standard form iff they are absolute number fields.::

        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^2+2)
        sage: is_in_standard_form(K)
        True
        sage: L.<b> = K.extension(x^2+3)
        sage: is_in_standard_form(L)
        False

    Function fields are in standard form iff they are finite, simple and
    separable extensions of a rational function field over a field `k`
    in standard form.::

        sage: is_in_standard_form(FunctionField(K, "x"))
        True
        sage: is_in_standard_form(FunctionField(L, "x"))
        False

    A finite extension of a rational function field is in standard form if
    the constant base field is in standard form, and if the extension is
    finite, simple, separable and of degree `>1`:

    """
    if isinstance(K, StandardField):
        return True
    assert K in Fields or K in Rings and K.is_field(), "K must be a field"
    assert is_standard_field(K), "K must be a standard field"
    if K.is_finite():
        from sage.all import GF
        q = K.cardinality()
        return K is GF(q)
    elif K in NumberFields:
        # not sure this is the right test..
        return hasattr(K, "is_absolute") and K.is_absolute()
    elif K in FunctionFields:
        k = K.constant_base_field()
        K0 = K.rational_function_field()
        if is_in_standard_form(k):
            if K0 is K.base_field():
                # K is a rational function field
                return True
            else:
                # we test whether K/K_0 is simple, separable and of degree >1
                return (K.rational_function_field() is K.base_field()
                        and K.is_separable() and K.degree() > 1)
        else:
            # the constant base field is not in standard form
            return False

# ----------------------------------------------------------------------------

#                     constructor functions


def standard_field(K):
    r""" Return the standard form of this field.

    INPUT:

    - ``K`` -- a standard field

    OUTPUT:

    the object representing `K` and its standard model.

    If the input ``K`` is an instance of :class:`StandardField`, then
    ``K`` itself is returned. Otherwise, an instance ``Ks`` of
    :class:`StandardField` is returned such that ``Ks.original_model()``
    is equal to the input ``K``

    EXAMPLES::

        sage: from mclf import *
        sage: standard_field(QQ)
        Rational Field as a standard field

        sage: R.<x> = GF(2)[]
        sage: k.<z> = GF(2).extension(x^3+x^2+1)
        sage: k = standard_field(k); k
        Finite Field in z of size 2^3 as a standard field
        sage: k.generator()
        z3
        sage: k.polynomial()
        x^3 + x + 1

        sage: R.<x> = QQ[]
        sage: K.<a> = NumberField(x^2+x+1)
        sage: L.<b> = K.extension(x^3+a*x+1)
        sage: LL = standard_field(L)
        sage: LL.original_model()
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
    if isinstance(K, StandardField):
        return K
    assert is_standard_field(K), "K must be a standard field"
    if K.is_finite():
        return StandardFiniteField(K)
    elif K in NumberFields:
        return StandardNumberField(K)
    else:
        return standard_function_field(K)


def standard_finite_field(q):
    r""" Return the finite field with `q` elements, as a standard field.

    INPUT:

    - ``q`` -- a prime power `q=p^r>1`

    OUTPUT:

    the field with `q` elements, as a standard field.

    """
    from sage.all import GF
    return standard_field(GF(q))


def standard_number_field(f, gen_name):
    r""" Return the number field given by a polynomial `f`,
    as a standard field.

    INPUT:

    - ``f`` -- an irreducible polynomial over `\mathbb{Q}`
    - ``gen_name`` -- an alphanumeric string

    OUTPUT:

    the number field `K` with one generator with minimal polynomial `f`,
    as a standard field.

    """
    from sage.all import NumberField
    return standard_field(NumberField(f, gen_name))


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

    Note that the constant base field of the output is the standard model
    of `k`:
    ::

        sage: k0.<a> = GF(4)
        sage: R.<t> = k0[]
        sage: k.<b> = k0.extension(t^2+t+a); k
        Univariate Quotient Polynomial Ring in b over Finite Field in a
        of size 2^2 with modulus b^2 + b + a
        sage: F = standard_rational_function_field(k, "x"); F
        Rational function field in x over Finite Field in z4 of size 2^4
        as standard rational function field

    """
    if isinstance(k, StandardField):
        assert k.is_finite() or k.is_number_field()
        k = k.standard_model()
    else:
        assert k in Fields or k in Rings and k.is_field(), "k must be a field"
        assert k.is_finite() or k in NumberFields, "k must be either finite, \
            or a number field."
        k = standard_field(k).standard_model()
    F = FunctionField(k, var_name)
    return StandardFunctionField(F)


def standard_function_field(K):
    r""" Return the standard model of this function field.

    INPUT:

    - ``K`` -- a standard function field

    Alternatively, the function field `K` can also be given as an irreducible
    bivariate polynomial `f` over a finite field or a number field `k`.
    In this case, we set `K:=k(x,y \mid f(x,y)=0)`.

    OUTPUT:

    the object representing the function field `K` and its standard model.

    .. NOTE::

        At the moment, a standard model may be an extension of `k(x)` of degree
        one; in this case, it would be better to replace it with `k(x)` itself.


    EXAMPLES::

        sage: from mclf import *
        sage: k = GF(2)
        sage: R.<t> = k[]
        sage: F0.<x> = FunctionField(k)
        sage: S.<y> = F0[]
        sage: F.<y> = F0.extension(y^2+y+1); F
        Function field in y defined by y^2 + y + 1
        sage: standard_function_field(F)
        Function field in y defined by y^2 + y + 1 as standard function field

    We can also define a standard function field by an equation:
    ::

        sage: A.<x,y> = k[]
        sage: standard_function_field(y^2+x^3+1)
        Function field in y defined by y^2 + x^3 + 1 as standard function field

    """

    if K not in Fields and not (K in Rings and K.is_field()):
        # we assume that K is a bivariate polynomial
        f = K
        A = f.parent()
        K0 = FunctionField(A.base_ring(), A.variable_names()[0])
        R = PolynomialRing(K0, A.variable_names()[1])
        G = R(f(K0.gen(), R.gen()))
        assert G.degree() > 0, "the polynomial f must have positive degree in y"
        assert G.is_irreducible(), "the polynomial F must be irreducible"
        K = K0.extension(G.monic(), A.variable_names()[1])
    return StandardFunctionField(K)


# --------------------------------------------------------------------------

#                   standard field classes

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

        If `a` is an element of the standard model, then we return `a` itself.
        Otherwise, we try to coerce `a` into the original model.

        """
        if a.parent().is_subring(self.standard_model()):
            return self.standard_model()(a)
        else:
            return self.from_original_model()(a)

    def contains_as_subfield(self, k):
        r""" Return whether elements of `k` can be coerced into
        this standard field.

        INPUT:

        - ``k`` -- a standard field

        OUTPUT:

        whether any element of `k` can be coerced into this standard field `K`.

        This means that for any element of `k`, the command `K(a)` does not
        raise an error and produces a meaningful result. In fact, this is true
        iff `a` can be coerced into the standard model of `K` or into the
        original model.

        If this method returns ``True`` we can define the embedding of `k` into
        this field via::

            sage: K.embedding_of_subfield(k)


        EXAMPLES::

            sage: from mclf import *
            sage: K0 = GF(4)
            sage: R.<t> = K0[]
            sage: K.<a> = K0.extension(t^2+t+K0.gen())
            sage: Ks = standard_field(K)
            sage: Ks.contains_as_subfield(K)
            True

        """
        # if L is an instance of StandardField, an "element" of L is an
        # element of the standard model
        if isinstance(k, StandardField):
            k = k.standard_model()
        return (self.standard_model().has_coerce_map_from(k)
                or self.original_model().has_coerce_map_from(k))

    def embedding_of_subfield(self, k):
        r""" Return the embedding of a subfield into this standard field.

        INPUT:

        - ``k`` -- a standard field, which can be coerced into this field `K`

        OUTPUT:

        the natural embedding `k\to K`.

        If there is no natural embedding, an error is raised.

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K1.<a> = NumberField(x^2+2)
            sage: K2.<b> = K1.extension(x^2 + a)
            sage: K = standard_field(K2)
            sage: K.embedding_of_subfield(K1)
            the embedding of Number Field in a with defining polynomial x^2 + 2
            into Number Field in b with defining polynomial x^4 + 2,
            sending a to -b^2

        """
        assert is_standard_field(k), "k must be a standard field"
        assert self.contains_as_subfield(k), (
            "k must be a natural subfield of K")
        if not isinstance(k, StandardField):
            k = standard_field(k)
        return k.hom(self)

    def is_subfield_of(self, L):
        r""" Return whether elements of this standard field can be coerced
        into `L`.

        INPUT:

        - ``L`` -- a standard field

        OUTPUT:

        whether any element of (the standard model of) this field can be
        coerced into `L`.

        If this is true then we can define the natural embedding of this field
        `K` into `L` via::

            sage: K.hom(L)


        EXAMPLES::

            sage: from mclf import *
            sage: K0 = GF(4)
            sage: R.<t> = K0[]
            sage: K.<a> = K0.extension(t^2+t+K0.gen())
            sage: Ks = standard_field(K)
            sage: Ks.is_subfield_of(K)
            False

        """
        if isinstance(L, StandardField):
            return L.contains_as_subfield(self)
        else:
            return L.has_coerce_map_from(self.standard_model())

    def polynomial_ring(self, var_names):
        r""" Return a polynomial ring over this standard field.

        INPUT:

        - ``var_names`` -- a list of alphanumeric strings

        OUTPUT:

        the polynomial ring over the standard model of this field,
        with variable names ``var_names``.

        """
        return PolynomialRing(self.standard_model(), var_names)

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
            from mclf.fields.factor_polynomial_over_function_field \
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
        if self.is_function_field() and not self.is_rational_function_field():
            from mclf.fields.factor_polynomial_over_function_field \
                import factor_polynomial_over_function_field
            factors_of_f = factor_polynomial_over_function_field(
                self.standard_model(), f)
        else:
            factors_of_f = f.factor()
        return [g for g, _ in factors_of_f]

    def extension(self, f, gen_name=None):
        r""" Return the finite extension of this field given by an irreducible
        polynomial.

        INPUT:

        - ``f`` -- an irreducible univariate polynomial over this field.
        - ``gen_name`` -- an alphanumeric string (optional)

        OUTPUT:

        The finite simple extension `L/K` given by `f`. This is an object of
        :class:`StandardFiniteFieldExtension <mclf.fields.\
        finite_field_extensions.StandardFiniteFieldExtension`.


        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_field(QQ)
            sage: x = K.polynomial_generator("x")
            sage: K.extension(x^2+2)
            Number Field in x with defining polynomial x^2 + 2,
            as finite extension of Rational Field
            sage: K.extension(x^2+2, "a")
            Number Field in a with defining polynomial x^2 + 2,
            as finite extension of Rational Field

        """
        # we make sure the base ring of f is the standard model
        f = self.change_coefficients(f)
        # we make sure that f is irreducible
        assert len(self.prime_factors(f)) == 1, "f must be irreducible"
        from mclf.fields.finite_field_extensions import (
            finite_field_extension)
        return finite_field_extension(self, f, gen_name)

    def inclusion(self, L):
        r""" Return the inclusion of this standard field into `L`.

        INPUT:

        ``L`` -- another standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this standard field `K` into
        `L`, provided there is one. If not, an error is raised.

        This must be realized by the subclass.

        """
        raise NotImplementedError()

    def structure(self):
        r""" Return the structure of this standard field.

        This is a presentation of this standard field `K` as a sequence of
        simple extensions.

        OUTPUT:

        a list of triples `(K_i, \alpha_i, f_i)`, `i=1,\ldots,r`, such that

        - `K_0\subset K_1\subset \ldots \subset K_r` is an increasing sequence
          of subfields of (the standard model of) this field `K`, where `K_0`
          is the prime field and `K_r=K`,
        - `\alpha_i\in K_i` is a generator of the extension `K_i/K_{i-1}`,
        - `f_i` is the minimal polynomial of `\alpha_i` over `K_{i-1}`,
          or `f_i=0` if `\alpha_i` is transcendental over `K_{i-1}`.

        Note that if `K` is a finite or a number fields, then `r=1`, and if `K`
        is a function field we have `r=2` or `r=3`.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_field(GF(4))
            sage: k.structure()
            [(Finite Field in z2 of size 2^2, z2, x^2 + x + 1)]

            sage: x, y = k.polynomial_generators(["x", "y"])
            sage: K = standard_function_field(x^3 + y^2)
            sage: K.structure()
            [(Finite Field in z2 of size 2^2, z2, x^2 + x + 1),
             (Rational function field in x over Finite Field in z2 of size 2^2,
               x, 0),
             (Function field in y defined by y^2 + x^3, y, y^2 + x^3)]

        """
        K = self.standard_model()
        if self.is_finite() or self.is_number_field():
            return [(K, self.generator(), self.polynomial())]
        elif self.is_function_field():
            k = self.constant_base_field()
            if self.is_rational_function_field():
                x = self.generator()
                f = self.polynomial_ring(["xx"]).zero()
                return k.structure() + [(K, x, f)]
            else:
                K0 = self.rational_base_field()
                y = self.generator()
                f = self.polynomial()
                return K0.structure() + [(K, y, f)]
        else:
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
        return "the standard field with {} elements".format(
                self.cardinality())

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

    def minimal_polynomial(self, a, var_name="x"):
        r""" Return the absolute minimal polynomial of a field element.

        INPUT:

        - ``a`` -- an element of this finite field
        - ``var_name`` -- an alphanumeric string

        OUTPUT:

        the absolute minimal polynomial of `a`; this is an irreducible
        polynomial over the prime field.

        We use ``var_name`` for the name of the variable of the minimal
        polynomial. The default value is "x".

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_finite_field(9)
            sage: K.minimal_polynomial(K.generator()^2 + 1)
            x^2 + x + 2
            sage: K.minimal_polynomial(5)
            x + 1

        """
        a = self(a)
        if self.is_prime_field():
            R = PolynomialRing(self.prime_field(), var_name)
            return R.gen() - a
        else:
            return a.minpoly(var_name)

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
            assert self.is_subfield_of(L)
            a = L(self.generator())
        elif len(a) == 1:
            a = a[0]
        else:
            raise ValueError("wrong number of arguments")
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfFiniteField)
        return EmbeddingOfFiniteField(self, L, a)

    def inclusion(self, L):
        r""" Return the inclusion of this finite field into `L`.

        INPUT:

        ``L`` -- a standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this finite field `K` into
        `L`, provided there is one. If not, an error is raised.

        EXAMPLES::

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
        return False

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

    def minimal_polynomial(self, a, var_name="x"):
        r""" Return the absolute minimal polynomial of a field element.

        INPUT:

        - ``a`` -- an element of this number field
        - ``var_name`` -- an alphanumeric string

        OUTPUT:

        the absolute minimal polynomial of `a`; this is an irreducible
        polynomial over `\mathbb{Q}`.

        We use ``var_name`` for the name of the variable of the minimal
        polynomial. The default value is "x".

        EXAMPLES::

            sage: from mclf import *
            sage: R.<x> = QQ[]
            sage: K = standard_number_field(x^3 - 2, "a")
            sage: K.minimal_polynomial(K.generator()^2 + 1)
            x^3 - 3*x^2 + 3*x - 5
            sage: K.minimal_polynomial(2)
            x - 2

        """
        a = self(a)
        if self.is_prime_field():
            R = PolynomialRing(self.prime_field(), var_name)
            return R.gen() - a
        else:
            return a.minpoly(var_name)

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

        The result is an instance of the class
        :class:`EmbeddingOfNumberField <mclf.fields.\
        embeddings_of_standard_fields.EmbeddingOfNumberField>`.
        """
        if not isinstance(L, StandardField):
            assert is_standard_field(L), "L must be a standard field"
            L = standard_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if len(a) == 0:
            assert self.is_subfield_of(L)
            a = L(self.generator())
        elif len(a) == 1:
            a = L(a[0])
        else:
            raise ValueError("wrong number of arguments")
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfNumberField)
        return EmbeddingOfNumberField(self, L, a)

    def inclusion(self, L):
        r""" Return the inclusion of this number field into `L`.

        INPUT:

        ``L`` -- a standard field

        OUTPUT:

        the natural inclusion `\phi:K\to L` of this number field `K` into
        `L`, provided there is one. If not, an error is raised.

        EXAMPLES::

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
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfNumberField)
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
            if is_in_standard_form(K):
                # take K as the standard model
                F = K
                F_to_K = identity_map(K)
                K_to_F = identity_map(K)
            else:
                F, K_to_F, F_to_K = standard_model_of_function_field(K)

            k = standard_field(F.constant_base_field())
            self._original_model = K
            self._constant_base_field = k
            self._standard_model = F
            self._from_original_model = K_to_F
            self._to_original_model = F_to_K
            if F.base_field() is F:
                self._is_rational_function_field = True
                self._rational_base_field = F
                self._generators = [F.gen()]
                self._polynomial = None
                self._bivariate_polynomial = None
            else:
                self._is_rational_function_field = False
                x = F.base_field().gen()
                y = F.gen()
                self._rational_base_field = standard_function_field(
                    F.base_field())
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
            if f.is_zero():
                return (A.zero(), A.one())
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
        r""" Return the minimal polynomial of this element over the rational
        base field.

        INPUT:

        - `t` -- an element of this function field `F`

        OUTPUT:

        The minimal polynomial of `t` over the rational base field `k(x)`
        of `F`.

        """
        if self.is_rational_function_field():
            # We return T-t
            T = self.polynomial_generator(var_name)
            return T - self(t)
        else:
            return self(t).minpoly(var_name)

    def norm(self, t):
        r""" Return the norm of this element over the rational base field.

        INPUT:

        - `t` -- an element of this function field `F`

        OUTPUT:

        The norm of `t` over the rational base field `k(x)` of `F`.

        """
        if self.is_rational_function_field():
            return self(t)
        else:
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
            x^6 + x^5 + x^4*y + x^4 + x^2*y^2 + x^3 + x^2*y + x*y^2
              + y^3 + y^2 + 1

        """
        K = self
        K0 = K.rational_base_field()
        k = K.constant_base_field()
        f = K.minimal_polynomial(x)
        g = K.minimal_polynomial(y)
        X, Y, T = k.polynomial_generators(["X", "Y", "T"])
        F = make_bivariate(f)(T, X)
        G = make_bivariate(g)(T, Y)
        X, Y = k.polynomial_generators(["x", "y"])
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
        3. We have `\phi=\psi_0` on `k(x)` and `\phi(y)=u` otherwise.

        If no such embedding exists, an error is raised.

        If `\phi_0` is not given, we assume that we are in Case 1 or 2, and
        that there is a canonical embedding of the constant base field `k`
        into `L`.  If not, an error is raised.

        The result is an instance of
        :class:`EmbeddingOfFunctionField <mclf.fields.\
        embeddings_of_standard_fields.EmbeddingOfFunctionField>`.

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
            sage: L = K.extension(y^2 + x^3 +1); L
            Function field in y1 defined by y1^2 + x^3 + 1,
            as finite extension of Rational function field in x over
            Rational Field
            sage: y = L.generator()
            sage: L.hom(L, [x, -y])
            the embedding of Function field in y defined by y^2 + x^3 + 1
            into Function field in y defined by y^2 + x^3 + 1,
            sending [x, y] to [x, -y]

            sage: k = standard_field(GF(4))
            sage: phi0 = k.hom(k, k.generator()^2)
            sage: F = standard_rational_function_field(k, "x")
            sage: x = F.generator()
            sage: phi = F.hom(F, x, phi0); phi
            the embedding of Rational function field in x over Finite Field
            in z2 of size 2^2 into Rational function field in x over Finite
            Field in z2 of size 2^2, sending [x] to [x]
            sage: phi(k.generator())
            z2 + 1

        """
        from mclf.fields.embeddings_of_standard_fields import (
           embedding_of_standard_fields, EmbeddingOfStandardFields)
        K = self
        K0 = K.rational_base_field()
        k = K.constant_base_field()
        if not isinstance(L, StandardFunctionField):
            L = standard_function_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")
        if not type(image_of_gens) is list:
            image_of_gens = [L(image_of_gens)]
        else:
            image_of_gens = [L(a) for a in image_of_gens]
        if len(args) == 0:
            assert k.is_subfield_of(L)
            phi0 = k.hom(L)
            if len(image_of_gens) == 1:
                assert K.is_rational_function_field(), "wrong input"
        elif len(args) == 1 and len(image_of_gens) == 1:
            phi0 = args[0]
            if not isinstance(phi0, EmbeddingOfStandardFields):
                phi0 = embedding_of_standard_fields(phi0)
            assert phi0.maps_into(L)
            if not K.is_rational_function_field():
                image_of_gens = [phi0(K0.generator())] + image_of_gens
        elif len(args) == 1 and len(image_of_gens) == 2:
            phi0 = args[0]
            assert phi0.applies_to(k)
        else:
            raise ValueError("wrong type of arguments")
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfFunctionField)
        return EmbeddingOfFunctionField(self, L, image_of_gens, phi0)

    def with_new_constant_base_field(self, phi0):
        r""" Return this standard function field, with a new constant
        base field.

        INPUT:

        - ``phi0`` -- a field homomorphism `\phi:k_1\to F`.

        Here `F` is this function field, and `k_1` is a finite or an number
        field.

        Alternatively, one can define `\phi_0` by giving a subfiekd `k_1`
        of `F`, in wich case we take for `\phi_0` the canonical inclusion
        `k_1\subset F`.


        OUTPUT:

        a pair `(F_1, s)`, where `F_1` is a standard function field with
        constant base field `k_1`, `s:F_1\to F` is an isomorphism extending
        `\phi_0`, and `t:F\to F_1` is the inverse of `s`.


        EXAMPLES::

            sage: from mclf import *
            sage: R.<t> = QQ[]
            sage: k0 = standard_field(QQ)
            sage: k = k0.extension(t^2+1)
            sage: x, y = k0.polynomial_generators(["x", "y"])
            sage: F = standard_function_field(x^2+y^2); F
            Function field in y defined by y^2 + x^2 as standard function field

            sage: i = k.relative_generator()
            sage: x, y = F.generators()
            sage: phi = k.relative_hom(F, x/y)
            sage: F1, _, _ = F.with_new_constant_base_field(phi); F1
            Rational function field in x0 over Number Field in t with defining
            polynomial t^2 + 1, as finite extension of Rational function field
            in x0 over Number Field in t with defining polynomial t^2 + 1

        """
        from mclf.fields.embeddings_of_standard_fields import (
            embedding_of_standard_fields, EmbeddingOfStandardFields)
        F = self
        if is_standard_field(phi0):
            k1 = phi0
            assert F.contains_as_subfield(k1)
            phi0 = F.embedding_of_subfield(k1)
        elif not isinstance(phi0, EmbeddingOfStandardFields):
            phi0 = embedding_of_standard_fields(phi0)
        # now phi0 is a embedding of standard fields

        k = F.constant_base_field()
        k1 = phi0.Domain()
        assert k1.is_finite() or k1.is_number_field()
        assert phi0.maps_into(F)

        # first we construct a rational function field F01 over k1;
        # the desired field F1 will be a finite extension of F01
        F01 = standard_rational_function_field(k1, F.variable_names()[0]+"0")
        F01_to_F = F01.hom(F, F.generators()[0], phi0)

        alpha = k.generator()
        f = k.polynomial()    # f is defined over the common prime field of
        #                       k and k1
        factors_of_f_k1 = k1.prime_factors(f)
        found_factor = False
        for g in factors_of_f_k1:
            if k.change_coefficients(g)(alpha).is_zero():
                F11 = F01.extension(g)  # F11/F01 is in FiniteFieldExtension!
                found_factor = True
                break
        assert found_factor
        F11_to_F = F11.relative_hom(F, alpha, F01_to_F)
        k_to_F11 = k.hom(F11, F11.relative_generator())
        if F.is_rational_function_field():
            # we are already done
            F_to_F11 = F.hom(F11, F01.generator(), k_to_F11)
            return F11.extension_field(), F_to_F11, F11_to_F
        else:
            # F is a proper extension of F0 = k(x), and F11_to_F is not
            # yet surjective
            F0 = F.rational_base_field()
            F0_to_F11 = F0.hom(F11, F11.generators()[0], k_to_F11)
            y = F.generator()
            f = F.polynomial()  # this is a polynomial over F0
            f_F11 = F0_to_F11.change_coefficients(f)
            factors_of_f_F11 = F11.prime_factors(f_F11)
            for g in factors_of_f_F11:
                g_F = F11_to_F.change_coefficients(g)
                if g_F(y).is_zero():
                    F1 = F11.extension(g)
                    F1_to_F = F1.relative_hom(F, y, F11_to_F)
                    F_to_F1 = F.hom(F1, F1.relative_generator(), F0_to_F11)
                    return F1.extension_field(), F_to_F1, F1_to_F
            # if we get here, something went wrong
            raise AssertionError("Didn't find the correct factor")

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

        EXAMPLES::

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
        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfFunctionField)
        if not isinstance(L, StandardField):
            L = standard_field(L)
        k = self.constant_base_field()
        phi0 = k.hom(L.constant_base_field())
        image_of_gens = [L(a) for a in self.generators()]
        return EmbeddingOfFunctionField(self, L, image_of_gens, phi0)


# ---------------------------------------------------------------------------

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
    if is_in_standard_form(K):
        return K, identity_map(K), identity_map(K)
    if K.rational_function_field() is K:
        # K is a rational function field, but its constant base field
        # is not in standard form
        k = standard_field(K.constant_base_field())
        F = FunctionField(k.standard_model(), K.variable_name())
        K_to_F = K.hom([F.gen()], k.from_original_model())
        F_to_K = F.hom([K.gen()], k.to_original_model())
        return F, K_to_F, F_to_K
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


#  this should be obsolete; it is only used when initializing a finite
# field as a standard field.
# however, the class "EmbeddingOfStandardField" has a method "inverse"


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

    the homomorphism `\phi:K\to L` determined by ``args``.

    The rules that determine `\phi` are as follows:

    - If `K` is a subfield of `L`, then the extra arguments may be omitted, and
      then `\phi` is the natural inclusion `K\subset L`.
    - If one element `\alpha\in L` is given, then `K` must be a simple extension
      of its base field `K_0`; we then try to find a homomorphism `\phi:K\to L`
      sending the canonical generator of `K/K_0` to `\alpha`. The restriction
      of `\phi` to `K_0` is either the homomorphism `\phi_0:K_0\to L` given as
      the fourth argument, or the natural inclusion `K_0\subset L`.
    - If a list of two elements `\alpha,\beta\in L` is given, then `K` must be
      a function field in standard form, i.e. a simple finite extension
      `K/K_0`, where `K_0=k(x)` is a rational function field and `y\in K` is a
      generator of `K/K_0`. In this case, we try to find a homomorphism
      `\phi:K\to L` with `\phi(x)=\alpha` and `\phi(y)=\beta`. The restriction
      of `\phi` to `k`is either the homomorphism `\phi_0:k\to L` given as
      the fourth argument, or the natural inclusion `k\subset L`.

      The necessity of such a function stems from the inconsistent way
      arguments are processed by the method :meth:`hom` attached to various kind
      of fields and rings in Sage. By implementing this funciton we hope to
      provide a more uniform way of defining homomorphisms on the kind of
      fields occuring in this project.


      EXAMPLES::

        sage: from mclf import *
        sage: R.<t> = QQ[]
        sage: K.<i> = NumberField(t^2+1)
        sage: homomorphism_on_standard_field(K, K, [-i])
        Ring endomorphism of Number Field in i with defining polynomial
        t^2 + 1
          Defn: i |--> -i

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

    # now len(image_gens)=1
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
    if K.is_finite() or (hasattr(K, "is_absolute") and K.is_absolute()):
        return K.hom(image_gens, L)
    else:
        # we need to specify the codomain! It should be L
        return K.hom(image_gens, base_morphism=phi0)


def identity_map(K):
    r""" Return the identity map for a standard field `K`.

    """
    from sage.categories.homset import Hom
    return Hom(K, K).identity()


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
