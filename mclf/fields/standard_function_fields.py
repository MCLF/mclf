# -*- coding: utf-8 -*-
r"""
Standard function fields
========================



"""

from sage.categories.rings import Rings
from sage.categories.fields import Fields
from sage.categories.number_fields import NumberFields
from sage.categories.function_fields import FunctionFields
from sage.rings.function_field.constructor import FunctionField
from mclf.fields.standard_fields import StandardField


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
        standard function field in [x, y] over Finite Field of size 2,
        with equation y^2 + y + 1

    We can also define a standard function field by an equation:
    ::

        sage: A.<x,y> = k[]
        sage: standard_function_field(y^2+x^3+1)
        standard function field in [x, y] over Finite Field of size 2,
        with equation x^3 + y^2 + 1

    """

    if K not in Fields and not (K in Rings and K.is_field()):
        # we assume that K is a bivariate polynomial
        f = K
        A = f.parent()
        K0 = FunctionField(A.base_ring(), A.variable_names()[0])
        from sage.all import PolynomialRing
        R = PolynomialRing(K0, A.variable_names()[1])
        G = R(f(K0.gen(), R.gen()))
        assert G.degree() > 0, "the polynomial f must have positive degree in y"
        assert G.is_irreducible(), "the polynomial F must be irreducible"
        K = K0.extension(G.monic(), A.variable_names()[1])
    # now K should be a function field
    F, K_to_F, F_to_K = standard_model_of_function_field(K)
    if F.base_field() is F:
        return StandardRationalFunctionField(K_to_F, F_to_K)
    else:
        return StandardNonrationalFunctionField(K_to_F, F_to_K)


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
        standard rational function field in xx over Rational Field


    Note that the constant base field of the output is the standard model
    of `k`:
    ::

        sage: k0.<a> = GF(4)
        sage: R.<t> = k0[]
        sage: k.<b> = k0.extension(t^2+t+a); k
        Univariate Quotient Polynomial Ring in b over Finite Field in a
        of size 2^2 with modulus b^2 + b + a
        sage: F = standard_rational_function_field(k, "x"); F
        standard rational function field in x over Finite Field in z4
        of size 2^4

    """
    if isinstance(k, StandardField):
        assert k.is_finite() or k.is_number_field()
        k = k.standard_model()
    else:
        assert k in Fields or k in Rings and k.is_field(), "k must be a field"
        assert k.is_finite() or k in NumberFields, "k must be either finite, \
            or a number field."
        from mclf.fields.standard_fields import standard_field
        k = standard_field(k).standard_model()
    from sage.all import FunctionField
    F = FunctionField(k, var_name)
    return StandardRationalFunctionField(F)


class StandardFunctionField(StandardField):
    r""" A function field over a finite field or a number field.

    INPUT:

    - ``K`` -- a function field `K` whose constant base field is finite
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

    def embedding_of_constant_base_field(self):
        r""" Return the embedding of the constant base field into this
        function field.

        """
        if not hasattr(self, "_embedding_of_constant_base_field"):
            from mclf.fields.embeddings_of_standard_fields import (
                EmbeddingOfConstantBaseField)
            self._embedding_of_constant_base_field = (
                EmbeddingOfConstantBaseField(self))
        return self._embedding_of_constant_base_field

    def constant_base_field(self):
        r""" Return the constant base field of this function field.

        EXAMPLES:

            sage: from mclf import *
            sage: k = standard_finite_field(2)
            sage: F0 = standard_rational_function_field(k, "x")
            sage: F0.constant_base_field()
            Finite Field of size 2, as a subfield of Rational function field
            in x over Finite Field of size 2

            sage: x = F0.generator()
            sage: y = F0.polynomial_generator("y")
            sage: F = F0.extension(y^2 + x^3 + 1, "y")
            sage: F.constant_base_field()
            Finite Field of size 2, as a subfield of Function field in y
            defined by y^2 + x^3 + 1

        """
        from mclf.fields.standard_subfields import standard_subfield
        if not hasattr(self, "_constant_base_field"):
            k = standard_subfield(self.embedding_of_constant_base_field())
            self._constant_base_field = k
        return self._constant_base_field

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

    def hom(self, L, *args):
        r""" Return a homomorphism from this function field to another function
        field.

        INPUT:

        - ``L`` -- a standard function field
        - ``args`` -- additional arguments

        OUTPUT:

        the embedding `\phi:K\to L` of this standard function field `K`
        into the given standard function field `L`, determined by the
        additional data ``args``, which must be in one of the following forms:

        - empty,
        - ``image_gens``: an element `\alpha` of `L`, or a list of one to three
          elements of `L`,
        - (``image_gens``, ``base_map``): here ``imega_gens`` is as above, and
          ``base_map`` is an embedding `\phi_0:K_0\to L` of a subfield `K_0`
          of `K`, which must be either the constant base field, or the rational
          base field.

        The embedding `\phi:K\to L` is determined as follows:

        1. If ``args`` is empty, `K` must be a natural subfield of `L`, in
           which case we return the natural inclusion.
        2. If ``base_map`` is not given, then the subfield `K_0` must also have
           a natural embedding into `L`, which we then choose for `\phi_0`.
           The embedding `\phi` is an extension of `\phi_0` determined by
           ``image_gens``.
        3. `\phi` is the unique extension of `\phi_0` which sends the natural
           generators of `K/K_0` to the elements of ``image_gens``.
        4. The subfield `K_0\subset K` is the unique natural subfield of `K`
           such that the number of generators of `K/K_0` is equal to the number
           of elements in ``image_gens``. For instance, if `K=k(x)` is a
           rational function field and `K_0=k` is the constant base field, then
           `K/K_0` has one natural generator, `x`. But if `K_0` is the prime
           subfield which is a proper subfield of `k`, then `K/K_0` has
           two generators, `a,x`, where `a` is the absolute generator of `k`.

        If no such embedding exists, an error is raised.

        The result is an instance of
        :class:`EmbeddingOfFunctionField <mclf.fields.\
        embeddings_of_standard_fields.EmbeddingOfFunctionField>`.

        EXAMPLES::

            sage: from mclf import *
            sage: K = standard_rational_function_field(QQ, "x")
            sage: x = K.generator()
            sage: phi = K.hom(K, [x^2 + x]); phi
            the embedding of Rational function field in x over Rational Field
            into Rational function field in x over Rational Field,
            sending [x] to [x^2 + x]
            sage: phi(x^3)
            x^6 + 3*x^5 + 3*x^4 + x^3

            sage: y = K.polynomial_generator("y")
            sage: L = K.extension(y^2 + x^3 +1); L
            Function field in y defined by y^2 + x^3 + 1, as finite extension
            of Rational function field in x over Rational Field
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
        if not isinstance(L, StandardFunctionField):
            L = standard_function_field(L)
        assert self.characteristic() == L.characteristic(), (
            "K and L must have the same characteristic")

        if len(args) == 0:
            assert L.contains_as_subfield(K), "K must be a subfield of L"
            phi0 = K.constant_base_field().hom(L)
            image_gens = [L(a) for a in K.generators()]
        elif len(args) == 1:
            image_gens = args[0]
            phi0 = None
        elif len(args) == 2:
            image_gens = args[0]
            phi0 = args[1]
        else:
            raise TypeError("wrong number of arguments")

        if not type(image_gens) is list:
            assert L.is_element(image_gens), "image_gens={} must be an element \
            of L = {} or a list of elements".format(image_gens, L)
            image_gens = [L(image_gens)]
        else:
            image_gens = [L(a) for a in image_gens]

        if len(image_gens) == 1:
            if K.is_rational_function_field():
                K0 = K.constant_base_field()
            else:
                K0 = K.rational_base_field()
        elif len(image_gens) == 2:
            if K.is_rational_function_field():
                K0 = K.prime_subfield()
                assert not K0.is_equal(K.constant_base_field())
            else:
                K0 = K.constant_base_field()
        elif len(image_gens) == 3:
            assert not K.is_rational_function_field()
            K0 = K.prime_subfield()
            assert not K0.is_equal(K.constant_base_field())
        else:
            raise TypeError("image_gens must have one or two elements")

        if phi0 is None:
            assert L.contains_as_subfield(K0), "K0 is not a subfield of L"
            phi0 = K0.hom(L)
        else:
            assert phi0.applies_to(K0), "base map is not defined on K0"

        from mclf.fields.embeddings_of_standard_fields import (
            EmbeddingOfFunctionField)
        return EmbeddingOfFunctionField(self, L, image_gens, phi0)

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
            sage: k0 = standard_field(QQ)
            sage: R.<t> = QQ[]
            sage: k = standard_number_field(t^2+1, "i")
            sage: x, y = k0.polynomial_generators(["x", "y"])
            sage: F = standard_function_field(x^2+y^2); F
            standard function field in [x, y] over Rational Field,
            with equation x^2 + y^2

            sage: i = k.generator()
            sage: x, y = F.generators()
            sage: phi = k.hom(F, x/y)
            sage: F1, _, _ = F.with_new_constant_base_field(phi); F1
            Rational function field in x0 over Number Field in i with defining
            polynomial t^2 + 1, as finite extension of Rational function field
            in x0 over Number Field in i with defining polynomial t^2 + 1

        Note that `F_1` is returned as a finite extension. We can get the
        field with this extra information as follows::

            sage: F1.extension_field()
            standard rational function field in x0 over Number Field in i
            with defining polynomial t^2 + 1

            sage: k0 = standard_finite_field(4)
            sage: a = k0.generator()
            sage: t = k0.polynomial_generator("t")
            sage: k1 = k0.extension(t^3 + t^2 + t + a, "b")
            sage: F0 = standard_rational_function_field(k1, "x")
            sage: x = F0.generator()
            sage: y = F0.polynomial_generator("y")
            sage: F = F0.extension(y^2+x^3+a)
            sage: F_k0, _, _ = F.with_new_constant_base_field(k0); F_k0
            standard function field in [x0_, y_] over Finite Field in z2 of
            size 2^2, with equation y_^9 + x0_^2*y_^6 + x0_^4*y_^3 + x0_^6
             + (z2 + 1)*y_^6 + (z2 + 1)*x0_^4 + (z2)*y_^3 + (z2)*x0_^2
             + (z2 + 1)

        """
        from mclf.fields.standard_fields import (is_standard_field,
                                                 standard_field)
        from mclf.fields.embeddings_of_standard_fields import (
            embedding_of_standard_fields, EmbeddingOfStandardFields)
        F = self
        k = F.constant_base_field()

        if is_standard_field(phi0):
            # we demand that K1 is a natural subfield of k
            # there are only two possibilities
            k1 = phi0
            if not isinstance(k1, StandardField):
                k1 = standard_field(k1)
            assert k.contains_as_subfield(k1)
            phi0 = k1.hom(k)
        elif not isinstance(phi0, EmbeddingOfStandardFields):
            phi0 = embedding_of_standard_fields(phi0)
        # now phi0 is a embedding of standard fields

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

            - this has not yet been properly implemented

            - The resulting standard function field has in general a different
              original model! This may lead to problems and should be changed
              at some point.

        .. TODO::

            - finish implementation
            - Make sure the resulting standard function field has the same
              original model.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_field(GF(3))
            sage: x, y = k.polynomial_generators(["x", "y"])
            sage: F = standard_function_field(x^2 + y^2)
            sage: t = k.polynomial_generator("t")
            sage: K = k.extension(t^2 + 1)
            sage: phi = k.hom(K)
            sage: F.base_change(phi)
            Traceback (most recent call last):
            ...
            AttributeError: 'FiniteField_prime_modn_with_category' object has no attribute 'is_equal'

            sage: x = F.generators()[0]
            sage: y = F.generators()[1]
            sage: u = K.hom(F, x/y - 1)
            sage: F.base_change(phi, u)[0]
            Traceback (most recent call last):
            ...
            AttributeError: 'FiniteField_prime_modn_with_category' object has no attribute 'is_equal'


        """
        from sage.all import FunctionField
        F = self
        k = F.constant_base_field()
        assert phi.domain().is_equal(k), "the domain of phi\
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
                raise AssertionError("couldn't find the right factor")


class StandardRationalFunctionField(StandardFunctionField):
    r""" Return a rational function field.

    INPUT:

    either

    - ``K`` -- a rational function field,

    or

    - ``s`` -- an isomorphism of Sage function field `s:K\to F`,
      where `F` is a rational function field in standard form
    - ``t`` -- the inverse of `s`

    OUTPUT:

    the standard rational function field corresponding to the input.

    If a `K` is given as an instance of :class:`StandardRationalFunctionField`,
    we simply make a copy of all the data defining `K`.

    If the mutually inverse isomorphisms `s` and `t` are given, we take the
    domain of `s` as the original model, and the codoamin as the standard model.

    """

    def __init__(self, *args):
        if len(args) == 1 and isinstance(args[0],
                                         StandardRationalFunctionField):
            K = args[0].original_model()
            F = args[0].standard_model()
            K_to_F = args[0].from_original_model()
            F_to_K = args[0].to_original_model()
        elif len(args) == 1:
            K = args[0]
            # test input:
            assert is_standard_rational_function_field(K), "K is not \
                a rational function field in standard form"
            F = K
            from mclf.fields.standard_fields import identity_map
            F_to_K = identity_map(K)
            K_to_F = F_to_K
        elif len(args) == 2:
            K_to_F = args[0]
            F_to_K = args[1]
            K = K_to_F.domain()
            F = K_to_F.codomain()
        else:
            raise TypeError("wrong number of parameters")

        self._original_model = K
        self._standard_model = F
        self._from_original_model = K_to_F
        self._to_original_model = F_to_K

    def __repr__(self):
        return "standard rational function field in {} over {}".format(
            self.variable_name(), self.constant_base_field().subfield())

    def is_rational_function_field(self):
        r""" Return whether this field is a rational function field.

        This means that the standard model of this field is of the form
        `k(x)`, where `k` is the constant base field.

        """
        return True

    def embedding_of_rational_base_field(self):
        r""" Return the embedding of the rational base field into this
        function field.

        For a rational function field, this embedding is the identity.

        """
        if not hasattr(self, "_embedding_of_rational_base_field"):
            from mclf.fields.embeddings_of_standard_fields import(
                IdentityEmbedding)
            self._embedding_of_rational_base_field = IdentityEmbedding(self)
        return self._embedding_of_rational_base_field

    def rational_base_field(self):
        r""" Return the rational base field of this  function field.

        EXAMPLES:

            sage: from mclf import *
            sage: k = standard_finite_field(2)
            sage: F0 = standard_rational_function_field(k, "x")
            sage: F0.rational_base_field()
            Rational function field in x over Finite Field of size 2,
            as a subfield of Rational function field in x over Finite Field
            of size 2

        """
        if not hasattr(self, "_rational_base_field"):
            self._rational_base_field = self.as_subfield_of_itself()
        return self._rational_base_field

    def generator(self):
        r""" Return the standard generator of this rational base field.

        """
        return self.standard_model().gen()

    def generators(self):
        r""" Return the standard generators of this function field.

        Since this is a rational function field, we return a list with one
        element, the stnadard generator.

        """
        return [self.generator()]

    def variable_name(self):
        r""" Return the name of the standard generator of this rational
        function field.

        """
        return self.standard_model().variable_name()

    def variable_names(self):
        r""" Return the list of names of the standard generators of this
        function field.

        Since this is a rational function field, we return a list with one
        element, the name of the standard generator.

        """
        return [self.variable_name()]

    def is_constant(self, a):
        r""" Return whether the element `a` is a constant element
        of this rational function field.

        """
        return (a.numerator().degree() == 0
                and a.denominator().degree() == 0)

    def place(self, pi):
        r""" Return the place on this rationa function field with given
        caninical uniformizer.


        """
        from mclf.valuations.discrete_valuations_on_function_fields import (
            PlaceOnRationalFunctionField)
        return PlaceOnRationalFunctionField(self, pi)


class StandardNonrationalFunctionField(StandardFunctionField):
    r""" Return a nonrational function field.

    A function field `K` is called *nonrational* if its standard model is a
    finite extension of its rational base field of degree `>1`.

    INPUT:

    either

    - ``K`` -- a nonrational function field,

    or

    - ``s`` -- an isomorphism of Sage function field `s:K\to F`,
      where `F` is a nonrational function field in standard form
    - ``t`` -- the inverse of `s`

    OUTPUT:

    the standard nonrational function field corresponding to the input.

    If a `K` is given as an instance of
    :class:`StandardNonrationalFunctionField`,
    we simply make a copy of all the data defining `K`.

    If the mutually inverse isomorphisms `s` and `t` are given, we take the
    domain of `s` as the original model, and the codomain as the standard model.

    """

    def __init__(self, *args):
        if len(args) == 1 and isinstance(args[0],
                                         StandardNonrationalFunctionField):
            K = args[0].original_model()
            F = args[0].standard_model()
            K_to_F = args[0].from_original_model()
            F_to_K = args[0].to_original_model()
        elif len(args) == 1:
            K = args[0]
            # test input:
            assert is_rational_function_field(K), "K is not \
                a function field in standard form"
            F = K
            from mclf.fields.standard_fields import identity_map
            F_to_K = identity_map(K)
            K_to_F = F_to_K
        elif len(args) == 2:
            K_to_F = args[0]
            F_to_K = args[1]
            K = K_to_F.domain()
            F = K_to_F.codomain()
        else:
            raise TypeError("wrong number of parameters")

        self._original_model = K
        self._standard_model = F
        self._from_original_model = K_to_F
        self._to_original_model = F_to_K

        # as factoring of polynomials over nonrational function fields
        # is not implemented in Sage, we add our own implementation
        # to the standard model of our function field:
        from mclf.fields.factor_polynomial_over_function_field import (
            factor_polynomial_over_function_field)
        F._factor_univariate_polynomial = (
            lambda f: factor_polynomial_over_function_field(f.base_ring(), f))

    def __repr__(self):
        return "standard function field in {} over {}, with equation {}".format(
            self.generators(), self.constant_base_field().subfield(),
            self.bivariate_polynomial())

    def is_rational_function_field(self):
        r""" Return whether this field is a rational function field.

        This means that the standard model of this field is of the form
        `k(x)`, where `k` is the constant base field.

        """
        return False

    def embedding_of_rational_base_field(self):
        r""" Return the embedding of the rational base field into this
        function field.

        """
        if not hasattr(self, "_embedding_of_rational_base_field"):
            from mclf.fields.embeddings_of_standard_fields import (
                EmbeddingOfRationalBaseField)
            iota = EmbeddingOfRationalBaseField(self)
            self._embedding_of_rational_base_field = iota
        return self._embedding_of_rational_base_field

    def rational_base_field(self):
        r""" Return the rational base field of this  function field.

        EXAMPLES:

            sage: from mclf import *
            sage: k = standard_finite_field(2)
            sage: F0 = standard_rational_function_field(k, "x")
            sage: x = F0.generator()
            sage: y = F0.polynomial_generator("y")
            sage: F = F0.extension(y^2 + x^3 + 1, "y")
            sage: F.rational_base_field()
            Rational function field in x over Finite Field of size 2,
            as a subfield of Function field in y defined by y^2 + x^3 + 1

        """
        from mclf.fields.standard_subfields import standard_subfield
        if not hasattr(self, "_rational_base_field"):
            F0 = standard_subfield(self.embedding_of_rational_base_field())
            self._rational_base_field = F0
        return self._rational_base_field

    def generator(self):
        r""" Return the standard generator of this nonrational function field.

        The standard model of this function field is of the form

        .. MATH::

            F = k(x)[y | f(x,y)=0].

        We return the element `y` of `F`.

        """
        return self.standard_model().gen()

    def generators(self):
        r""" Return the standard generators of this nonrational function field.

        The standard model of this function field is of the form

        .. MATH::

            F = k(x)[y | f(x,y)=0].

        We return the list of elements [`x`, `y`] of `F`.

        """
        return [self.rational_base_field().generator(), self.generator()]

    def variable_names(self):
        r""" Return the name of the standard generators.

        The standard model of this function field is of the form

        .. MATH::

            F = k(x)[y | f(x,y)=0].

        We return the list of names of the elements `x, y` of `F`.

        """
        return [self.rational_base_field().variable_name(),
                self.variable_name()]

    def variable_name(self):
        r""" Return the name of the standard generator of this function field.

        OUTPUT:

        The vraible name for the standard generator of this function field over
        its rational base field.

        """
        return self.standard_model().variable_name()

    def polynomial(self):
        r""" Return the minimal polynomial of the standard generator over the
        rational base field.

        This is the irreducible, monic and univariate polynomial `f` over the
        rational base field `k(x)` such that the standard form of this
        function field is `F = k(x)[y\mid f(y)=0]`.

        """
        return self.standard_model().polynomial()

    def bivariate_polynomial(self):
        r""" Return the equation between the two standard generators of this
        function field.

        OUTPUT:

        the irreducible bivariate polynomial `f` defining the standard model,

        .. MATH::

            F = k(x)[ y | f(x,y)=0].

        """
        if not hasattr(self, "_bivariate_polynomial"):
            self._bivariate_polynomial = make_bivariate(self.polynomial())
        return self._bivariate_polynomial

    def as_polynomial(self, f, bivariate=False):
        r""" Return the polynomial representing the field element `f`.

        INPUT:

        - ``f`` -- an element of this function field `K`
        - ``bivariate`` -- a boolean (default: ``False``)

        OUTPUT:

        a polynomial `\tilde{f}` over the rational base field `k(x)` of `K`
        such that `f=\tilde{f}(y)`, where `y` is the standard generator of `K`
        over `k(x)`.

        """
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

        EXAMPLES::

            sage: from mclf import *
            sage: K0.<x> = FunctionField(QQ)
            sage: R.<y> = K0[]
            sage: K.<y> = K0.extension(y^2-x^3-1)
            sage: K = standard_field(K)
            sage: K.as_rational_function(x+y/x)
            (x^2 + y, x)

        """
        from sage.all import PolynomialRing, lcm
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

        To check this, we compute the mnimal polynomial of `a` over the
        rational base field and check whether all of its coefficients are
        constant.

        EXAMPLES::

            sage: from mclf import *
            sage: k = standard_finite_field(2)
            sage: x, y = k.polynomial_generators(["x", "y"])
            sage: K = standard_function_field(x^2 + y^3)
            sage: x, y = K.generators()
            sage: K.is_constant(x^2 + y^3 + 1)
            True
            sage: K.is_constant(y + x)
            False
            sage: K.is_constant(1/x)
            False

        """
        K0 = self.rational_base_field()
        f = self.minimal_polynomial(a)
        return all(K0.is_constant(f[i]) for i in range(f.degree()+1))


# ---------------------------------------------------------------------------

#                        helper functions

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
    from mclf.fields.standard_fields import (standard_field,
                                             is_in_standard_form, identity_map)
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


def is_standard_rational_function_field(K):
    r""" Return whether `K` is a rational function field in standard form.

    """
    from sage.categories.function_fields import FunctionFields
    from mclf.fields.standard_fields import is_in_standard_form
    return (K in FunctionFields() and K.base_field() is K
            and is_in_standard_form(K))


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
    from sage.all import PolynomialRing, lcm
    R = f.parent()
    K = R.base_ring()
    k = K.constant_base_field()
    A = PolynomialRing(k, [K.variable_name(), R.variable_name()])
    t, x = A.gens()
    d = lcm([f[i].denominator() for i in range(f.degree() + 1)])
    f = d*f
    F = sum(f[i].numerator()(t)*x**i for i in range(f.degree() + 1))
    return F
    return F
