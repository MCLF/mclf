# Testing ground for ``FieldExtensions``
# ======================================

from sage.rings.function_field.constructor import FunctionField


def create_finite_function_field_extension(phi):
    r""" Return a finite extension of function fields.

    INPUT:

    - ``phi`` -- an injective morphisms between two function fields, say
      `\phi:F\to M`, such that `M` is finite over `\phi(F)`

    OUTPUT:

    A triple `(F_1,\phi_1},\psi_1)`, where `F_1/F`
    is a simple finite extension, `\phi_1:F_1\to M` is an isomorphism
    lifing `\phi` and `\psi_1` is the inverse of `\phi_1`.

    The function fields `F, M` may have distinct constant base fields `K, L`.
    It follows from the assumptions that the restriction of `\phi` to `K` is
    an embedding into `L`.

    """
    F = phi.domain()
    M = phi.codomain()
    F0 = F.base_field()
    K = F0.constant_base_field()
    L = M.constant_base_field()
    assert K.is_subring(L), "K must be a subfield of L"
    x = F0.gen()
    y = F.gen()

    # FL = base_change_of_function_field(F, L)
    # FL0 = FL.base_field()

    # t = phi(FL0.gen())
    # phi1, psi1 = subfield_of_function_field(F2, t)
    # this doesn't work yet


def finite_extension_of_function_field(F, equations):
    r""" Return a simple finite extension of a function field.

    INPUT:

    - ``F`` -- a function field
    - ``equations`` -- a list of irreducible polynomials over `F`

    OUTPUT:

    A pair (`E`, ``generators``), where `E` is a finite simple extension of `F`,
    and ``generators`` is a list `(\alpha_1,\ldots,\alpha_r)` of elements of `E`
    which generate the extension `E/F` and such that `\alpha_i` is a root of the
    `i`-th polynomial in ``equations``.

    """
    pass


def base_change_of_function_field(F, L):
    r""" Return the base change of F to the field of constants L.

    INPUT:

    - ``F`` -- a function field, with field of constants `K`
    - ``L`` -- a field extension of `K`

    OUTPUT: the function field `F_L`, which is the product of `F` and `L` over
    `K`, considered as a function field with constant base field `L`.

    We assume that `F` and `L` are linearly disjoint over `K`. Otherwise, an
    error is raised.

    """
    F0 = F.base_field()
    K = F0.constant_base_field()
    assert K.is_subring(L)
    if F == F0:
        return FunctionField(L, F.var_name())

    F0L = FunctionField(L, F0.variable_name())
    f = F.polynomial().change_ring(F0L)
    assert len(f.factor()) == 1, "F and L have to be linearly disjoint over K."
    return F0L.extension(f, F.variable_name())


def subfield_of_function_field(F, t):
    r""" Return a new presentation of the function field F as finite extension
    of given subfield.

    INPUT:

    - ``F`` -- a function field
    - ``t`` -- a transcendential element of `F`

    Let `K` denote the constant base field of `F`.

    OUTPUT: a pair `(\phi,\psi)` of inverse isomorphisms of function fields

    .. MATH::

        \phi: F_1\to F, \quad \psi=\phi^{-1}:F\to F_1,

    where `F_1=K(t,z)` is a function field with base field the rational function
    field `K(t)` and the isomorphism `\phi` sends `t\in F_1` to the given element
    `t\in F`.

    """
    from sage.rings.function_field.constructor import FunctionField
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    K = F.constant_base_field()
    F0 = F.base_field()
    if F == F0:
        # F is a rational function field
        F0 = FunctionField(K, "t")
        t1 = F0.gen()
        R = PolynomialRing(F0, ["z"])
        g = R(t.numerator())
        h = R(t.denominator())
        f = g - t1*h
        F1 = F0.extension(f)
        z1 = F1.gen()
        phi0 = F0.hom(t)
        phi = F1.hom(F.gen(), phi0)
        psi = F.hom(z1)
        return phi, psi
    else:
        # F is a finite simple extension of the rational function field F0
        A = PolynomialRing(K, ["X", "Y", "T", "Z"])
        X, Y, T, Z = A.gens()

        # construction equation between generators of F
        x = F0.gen()
        y = F.gen()
        f = F.polynomial()
        assert f(y) == 0
        from sage.arith.functions import lcm
        h = lcm([c.denominator() for c in f])
        f = h*f
        g1 = sum([f[i].numerator()(X)*Y**i for i in range(f.degree()+1)])
        assert g1(x, y, T, Z) == 0

        # construct relation between x, y and t
        t_coeffs = t.list()
        h = lcm([c.denominator() for c in t_coeffs])
        t_coeffs = [(h*c).numerator() for c in t_coeffs]
        g2 = h(X)*T - sum(t_coeffs[i](X)*Y**i for i in range(len(t_coeffs)))
        assert g2(x, y, t, Z) == 0

        # construct relation between x, y and z:=x+y
        z = x + y
        g3 = Z - X - Y
        assert g3(x, y, T, z) == 0

        # find the relation between t and z
        J = A.ideal(g1, g2, g3)
        G = J.elimination_ideal([X, Y]).gens()[0]
        for g, _ in G.factor():
            if g(X, Y, t, z) == 0:
                break
        else:
            raise ValueError("We did not find a good factor of G")
        assert len(g.factor()) == 1

        # construct the function field F1
        F0 = FunctionField(K, "t")
        t1 = F0.gen()
        R = PolynomialRing(F0, "z")
        z1 = R.gen()
        g = g(0, 0, t1, Z).univariate_polynomial()(z1).monic()
        F1 = F0.extension(g)
        z1 = F1.gen()

        # wrote x,y as functions of t,z
        R = PolynomialRing(F1, ["X"])
        X = R.gen()
        G1 = g1(X, z1 - X, t1, z1)
        G2 = g2(X, z1 - X, t1, z1)
        G3 = G1.gcd(G2)
        assert G3.degree() == 1
        x1 = - G3[0]
        y1 = z1 - x1
        assert g1(x1, y1, T, Z) == 0

        # construct the morphism phi:F1-->F
        phi0 = F0.hom(t)
        phi = F1.hom(z, phi0)

        # construct the inverse morphism psi:F-->F1
        psi0 = F.base_field().hom(x1)
        psi = F.hom(y1, psi0)

        assert phi(psi(x)) == x
        assert phi(psi(y)) == y
        assert psi(phi(t1)) == t1
        assert psi(phi(z1)) == z1

        return phi, psi
