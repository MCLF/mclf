"""
         Factoring univariate polynomials over functions fields
         ======================================================

"""

from sage.arith.all import lcm, gcd


def factor_polynomial_over_function_field(K, f):
    r"""
    Factor the polynomial f over the function field K.

    INPUT:

    - ``K`` -- a global function field
    - ``f`` -- a nonzero univariate polynomial over ``K``

    OUTPUT: the complete factorization of ``f``

    """
    f = f.change_ring(K)
    if K is K.rational_function_field():
        return f.factor()

    K0 = K.rational_function_field()
    k = K0.constant_base_field()
    old_name = f.variable_name()
    if (K.variable_name() == old_name or
            K0.variable_name() == old_name or
            hasattr(k, "variable_name") and k.variable_name() == old_name):
        # replace x with x1 to make the variable names distinct
        f = f.change_variable_name(old_name + "1")
    F, d = to_trivariate_polynomial(K, f)
    R = F.parent()
    G = R(defining_polynomial(K))
    factorization = []
    g = f
    J = R.ideal(F, G)
    for Q, P in J.primary_decomposition_complete():
        prime_factor = prime_factor_from_prime_ideal(K, P)
        if prime_factor.degree() > 0:
            e = 0
            while True:
                q, r = g.quo_rem(prime_factor)
                if r == 0:
                    g = q
                    e += 1
                else:
                    break
            factorization.append((prime_factor, e))
    assert g.degree() == 0, "f did not factor properly"
    from sage.structure.factorization import Factorization
    ret = Factorization(factorization, g[0])
    return ret


def roots_of_polynomial_over_function_field(K, f):
    r""" Return the set of roots of a polynomial over a function field.

    """
    roots = []
    for g, _ in factor_polynomial_over_function_field(K, f):
        if g.degree() == 1:
            roots.append(-g[0])
    assert all(f(a).is_zero() for a in roots), "something went wrong"
    return roots


def defining_polynomial(K):
    r"""
    Return the defining polynomial of K, as a bivariate polynomial.

    INPUT:

    - ``K`` -- a function field, given as an extension of a rational function field

    OUTPUT: a bivariate polynomial `g` over the constant base field `k` of K
    such that `K` is the fraction field of `k[y, x]/(g)`. Here `x` is the
    generator of the rational function field `K_0` from which `K` was created,
    and `y` is the generator of `K`.

    """
    return K.base_field()._to_bivariate_polynomial(K.polynomial())[0]


def to_bivariate_polynomial(K, a):
    r"""
    Convert ``a`` from an element of ``K`` to a bivariate polynomial and a denominator.

    INPUT:

    - ``K`` -- a function field, given as a finite extension of a rational function field.
    - ``a`` -- an element of ``K``

    OUTPUT:

    - a bivariate polynomial F
    - a univariate polynomial d

    such that `a = F(y, x)/d(x)`.

    """
    v = a.list()
    denom = lcm([c.denominator() for c in v])
    S = denom.parent()
    y, x = S.base_ring()['%s,%s' % (K.variable_name(),
                                    K.base_field().variable_name())].gens()
    phi = S.hom([x])
    F, d = sum([phi((denom * v[i]).numerator()) *
               y**i for i in range(len(v))]), denom
    return F, d


def to_trivariate_polynomial(K, f):
    r"""
    Convert ``f`` from a univariate polynomial over K into a trivariate
    polynomial and a denominator.

    INPUT:

    - ``K`` -- a function field
    - ``f`` -- univariate polynomial over K

    OUTPUT:

    - trivariate polynomial F, denominator d

    Here `F` is a polynomial in `k[x, y, z]` and d a polynomial in `k[x]`.

    """
    v = [to_bivariate_polynomial(K, c) for c in f.list()]
    denom = lcm([b for a, b in v])
    S = denom.parent()
    k = S.base_ring()
    z, y, x = k['%s,%s,%s' % (f.parent().variable_name(), K.variable_name(),
                K.base_field().variable_name())].gens()
    F = z.parent().zero()
    for i in range(len(v)):
        a, b = v[i]
        F += (denom(x) * a(y, x) / b(x)).numerator() * z**i
    d = denom(x)
    return F, d


def prime_factor_from_prime_ideal(K, P):
    r"""
    Return the univariate polynomial over K corresponding to the prime ideal P.

    INPUT:

    - ``K`` -- a function field
    - ``P`` -- a prime ideal of a multivariate polynomial ring

    OUTPUT: a monic irreducible polynomial `f` over `K`.
    We assume that `P` is a prime ideal of `k[z, y, x]` and that
    `K = k(y, x | g(y,x) = 0)`. Then `f` is a generator of the ideal generated
    by `P` in `K[z]`.

    """
    R = P.ring()
    S = K['%s' % R.variable_names()[0]]
    z = S.gen()
    y = K.gen()
    x = K.base_field().gen()
    generators = [f(z, y, x) for f in P.gens()]
    return S(gcd(generators)).monic()
