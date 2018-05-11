r""" Points of type V on the Berkovich line.
============================================


"""


from sage.all import SageObject, cached_method, Infinity
from mclf.berkovich.berkovich_line import BerkovichLine




class TypeVPointOnBerkovichLine(SageObject):
    r"""
    A point of type V on the Berkovich line.

    A "point" `\eta` of type V on the Berkovich line `X^{an}` corresponds to a
    pair `(v,\bar{v})`, where `v` is a type-II-valuation and `\bar{v}` is a
    function field valuation on the residue field of `v`.  We call `v` the
    "major valuation" and `\bar{v}` the "minor valuation" associated to `\eta`.

    Note that `\eta` is not, properly speaking, a point on the analytic space
    `X^{an}`, but rather a point on the adic space `X^{ad}`.

    Equivalent ways to describe `\eta` are:

    - the rank-2-valuation given as the composition of `v` and `\bar{v}`
    - a "residue class" on `X^{an}`; more precisely, `\eta` corresponds to
      a connected component of `X^{an}-\{\xi\}`, where `\xi` is the
      type-II-point corresponding to `v` (and then `\xi` is the unique boundary
      point of the residue class)
    - an "open discoid": more precise, a pair `(\phi,s)`, where `\phi` is
      a rational function such that the open discoid

      .. MATH::

             D = \{ v \mid v(\phi) > s \}

      is the residue class corresponding to `\eta`. Moreover, either `\phi`
      of `1/\phi` is a monic, integral and irreducible polynomial in `x`
      or in `1/x`.
    - a "tangent vector" on `X^{an}`; more precisely a group homomorphism

      .. MATH::

          \partial: K(x)^* \to \mathbb{Z}

    with the following properties: let `(\phi,s)` be the discoid representation
    of `\eta`. We define, for `t\geq s`, the valuation `v_t` as the valuation
    corresponding to the boundary point of the open discoid `v(\phi)>t`. Then
    `\partial(f)` is the right derivative at `t=s` of the function

    .. MATH::

        t \mapsto v_t(f).

    Let `\xi_1` be a point of type II, and `\xi_2` a point of type I or II.
    Then we can define the point of type V `\eta:=d(\xi_1,\xi_2)` as the unique
    residue class with boundary point `\xi_1` containing `\xi_2`.

    INPUT:

    - ``xi0`` -- point of type II
    - ``xi1`` -- arbitrary point of X, distinct from xi0

    OUTPUT:

    The type-V-point corresponding to the connected component
    of `X^{an}-{\xi0}`` which contains `\xi1`.


    EXAMPLES:

    ::

        sage: from mclf import *
        sage: K = QQ
        sage: vK = K.valuation(2)
        sage: F.<x> = FunctionField(K)
        sage: X = BerkovichLine(F, vK)
        sage: xi1 = X.point_from_discoid(x,1)
        sage: xi2 = X.point_from_discoid(x^2+4,3)
        sage: eta = TypeVPointOnBerkovichLine(xi1, xi2)

    We see that ``eta`` represents an open disk inside the closed unit disk.
    ::

        sage: eta
        Point of type V given by residue class v(x + 2) > 1

    Here is an example of a type-V-point representing an open disk in the
    complement of the closed unit disk:
    ::

        sage: xi0 = X.gauss_point()
        sage: xi3 = X.point_from_discoid(x+2, 2, in_unit_disk=False)
        sage: eta = TypeVPointOnBerkovichLine(xi0, xi3)
        sage: eta
        Point of type V given by residue class v(1/x) > 0

    We check that ``xi0`` lies outside the open disk and ``xi3`` inside:
    ::

        sage: eta.is_in_residue_class(xi0)
        False
        sage: eta.is_in_residue_class(xi3)
        True

        sage: xi4 = X.point_from_discoid(x+2, 3, in_unit_disk=False)
        sage: TypeVPointOnBerkovichLine(xi3, xi4)
        Point of type V given by residue class v((2*x + 1)/x) > 2
        sage: TypeVPointOnBerkovichLine(xi4, xi3)
        Point of type V given by residue class v(x/(2*x + 1)) > -3

    """

    def __init__(self, xi0, xi1):

        X = xi0._X
        x = X._F.gen()
        self._X = X
        assert xi0.type() == "II", "xi0 must be a point of type II"
        assert not xi0.is_equal(xi1), "xi0 and xi1 must be distinct"
        self._xi0 = xi0
        self._v = xi0._v
        v0 = xi0.pseudovaluation_on_polynomial_ring()
        k_v = v0.residue_field()
        if not xi1.is_inductive():
            xi1 = xi1.approximation(xi0)
        v1 = xi1.pseudovaluation_on_polynomial_ring()
        if xi0.is_leq(xi1):
            # the Gauss point is not contained in the residue class
            # corresponding to eta
            if xi1.is_in_unit_disk():
                # now self represents an open discoid strictly contained in
                # the standard closed unit disk
                phi_pol = v0.equivalence_decomposition(v1.phi())[0][0]
                # phi_pol is a key polynomial for v_0
                self._phi_pol = phi_pol
                phib = normalized_reduction(v0, phi_pol)
                self._vb = k_v.valuation(phib(k_v.gen()))
                phi = phi_pol(x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "contained_in_unit_disk"
            else:
                # now self represents an open discoid in the complement
                # of the closed unit disk
                phi_pol = v0.equivalence_decomposition(v1.phi())[0][0]
                self._phi_pol = phi_pol
                phib = normalized_reduction(v0, phi_pol)
                self._vb = k_v.valuation(phib(k_v.gen()))
                phi = phi_pol(1/x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "disjoint_from_unit_disk"
        else:
            if xi0.is_in_unit_disk():
                # now self represents the complement of a closed discoid
                # properly contained in the standard closed unit disk.
                # In particular, the residue class contains Infinity,
                # and 0 lies in its complement.
                self._vb = k_v.valuation(1/k_v.gen())
                phi_pol = v0.phi()
                self._phi_pol = phi_pol
                phi = 1/phi_pol(x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "overlaps_with_unit_disk"
            else:
                # now self represents an open discoid which properly contains
                # the standard closed unit disk
                self._vb = k_v.valuation(1/k_v.gen())
                phi_pol = v0.phi()
                self._phi_pol = phi_pol
                phi = 1/phi_pol(1/x)
                self._phi = phi
                self._s = xi0.v(phi)
                self._type = "contains_unit_disk"

    def __repr__(self):

        return "Point of type V given by residue class v(%s) > %s"%self.open_discoid()

    def X(self):
        """
        Return the Berkovich line underlying the point.
        """
        return self._X


    def boundary_point(self):
        """ Return the boundary point of the type-V-point. """
        return self._xi0


    def point_inside_residue_class(self):
        """
        Return some point inside the residue class corresponding to the point.
        """

        phi, s = self.open_discoid()
        if self._type == "contained_in_unit_disk":
            xi = self.X().point_from_discoid(self._phi_pol, Infinity)
        elif self._type == "disjoint_from_unit_disk":
            xi = self.X().point_from_discoid(self._phi_pol, Infinity, False)
        elif self._type == "overlaps_with_unit_disk":
            xi = self.X().infty()
        else:
            xi = self.X().gauss_point()
        assert self.is_in_residue_class(xi), "xi does not lie in the residue class"
        return xi


    def major_valuation(self):
        return self._v

    def minor_valuation(self):
        return self._vb

    def is_in_residue_class(self, xi):
        r""" Test whether ``xi`` lies in the residue class of ``self``.

        INPUT:

        - ``xi`` -- a point on the Berkovich line underlying the type-V-point

        OUTPUT:

        ``True`` if ``xi`` lies in the residue class corresponding to ``self``

        EXAMPLES:

::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = K.valuation(2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: xi1 = X.point_from_discoid(x,1)
            sage: xi2 = X.point_from_discoid(x^2+4,3)
            sage: eta = TypeVPointOnBerkovichLine(xi1, xi2)
            sage: eta.is_in_residue_class(xi2)
            True
            sage: eta.is_in_residue_class(xi1)
            False


        """

        return xi.v(self._phi) > self._s

    def open_discoid(self):
        r""" Return the representation of self as an open discoid.

        INPUT:

        - self: a point of type V on a Berkovich line

        OUTPUT:

        a pair `(\phi, s)`, where `\phi` is a rational function and `s` a
        rational number is such that

        .. MATH::

               D = \{ v\in X \mid v(\phi) > s \}

        is the open discoid representing the type-V-point ``self``.

        Either `\phi` of `1/\phi` is a monic, integral and strongly irreducible
        polynomial in `x` or in `1/x`.
        """

        return self._phi, self._s


    # this function is maybe not so useful..
    def point_inside_discoid(self, t):
        r"""
        Return the point inside the residue class at the value `t`.

        The type-V-point corresponds to an open discoid defined by

        .. MATH::

                  v(\phi) > s.

        For for a rational number `t>s` we can define the type-II-point
        `\xi_t` corresponding to the closed discoid defined by

        .. MATH::

                 v(\phi) >= t.

        If `t=\infty` we obtain the type-I-point corresponding to `\phi=0`.

        INPUT:

        - ``t`` -- a rational number or Infinity

        OUTPUT:

        The point `\xi_t` inside the residue class corresponding to the closed
        discoid defined by `v(\phi) >= t`.

        If `t <= s` then an error is raised.

        """

        eta = self
        X = eta.X()
        phi,s = eta.open_discoid()
        assert t > s, "t must be > s"

        if eta._type == "contained_in_unit_disk":
            return X.point_from_discoid(eta._phi_pol, t)
        elif eta._type == "disjoint_from_unit_disk":
            return X.point_from_discoid(eta._phi_pol, t, in_unit_disk=False)
        else:
            raise NotImplementedError





    def derivative(self, f):
        r"""
        Return the "derivative" of ``f`` with respect to ``self``.

        Here we interpret the type-V-point as a 'tangent vector', more precisely
        as a homomorphism

        .. MATH::

                    \partial: K(x)^* \to \mathbb{Z}

        with the following property. Assume that `\eta=` ``self`` is represented
        by the open discoid `D_\eta = \{ v \mid v(\phi)> s \}`. Set

        .. MATH::

               v_t = [v, v_t(\phi) = t],

        for `t\geq s`.  Then `\partial(f)` is the right derivative
        at `t=s` of the function

        .. MATH::

            t \mapsto v_t(f),

        for all `f \in K(x)`.

        Alternative, we have that

        .. MATH::

            \partial(f) = \deg_\eta(f)/\deg_\eta(\phi),

        where `\deg_\eta(f)` denotes the degree of the divisor of `f`
        restricted to the open discoid `D_\eta`.

        WARNING: the following is not quite true; the formula has to be
        corrected by some ramification index:

        We remark that for rational functions `f` such that `v(f)=0` we have

        .. MATH::

             \partial(f) = \bar{v}(\bar{f}).

        Here `(v,\bar{v})` is the pair of valuations corresponding to `\eta`.


        INPUT:

        - ``f`` -- a nonzero element of the function field `K(x)`

        OUTPUT:

        The "right derivative" of the valuative function `v\mapsto v(f)`
        at ``self``.

        EXAMPLES:

        ::

            sage: from mclf import *
            sage: K = QQ
            sage: vK = K.valuation(2)
            sage: F.<x> = FunctionField(K)
            sage: X = BerkovichLine(F, vK)
            sage: xi1 = X.point_from_discoid(x^2+2, 1)
            sage: xi2 = X.point_from_discoid(x^2+2, 2)
            sage: eta = TypeVPointOnBerkovichLine(xi1, xi2)
            sage: eta
            Point of type V given by residue class v(x^2 + 2) > 1
            sage: eta.derivative(x^2+2)
            1
            sage: eta.derivative(x^4+4)
            2

        """

        eta = self
        X = eta._X
        F = X._F
        x = F.gen()
        xi_g = X.gauss_point()
        assert f.parent() is F, "f must lie in the function field of X"
        assert not f.is_zero(), "f must not be zero"

        phi, s = eta.open_discoid()
        if not eta.is_in_residue_class(xi_g):
            # now phi should be a monic polynomial in x or in 1/x
            if phi.denominator().is_one():
                # now eta corresponds to an open discoid properly contained
                # in the closed unit disk
                return self.derivative_of_polynomial(f.numerator())-self.derivative_of_polynomial(f.denominator())
            else:
                # now eta corresponds to an open discoid inside the complement
                # of the closed unit disk
                f = F.hom([1/x])(f)
                return self.derivative_of_polynomial(f.numerator())-self.derivative_of_polynomial(f.denominator())
        else:
            # now D_eta contains the Gauss point
            if eta.major_valuation()(x) >= 0:
                # now D_eta is the complement of a closed disk properly
                # contained in the unit disk
                v0 = eta._xi0.pseudovaluation_on_polynomial_ring()
                return -v0.effective_degree(f.numerator()) + v0.effective_degree(f.denominator())
            else:
                # now D_eta is the complement of a closed disk disjoint from
                # the unit disk
                f = F.hom([1/x])(f)
                v0 = eta._xi0.pseudovaluation_on_polynomial_ring()
                return - v0.effective_degree(f.numerator()) + v0.effective_degree(f.denominator())


    def derivative_of_polynomial(self, f):

        v = self._xi0.pseudovaluation_on_polynomial_ring()
        w = v.augmentation(self._phi_pol, v(self._phi_pol), check=False)
        v_list = w.valuations(f)
        val, pos = min((val, pos) for (pos, val) in enumerate(v_list))
        # now pos is the index of the first item in v_list where the minimum ist attained
        return pos

    def left_derivative(self, f):
        r"""
        Return the left derivative of ``f`` with respect to ``self``.

        INPUT:

        - ``f`` -- an element of the polynomial ring `K[x]` or of
                the function field `K(x)`

        OUTPUT:

        The left derivative of the valuative function

        .. MATH::

                H_f: v \mapsto v(f)

        at `\eta=` ``self``. If \eta` lies in the closed unit disk and `f`
        is a polynomial in `x` then this left derivative is equal to the
        'effective degree' of `f` with respect to the major valuation of `\eta`,
        as defined by MacLane.

        """

        if hasattr(f, "numerator"):
            return self.left_derivative_of_polynomial(f.numerator()) - self.left_derivative_of_polynomial(f.denominator())
        else:
            return self.left_derivative_of_polynomial(f)

    def left_derivative_of_polynomial(self, f):

        v = self._xi0.pseudovaluation_on_polynomial_ring()
        return v.effective_degree(f)

#--------------------------------------------------------------------------

def normalized_reduction(v, f):
    r""" Return the normalized reduction of ``f`` with respect to ``v``.

    INPUT:

    - ``v`` -- an inductive valuation on `K[x]`
    - ``f`` -- an element of `K[x]`

    OUTPUT:

    The normalized reduction of ``f`` with respect to ``v``, defined as follows:
    let `g\in K[x]` be an equivalence unit for ``v`` such that `v(g)=-v(f)`.
    Then the *normalized reduction* is defined as the image of `fg` in the residue
    ring of `v`. The result is only well defined up to multiplication with
    a constant.
    THIS IS NOT WELL DEFINED: IN GENERAL, `g` AS ABOVE DOES NOT EXIST!
    """

    r = v(f)
    m = abs(r.denominator())
    fb = v.reduce(f**m*v.equivalence_unit(-m*r))
    Fb = fb.factor()
    fb = Fb[0][0]
    return fb
