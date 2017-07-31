
r"""
Smooth projective curves over a field.

Let `k` be a field and `F/k` a finitely generated field extension of transcendence 
degree one (i.e. a 'function field over `k`'). Then there exists a smooth projective 
curve `Y` over `Spec(k)` with function field `F`, unique up to unique isomorphism.
The set of closed points on `Y` are in natural bijection with the set of discrete
valuations on `F` which are trivial on `k`. See 
- R. Hartshorne, Algebraic Geometry, Theorem I.6.9.

The classes in this module provide the definition and some basic functionality for 
such curves.

A curve `Y` is defined via its function field `F_Y`. Points are represented by 
the corresponding valuations on `F_Y`, and no smooth projective model of `Y` is actually
computed. However, we do compute a list of 'coordinate functions' `x_1,..,x_n` which
separate all points, meaning that the closure of the rational map from `Y` to projective
space of dimension `n` is injective. Then a (closed) point `P` on `Y` can also be represented 
by the tupel `(x_1(P),..,x_n(P))`.

A function field in Sage is always realized as a simple separable extension of a rational 
function field. Geometrically, this means that the curve `Y` is equipped with a finite 
separable morphism `phi:Y-->X`, where `X` is the projective line over the base field `k`.

The base field `k` is called the 'constant base field' of the curve, and it is part 
of the data. We do not assume that the extension `F_Y/k` is regular (i.e. that `k` is 
algebraically closed in `F_Y`). Geometrically this means that the curve `Y` may not be
absolutely irreducibel as a `k`-scheme. The 'field of constants' of `Y` is defined as 
the algebraic closure of `k` inside `F_Y`. It is a finite extension `k_c/k`. If we regard
`Y` as a curve over its fields of constants then it becomes absolute irreducible.

It would be interesting to have an efficient algorithm for computing the field of constants,
but it seems that this has not been implemented in Sage yet. 
To compute the genus of `Y` it is necessary to know at least the degree `[k_c:k]`.
We have implemented a probabilistic algorithm for computing the degree `[k_c:k]' 
(if `k` is finite, this determines `k_c` uniquely). 


AUTHORS:

- Stefan Wewers (2016-11-11): initial version


EXAMPLES::

    sage: from mclf import *
    sage: K = GF(2)
    sage: FX.<x> = FunctionField(K)
    sage: R.<T> = FX[]
    sage: FY.<y> = FX.extension(T^2+x^2*T+x^5+x^3)
    sage: Y = SmoothProjectiveCurve(FY)
    sage: Y
    The smooth projective curve over Finite Field of size 2 with Function field in y defined by y^2 + x^2*y + x^5 + x^3.
    sage: Y.genus()
    1
    sage: Y.zeta_function()
    (2*T^2 + T + 1)/(2*T^2 - 3*T + 1)


"""

#*****************************************************************************
#       Copyright (C) 2016 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.structure.sage_object import SageObject
from sage.rings.all import Infinity, ZZ
from sage.misc.prandom import randint
from sage.rings.power_series_ring import PowerSeriesRing
from mac_lane import *


class SmoothProjectiveCurve(SageObject):
    
    def __init__(self, F):
        self._function_field = F
        self._constant_base_field = F.constant_base_field()       #  F/k need not be regular
        # self._field_of_constants_degree = 1
        self._coordinate_functions = self.coordinate_functions()
        self._field_of_constants_degree = self.field_of_constants_degree()
        
    def __repr__(self):
        return "The smooth projective curve over %s with %s."%(self._constant_base_field, self._function_field)
    
    def point(self, v):
        """ Returns the point on the curve corresponding to v.
        
        INPUT:
        
        - v -- a discrete valuaton on the function field of the curve
        
        OUTPUT:
        
        The point on the curve corresponding to v.
        
        """
        
        return PointOnSmoothProjectiveCurve(self, v)
    
    
    @cached_method
    def field_of_constants_degree(self):
        """ Return the degree of the field of constants over the constant base field.
        
        If F is the function field of self and k the constant base field, then the 
        field of constansts k_c is the algebraic closure of k in F. 
        
        We use a probabilistic algorithms for computing the degree [k_c:k].
        
        """
        
        F = self._function_field
        k = self._constant_base_field
        P = self.random_point()
        n = P.absolute_degree()
        count = 0
        while n>1 and count < 10:
            P = self.random_point()
            n = n.gcd(P.absolute_degree())
            count += 1
        return n
    
    def function_field(self):
        """ Return the function field of self.
        
        """
        
        return self._function_field
    
    @cached_method
    def coordinate_functions(self):
        """ Return a list of coordinate functions.
        
        By 'list of coordinate functions' we mean elements x_i in 
        the function field, such that the map P --> [x_1(P):..:1]
        from the set of points to projective space is injective.
        But the image of this map may not be a smooth model of self.
        """
        F = self._function_field
        F0 = F.base_field()
        if F0 is F:
            return [F.gen()]
        
        # F is an extension of a rational ff F0
        ret = [F0.gen(), F.gen()]     # the coordinates of the affine plane model
        v0 = FunctionFieldValuation(F0, 1/F0.gen()) 
        V = v0.extensions(F)          # list of points at infinity
        separate_points(ret, V)       # make sure they are separated
        D = F.polynomial().discriminant().numerator()
        V0 = [FunctionFieldValuation(F0, g) for g, m in D.factor()]
        for v0 in V0:
            separate_points(ret, v0.extensions(F))
            # separate all intersection points of the affine plane model
        return ret    
        
        
    def random_point(self):
        """ Return a random point on self.
        
        """
        
        
        F = self._function_field
        F0 = F.base_field()
        R = F0._ring
        f = R.random_element(degree=(1,3)).factor()[0][0](F0.gen())
        v0 = FunctionFieldValuation(F0, f)
        V = v0.extensions(F)
        v = V[randint(0, len(V)-1)]
        return PointOnSmoothProjectiveCurve(self, v)
        
    
    def principal_divisor(self, f):
        """ Return the principal divisor of f.
        
        INPUT:
        
        - f: a nonzero element of the function field of self
        
        OUTPUT:
        
        the principal divisor D =(f)
        """
        
        F = self._function_field
        F0 = F.base_field()
        is_rational = (F is F0) 
        D = {}
        for g, m in f.norm().factor():
            v0 = FunctionFieldValuation(F0, g)
            if is_rational:
                P = PointOnSmoothProjectiveCurve(self, v0)
                a = P.coordinates()
                D[a] = (P, P.order(f))
            else:
                for v in v0.extensions(F):
                    P = PointOnSmoothProjectiveCurve(self, v)
                    a = P.coordinates()
                    D[a] = (P, P.order(f))
        v0 = FunctionFieldValuation(F0, F0.gen()**(-1))
        if is_rational:
            P = PointOnSmoothProjectiveCurve(self, v0)
            a = P.coordinates()
            D[a] = (P, P.order(f))
        else:
            for v in v0.extensions(F):
                P = PointOnSmoothProjectiveCurve(self, v)
                a = P.coordinates()
                D[a] = (P, P.order(f))
        assert self.degree(D) == 0, "Something is wrong: the degree of (f) is not zero!"        
        return D        
        
    
    def divisor_of_zeroes(self, f):
        """ Return the divisor of zeroes of f.
        """
        
        D = self.principal_divisor(f)
        ret = []
        for x,m in D:
            if m > 0: ret.append((x,m))
        return ret

    def divisor_of_poles(self, f):
        """ Return the divisor of poles of f.
        """
        
        D = self.principal_divisor(f)
        ret = []
        for x,m in D:
            if m < 0: ret.append((x,-m))
        return ret
    
    def degree(self, D):
        """ Return the degree of the divisor D.
        
        Note that the degree of D is defined relative to the 
        field of constants of the curve.
        """
        
        deg = ZZ.zero()
        for P, m in D.values():
            deg += m*P.degree()
        return deg
    
    def canonical_divisor(self):
        pass
    
    @cached_method
    def ramification_divisor(self):
        """ Return the ramification divisor of self.
        
        The function field of self is a finite separable extension
        of a rational function field. Geometrically, this means that
        the curve Y is represented as a separable cover of 
        the projective line X. The ramification divisor of this cover
        is supported in the set of ramification points of this cover.
        Sheaf theoretically, the divisor represents the sheaf of relative
        differentials Omega_{Y/X}. See:
        - Hartshorne, Algebraic Geometry, Definition IV.2.
        """
        
        FY = self._function_field
        FX = FY.base_field()
        R = {}
        if FX is FY:
            return R   # the cover is trivial, hence R=0
        supp = []      # compute the support of R
        d = FY.gen().minimal_polynomial('T').discriminant()
        for f, m in d.factor():
            supp += FunctionFieldValuation(FX, f).extensions(FY)
        supp += FunctionFieldValuation(FX,1/FX.gen()).extensions(FY)
        for v in supp:
            P = PointOnSmoothProjectiveCurve(self, v)
            t = v.uniformizer()
            F = t.minimal_polynomial('T')            
            Ft = F.derivative()(t)
            x = FX.gen()
            dx = FX.derivation()
            if P.order(x)<0:
                der = lambda f: -x**2*dx(f)
            else:
                der = dx
            Fx = F.map_coefficients(der)(t)
            m = P.order(Ft) - P.order(Fx)
            R[P._coordinates] = (P, m)
        return R    
    
    @cached_method
    def genus(self):
        """ Return the genus of the curve.
        
        The genus of the curve is defined as the dimension of
        the cohomology group `H^1(X,OO_X)`, as a vector space
        *over the field of constants k_c*. 
        
        The genus g of Y is computed using the Riemann-Hurwitz formula,
        applied to the cover phi:Y-->X corresponding to the realization
        of the function field of Y as a finite separable extension of 
        a rational function field. See:
        - Hartshorne, Algebraic Geometry, Corollary IV.2.4
        
        """
        FY = self._function_field
        if FY.base_field() is FY:
            return 0
        n = FY.polynomial().degree()/self._field_of_constants_degree
        r = self.degree(self.ramification_divisor())
        return ZZ(-n + r/2 +1)   
    
    def count_points(self, d):
        """ Return number of points of degree <= d.
        
        INPUT:
        
        - d: an interger >=1
        
        OUTPUT:
         
        a list N, where N[i] is the number of points on self
        of *absolute* degree i, for i=1,..,d.
        
        Recall that the absolute degree of a point if the degree of 
        the residue field of the point over the constant base field
        (*not* over the field of constants). 
        
        This is a very slow realization and should be improved at some point. 
        """
        
        F = self._function_field
        F0 = F.base_field()
        K = self._constant_base_field
        assert K.is_finite(), "Base field must be finite."
        p = K.characteristic()
        d0 = K.degree()
        q = K.cardinality()
        assert q == p**d0        
        
        # compute all nonconstant irreducible polynomials of degree <= g
        R = F0._ring
        x = R.gen()
        polys = set([x])
        for k in range(1,d+1):
            G = (x**(q**k-1)-1).factor()
            for g, e in G:
                polys.add(g)
        # count points
        N = [0]*(d+1)
        for g in polys:
            v0 = FunctionFieldValuation(F0, g)
            for v in v0.extensions(F):
                L = v.residue_field()
                try:
                    from_L, to_L, L = L.absolute_extension()
                except AttributeError:
                    pass
                k = ZZ(L.degree()/d0)
                if k <= d:
                    N[k] += 1
        v0 = FunctionFieldValuation(F0, 1/F0.gen())
        # points at infinity
        for v in v0.extensions(F):
            L = v.residue_field()
            try:
                from_L, to_L, L = L.absolute_extensions()
            except AttributeError:
                pass
            k = ZZ(L.degree()/d0)
            if k <= d:
                N[k] += 1  
        return N
    
    @cached_method
    def zeta_function(self, var_name='T'):
        """ Return the Zeta function of the curve.
        
        For any scheme X of finite type over ZZ, the arithmetic 
        zeta funtion of X is defined as the product
        
            zeta(X,s) := \prod_x 1/(1-N(x)^(-s)),
            
        where x runs over over all closed points of X and N(x)
        denotes the cardinality of the residue field of x.
        
        If X is a smooth projective curve over a field with 
        q elements, then zeta(x,s) = Zeta(X,q^(-s)), 
        where Zeta(X,T) is a rational function in T of the form
        
            Zeta(X,T) =  P(T)/(1-T)/(1-qT),
            
        for a polynomial P of degree 2g, with some extra properties
        reflecting the Weil conjectures. See:
        - Hartshorn, Algebraic Geometry, Appendix C, Section 1.
        
        Note that that this makes only sense if the constant base 
        field of self is finite, and that Zeta(X,T) depends on the
        choice of the constant base field. (unlike the function
        zeta(X,s)).
        """
        
        K = self._constant_base_field
        q = K.order()
        g = self.genus()
        S = PowerSeriesRing(ZZ, var_name, g+1)
        N = self.count_points(g)
        Z_series = S(1)
        for k in range(1,g+1):
            Z_series *= (1-S.gen()**k)**(-N[k])
        P = (Z_series*(1-S.gen())*(1-q*S.gen())).polynomial()
        c = range(2*g+1)
        for k in range(g+1):
            c[k] = P[k]
        for k in range(g+1,2*g+1):
            c[k] = c[2*g-k]*q**(k-g)
        R = P.parent()
        return R(c)/(1-R.gen())/(1-q*R.gen())

    
    def points_with_coordinates(self, a):
        """ Return all points with given coordinates.
        
        INPUT:
        
        - a -- a tupel of coordinates, of lenght n, at most the 
               number of coordinate functions of the curve 
        
        OUTPUT:
        
        a list containing all points on the curve whose first 
        n coordinate values agree with a.
        
        """
        
        n = len(a)
        assert n >= 1, "You must give at least one coordinate!"
        assert n <= len(self._coordinate_functions), "Too many coordinates given."
        F = self._function_field
        F0 = F.base_field()
        if a[0] == Infinity:
            v0 = FunctionFieldValuation(F0, 1/F0.gen())
        else:    
            v0 = FunctionFieldValuation(F0, F0.gen()-a[0])
        if F0 is F:
            return self.point(v0)
        V = v0.extensions(F)
        f = self.coordinate_functions()
        ret = []
        for v in V:
            if all([compute_value(v, f[i]) == a[i] for i in range(n)]):
                ret.append(self.point(v))
        return ret    
        
    
    
class PointOnSmoothProjectiveCurve(SageObject):
    """ A closed point on a smooth projective curve.
    
    A point on a curve X is identified with the corresponding 
    valuation on the function field of X. 
    However, we also evaluate a set of coordinate functions in the point;
    the corresponding tupel is used to identify the point (e.g.
    when checking for equality of points).
    """
    
    def __init__(self, X, v):
        self._curve = X
        self._valuation = v/v(v.uniformizer())
        self._coordinates = self.coordinates()
        
        
    def __repr__(self):
        return "Point on %s with coordinates %s."%(self._curve, self._coordinates)
    
    def curve(self):
        """ Return the underlying curve of the point.
        """
        
        return self._curve
    
    def valuation(self):
        """ Return the valuation corresponding to the point.
        """
        
        return self._valuation
    
    def residue_field(self):
        """ Return the residue field of the point.
        """
        
        return self._valuation.residue_field()
    
    @cached_method
    def absolute_degree(self):
        """ Return the absolute degree of self.
        
        The absolute degree of a point x on a curve X over k is the 
        degree of the extension k(x)/k.
        Here k is the base field, which may not be equal to the field of constants.
        """
        try:
            return self._absolute_degree
        except AttributeError:
            self._absolute_degree = extension_degree(self._curve._constant_base_field, self._valuation.residue_field())
            return self._absolute_degree
    
    @cached_method
    def degree(self):
        """ Return the degree of self.
        
        The absolute degree of a point x on a curve X is the 
        degree of the extension k(x)/k.
        Here k is the field of constants of X.
        """
        
        return ZZ(extension_degree(self._curve._constant_base_field, self._valuation.residue_field())/self._curve._field_of_constants_degree)
    
    def value(self, f): 
        """ Return the value of the function f in the point.
        
        If f has a pole then `Infinity` is returned.
        """
        
        if self._valuation(f) < 0:
            return Infinity
        else:
            return self._valuation.reduce(f)
        
    def order(self, f):
        """ Return the order of the function in the point.
        
        This is the same as self.valuation()(f).
        """
        
        return self._valuation(f)
    
    @cached_method
    def coordinates(self):
        """ Return the coordinate tupel of the point.
        """
        
        return tuple([self.value(x) for x in self._curve._coordinate_functions])
    
    
#------------------------------------------------------------------------------    
    
# auxiliary functions


def compute_value(v, f):
    
    from sage.rings.infinity import Infinity
    if v(f) < 0:
        return Infinity
    else:
        return v.reduce(f)
      
    
def separate_points(coordinate_functions, valuations):
    """ Add new coordinate functions to separate the points in V.
    
    INPUT: 
    
    - coordinate_functions: a list of elements of a function field F
    - valuations: a list of valuations on F
    
    OUTPUT: 
    compute
      an enlargement of 'coordinate_functions' with the property 
      that [value(v,x) for x in coordinate_functions] are pairwise
      distinct, when v runs through 'valuations'
      
    """
    
    repeat = True
    while repeat:
        dict = {}
        for v in valuations:
            a = tuple([compute_value(v, x) for x in coordinate_functions])
            if a in dict.keys():
                v1 = dict[a]
                coordinate_functions.append(v.separating_element([v1]))
                repeat = True
                break
            else:
                dict[a] = v
                repeat = False
    return coordinate_functions


# This function has been replaced by the method 'separating_element'
def separate_two_points(v1, v2):
    """ Return a function which separates v1 and v2.
    
    INPUT:
    
    - v1, v2: discrete valuations on a common function field F
    
    OUTPUT:
    
    an element f of F such that value(f, v1) != value(f, v2)
    
    """
    
    # print "calling <separate_points> with v1 = %s and v = %s."%(v1, v2)
    f = v1.uniformizer()
    if v2(f)<=0:
        return f    
    else:
        w = v2._base_valuation
        try:
            g = w._approximation.phi()
            print "g = ", g
            # maybe replace with _initial_approximation
        except AttributeError:
            w = w._base_valuation
            g = w._approximation.phi()
            print "! g = ",g
        # assert v2(g) > v1(g)
        n = ZZ(v1(g)/v1(f))
        return g*f**(-n)
    
    
def extension_degree(K, L):
    """ Return the degree of the field extension L/K.
    
        INPUT: 
        
        - K, L -- two field, where K has a natural embedding into L
        - check (default: False) -- boolean
        
        OUTPUT:
        
        the degree [L:K]
        
        At the moment, this works correctly only if K and L are 
        finite extensions of a common base field. It is not checked 
        whether K really maps to L. 
        
    """
    
    # assert K.is_finite(), "K must be finite."
    # assert L.is_finite(), "L must be finite."
    # assert K.characteristic() == L.characteristic(), "K and L must have the same characteristic."
    try:
        n = K.degree()
    except (AttributeError, NotImplementedError):
        n = K.absolute_degree()
    try:    
        m = L.degree()
    except (AttributeError, NotImplementedError):
        m = L.absolute_degree()
    assert n.divides(m), "K is not a subfield of L."
    return ZZ(m/n)
    
    
def sum_of_divisors(D1, D2):
    """" Return the sum of the divisors D1 and D2.
    
    INPUT:
    
    - D1, D2: divisors on the same curve X
    
    OUTPUT:
    
    D1 is replaced by the sum D1+D2 (note that this changes D1!).
    
    Here a divisor is given by a dictionary with entries (a:(P,m)),
    where a is a coordinate tupel, P is a point on X with coordinates a
    and m is the multiplicity of P in D.
    """
        
    for a in D2.keys():
        P, m2 = D2[a]
        if a in D1.keys():
            Q, m1 = D1[a]
            D1[a] = (P, m1+m2)
        else:
            D1[a] = D2[a]
    return D1        
     
    
    
    
    
    
        