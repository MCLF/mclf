"""                     Valuation trees
                        ===============

Let (K,v_K) be a complete field with residue field k,
and let X be the projective line over K, and X^an the associated
analytic space, in the sense of Berkovic.
Then X^an is a "simply connected special quasi-polyhedron", see
[Berkovic, Red Book, § 4]. Among other things, this means that
any two points x,y in X^an are the endpoints of a unique path (a
closed subset) [x,y] which is homeomorphic to the closed interval
[0,1] in RR.

Given a finite set S of points of  X^an,
then S spans a subtree T of X, in the following way.
The vertices of T are points of X^an, and they contain all
elements of S. Two vertices are adjacent if
the interval connecting them (whose existence and uniqueness is a
consequence of Berkovich's result mentioned above) does not
contain any other vertex. Moreover, the intervals corresponding to
two distinct edges can have only endpoints in common. Finally,
we have the minimality condition that a vertex which is not in S
has at least three adjacent vertices.

A vertex of the tree T of degree > 1 corresponds to points of type 2.
A point on X^an of type 2 corresponds to a valuation v on the function
field F = K(x) with the following properties:
(a) the restriction of v to K is equal to v_K
(b) the residue field of v has transcendence degree 1 over the residue
    field of K.
Let us call valuations with these properties *MacLane valuations*. If
v(x)>=0, then the restriction of v to K[x] can be represented as an
*inductive valuation*, see [MacLane, ??]. Similarly, if v(x)<0 then
the restriction of v to K[1/x] is an inductive valuation.

We call a tree T as above a *valuation tree* if every  vertex corresponds
to a point of type 2 (i.e. a MacLane valuation).

EDIT
A bit more general, we also consider *decorated valuation trees*. Recall
that a point of type 5 on the adic space X^ad corresponds to a pair
eta = (v,vb), where v is a MacLane valuation on F and vb is a discrete valuation
on the residue field of v which is trivial on the residue field of K.
Geometrically, a point of type 5 eta=(v,vb) corresponds to an open subset
D_\eta in X^an which is a residue class of an affinoid domain with v as
its only boundary point, see ??. A *decoration* of a valuation tree T consists
of a finite set of points of type 5 eta = (v,vb) such that v is a vertex of
T and the residue class D_\eta does not contain any vertex of T.
EDIT

No, a decorated tree should be nothing more than a subtree of X^an. However, we
should allow also algebraic points of type 1 as vertices. A point of type 1
is always a tail of the tree.


This module realizes the concept of a decorated valuation tree.


"""

from sage.geometry.newton_polygon import NewtonPolygon

class ValuationTree(SageObject):
    """ Create an empty valuation tree.

    """

    def __init__(self, F, vK):
        """ Create an (empty) valuation tree.

        INPUT:

        - F -- a rational function field over a base field K
        - vK -- a discrete valuation on the base field K of F

        OUTPUT:

        an empty valuation tree with function field F and base valuation vK
        """

        self._F = F
        self._K = F.constant_base_field()
        self._vK = vK
        assert self._K is vK.domain(), "Domain of vK is not the constant base field of F."
        self._vertices = []
        self._edges = []
        self._leaves = []

    def __repr__(self):

        return "valuation tree with function field %s over %s."%(self._F, self._vK)

    def vertices(self):
        """ Return the list of vertices of the tree.
        """
        return self._vertices

    def edges(self):
        """ Return the list of edges of the tree.
        """
        return self._edges

    def leaves(self):
        """ Return the list of all leaves of the tree.
        """
        return self._leaves


    def base_valuation(self):
        """ Return the valuation on the base field.
        """
        return self._vK

    def base_field(self):
        """ Return the base field.
        """
        return self._K

    def add_vertex(self, v):
        """ Add a new vertex to the tree.
        """
        if self._vertices == []:
            c = ValuationTreeVertex(v)
            self._vertices = [c]
        else:
            c = self._vertices[0]
            c.add_valuation(v)
            self._vertices = c.vertices()




class ResidueClass(SageObject):
    """ Construct a residue class on the Berkovich projective line.

    Let X be the projective line over a p-adic field
    K. A *residue class* is an open subset of the analytic space
    X^an which becomes,
    after a finite extension of K, an open disk. FALSE! 

    A residue class D_\eta is determined by a pair eta=(v, vb),
    where v is a MacLane valuation
    n function field F=K(x) and vb is a function field valuation
    on the residue field
    k(v) of v (which we consider as a function field over the
    residue field of K). We call v the *major valuation* and
    vb the *minor valuation*.

    To be continued...
    """

    def __init__(self, v, p):

        self._v = v
        self._vK = v._base_valuation
        self._K = self._vK.domain()
        self._kv = v.residue_field()
        if p in v.domain():
            self._phi = p
        elif p in kv.domain():
            self._psi = p
        elif isinstance(p, FunctionFieldValuation_base):
            self._vb = p
        else:
            raise ValueError("Base field of p is not as expected.")


    def __repr__(self):
        return "residue class of %s on discoid with boundary %s"%(self.phi(), self._v)

    def phi(self):
        """ Return a key polynomial defining self.
        """
        if hasattr(self, '_phi'):
            return self._phi
        elif hasattr(self, '_psi'):
            self._phi = self._v.lift_to_key(self._psi)
            return self._phi
        else:
            self._psi = self._vb.uniformizer()
            self._phi = self._v.lift_to_key(self._psi)
            return self._phi

    def psi(self):
        """ Return a defining uniformizer for the minor valuation.
        """
        if hasattr(self, '_psi'):
            return self._psi
        elif hasattr(self, '_vb'):
            self._psi = self._vb.uniformizer()
            return self._psi
        else:
            self._psi = maclane_normalized_reduction(self._v, self._phi)
            return self._psi

    def v(self):
        """ Return the major valuation.
        """
        return self._v

    def vb(self):
        """ Return the minor valuation.
        """

        if hasattr(self, '_vb'):
            return self._vb
        else:
            k1 = self._v.residue_field()
            k = FunctionField(k1.base_ring(), k1.variable_name())
            self._vb = FunctionFieldValuation(k, k(self.psi()))
            return self._vb
        # else:
        #     self._vb = FunctionFieldValuation(self._v.residue_field(), self.psi())
        #     return self._vb

    def is_in_residue_class(self, v):
        """ Check whether v is in the residue class of self.

        INPUT:
        - v: a MacLane valuation with the same domain
             as self,

        OUTPUT:
          'True' if v lies in the residue class defined by self,
          'False' otherwise

        ToDo:

        Allow v to be a prime element, representing a classical point.
        """

        phi = self.phi()
        return v(phi) > self._v(phi)



class ValuationTreeVertex(SageObject):
    """ The vertex of a valuation tree.

    The two main attibutes are:
    - a MacLane valuation v
    - a list of edges emanating from self;
      each edge is a pair (eta, c), where eta is a residue class
      with boundary v and c is the end vertex of the edge. Of
      course, c.v lies in the residue class eta.
    - a list of leaves emanating from self.



    """

    def __init__(self, v):

        self.v = v
        self.edges = []

    def __repr__(self):
        return "Vertex of MacLane tree of order %s, with valuation %s"%(len(self.edges), self.v)


    def is_equal(self, v):
        """ Check whether v is equal to self.v"""

        #print "calling <is_equal> for %s with v=%s."%(self, v)
        # if isinstance(self.v, GaussValuation):
        #    return isinstance(v, GaussValuation)
        return maclane_is_equal(self.v, v)

    def residue_class(self, v):
        """ Return the residue class with boundary self.v containing v."""

        # print "calling <residue_class> for %s with v=%s"%(self.v, v)
        assert not self.is_equal(v), "v must not be equal to self.v"
        if maclane_leq(self.v, v):
            eta = ResidueClass(self.v, valuation_key(v))
            # print "returning eta =", eta.phi()
            return eta
        else:
            eta = ResidueClass(self.v, 1/self.v.domain().gen())
            # print "returning eta = ", eta.phi()
            return eta

    def add_edge(self, c):
        """ Add the edge pointing to c.

        We assume that c.v is not contained in any residue class
        corresponding to an edge emanating from self,
        and vice versa.
        """

        eta = self.residue_class(c.v)
        self.edges.append((eta, c))
        return


    def delete_edge(self, c):
        """ delete the edge from self to c """

        for i in range(len(self.edges)):
            if maclane_is_equal(self.edges[i][1].v, c.v):
                del self.edges[i]
                return
        raise AssertionError("There is no edge to c.")



    def add_valuation(self, v, count=0):
        """ Add the valuation v to the tree with root self.

        INPUT:

        - v: a MacLane valuation on the domain of self.v

        OUTPUT:

        Adds a new vertex with valuation v to the MacLane
        tree with vertex self, and returns the vertex
        corresponding to v. If the tree already contains a
        vertex corresponding to v then this vertex is returned,
        and the tree is left unchanged.

        """

        if count > 5:
            print "dead end!"
            return
        # print "calling 'add_valuation' from ", self.v
        if self.is_equal(v):
            return  self  # self.v==v
        for eta, c in self.edges:
            if c.is_equal(v):
                return c
            if eta.is_in_residue_class(v):
                if maclane_is_between(self.v, v, c.v):
                    # delete the edges between self and c
                    self.delete_edge(c)
                    c.delete_edge(self)
                    # we insert a new vertex between self and c
                    new_vertex = ValuationTreeVertex(v)
                    self.add_edge(new_vertex)
                    new_vertex.add_edge(self)
                    new_vertex.add_edge(c)
                    c.add_edge(new_vertex)
                    return new_vertex
                elif maclane_is_between(self.v, c.v, v):
                    # starting new search from c
                    return c.add_valuation(v, count+1)
                else:
                    # c.v =", c.v, " and v= ",v, " need to be separated
                    v_new = maclane_median(self.v, c.v, v)
                    self.add_valuation(v_new, count+1)
                    return self.add_valuation(v, count+1)
        # v is not contained in a residue class of an edge
        # from self; therefore,
        # insert a new vertex adjacent to self
        new_vertex = ValuationTreeVertex(v)
        self.add_edge(new_vertex)
        new_vertex.add_edge(self)
        return new_vertex


    def graph(self):
        """ Compute a representation of self as a graph.

        INPUT:
          (no parameter)

        OUTPUT:
          a pair G, vertex_list, where G is a Sage object
          of type 'Graph' representing the MacLane tree with
          vertex self.
          The vertices of G are represented by the numbers
          0,1,.., and the ith entry of vertex_list is the
          corresponding vertex of the MacLane tree

        """

        G = Graph()
        vertex_list = []
        self.add_vertex_to_graph(G, vertex_list)
        return G, vertex_list

    def add_vertex_to_graph(self, G, vertex_list, head=None):
        """ Add recursively vertices to the graph G.

        INPUT:

        - G: a graph (whose vertices a numbers 0,1,..)
        - vertex_list: a list whose ith entry is the MacLane tree
          vertex corresponding to the vertex i of G
        - head: a MacLane valuation v adjacent of self.v
          (or 'None' by default).

        OUTPUT:

        The function adds a new vertex to the graph G which
        corresponds to self.v and stores the value of v in the
        list 'vertex_list'. The function is then applied
        recursively to all vertices of the MacLane tree
        adjacent to self, except to the vertex with
        valuation 'head'. So in total, the full subtree of the
        MacLane tree with vertex self which is obtained by cutting
        off the edge pointing to 'head' is added to the graph G.

        """

        n = len(vertex_list)
        vertex_list.append(self.v)
        G.add_vertex(n)
        for eta, c in self.edges:
            if not c.v is head:
                c.add_vertex_to_graph(G, vertex_list, self.v)
                for m in range(len(vertex_list)):
                    if c.is_equal(vertex_list[m]):
                        break
                assert c.is_equal(vertex_list[m])
                G.add_edge(n,m)

    def vertices(self, predecessor=None):
        """ Return a list of all vertices of the tree.
        """

        vertices = [self]
        for eta, c in self.edges:
            if not c is predecessor:
                vertices += c.vertices(self)
        return vertices


#------------------------------------------------------------
""" Several functions related to the tree structure on X

"""

def valuation_from_discoid(vK, phi, r, count=0):
    """ Return the boundary of the discoid given by vK, phi and r.

    INPUT:

    - vK -- a discrete valuation on a field K
    - phi -- a strictly irreducible polynomial,
             as an element of the function field K(x), or 1/x
    - r -- a rational number

    OUTPUT:

    A geometric valuation v on the function field K(x)
    with base valuation vK,
    which is the unique boundary point of the affinoid

        D := { x | v_x(phi) >= r }.

    If D has more than one boundary point (e.g. it is
    not a discoid) then an error is raised.
    """
    if count > 3:
        return False
    # print "calling valuation_from_discoid with phi =%s and r=%s."%(phi, r)
    F = phi.parent()
    R = F._ring
    x = F.gen()
    if phi == 1/x:
        v0 = GaussValuation(R, vK)
        if r == 0:
            return FunctionFieldValuation(F, v0)
        elif r < 0:
            v1 = v0.augmentation(R.gen(), -r)
            return FunctionFieldValuation(F, v1)
        else:
            v1 = FunctionFieldValuation(F, v0.augmentation(R.gen(), r))
            return FunctionFieldValuation(F, (v1, F.hom([1/x]), F.hom([1/x])))
    # now phi should be a polynomial in x
    phi1 = R(phi.numerator())
    n = phi1.degree()
    c = phi1.padded_list()
    v0 = GaussValuation(R, vK)
    if vK(c[0]) >= r:     #  0 lies in D
        s = max([(r-vK(c[i]))/i for i in range(1,n+1)])
        # now D = D[s]
        if s == 0:
            return FunctionFieldValuation(F, v0)
        elif s > 0:
            v = v0.augmentation(R.gen(), s)
            return FunctionFieldValuation(F, v)
        else:
            v = FunctionFieldValuation(F, v0.augmentation(R.gen(), -s))
            return FunctionFieldValuation(F, (v, F.hom([1/x]), F.hom([1/x])))
    else:                 #  0 does not ly in D
        np = NewtonPolygon([(i,vK(c[i])) for i in range(n+1)])
        assert len(np.slopes(repetition=False)) == 1, "phi is not strictly irreducible."
        s = -np.slopes()[0]  # s = valuation of all roots of phi
        if s >= 0:           #  D is strictly contained in the unit disk D[0]
            r = r - vK(c[n])
            phi1 = phi1.monic()  # normalize phi and r
            v = v0
            while v(phi1) < r:
                if v.is_key(phi1):
                    v = v.augmentation(phi1, r)
                else:
                    V = v.mac_lane_step(phi1)
                    assert len(V) == 1, "D is not a discoid."
                    v = V[0]
                    if v(phi1) > r:
                        v0 = v.augmentation_chain()[-1]
                        psi = v.phi()
                        w = v0.augmentation(psi, v0(psi), check=False)
                        c = list(w.coefficients(phi1))
                        assert v0(c[0]) < v(phi1)
                        t = max([(r-v0(c[i]))/i for i in range(1,len(c))])
                        v = v0.augmentation(psi, t)
                        assert v(phi1) == r
            assert v(phi1) == r, "Something went wrong!"
            return FunctionFieldValuation(F, v)
        else:             # D is not contained in the closed unit disk
            v = valuation_from_discoid(vK, x^n*phi1(1/x), r-n*s, count+1)
            return FunctionFieldValuation(F, (v, F.hom([1/x]), F.hom([1/x])))



def valuation_key(v):
    """ Return a key polynomial for v.

    INPUT:

    - v: a discrete valuation on a rational function field F=K(x)

    OUTPUT:

    an element phi of F which is a irreducible polynomial in x
    and such that the affinoid domain

        D := { x | v_x(phi) >= v(phi) }

    is a closed discoid with boundary point v.  Then D = D_v
    is the unique discoid with boundary point v which does not
    contain the point oo.
    """

    try:
        return v.domain()(v._base_valuation.phi())
    except AttributeError:
        x = v.domain().gen()
        phi = v._base_valuation._base_valuation.phi()
        if phi[0].is_zero():
            return x
        else:
            return x^phi.degree()*phi(1/x)
            # return v.domain()(v._base_valuation._base_valuation.phi()(1/x).numerator())



def maclane_is_equal(v1, v2):
    """ Check whether v1=v2.

    INPUT:

     - v1, v2: discrete valuations on the same function field F = K(x) and
               the same restriction to the base field K

    OUTPUT:

    'True' if v1 = v2

    We use the fact that v1=v2 iff the discoids D_v1 and D_v2 are equal.

    """

    phi1 = valuation_key(v1)
    phi2 = valuation_key(v2)
    return v1(phi1) == v2(phi2) and v2(phi1) == v2(phi2)


def maclane_leq(v1, v2):
    """ Check wether v1 <= v2.

    INPUT:

    - v1, v2: discrete valuations on the same domain F = K(x),
              with the same restriction

    OUTPUT:

    'True' if v1 <= v2.

    Here '<=' refers to the natural partial ordering on the Berkovich
    projective line in which the point oo is the minimal element. Then
    v1<=v2 iff v2 is contained in the discoid D_v1.

    """
    phi1 = valuation_key(v1)
    phi2 = valuation_key(v2)
    return v1(phi1) <= v2(phi1)

def maclane_is_between(v1, v2, v3):
    """ Check whether v2 lies between v1 and v3.

    INPUT:

    - v1, v2, v3: MacLane valuations on the same domain K[x]

    OUTPUT:

    'True' if v2 lies on the interval from v1 to v3

    """

    if maclane_leq(v1, v3):
        return maclane_leq(v1, v2) and maclane_leq(v2, v3)
    elif maclane_leq(v3, v1):
        return maclane_leq(v3, v2) and maclane_leq(v2, v1)
    else:
        v4 = maclane_infimum(v1, v3)
        return ( maclane_leq(v4, v2) and
                 (maclane_leq(v2, v1) or maclane_leq(v2, v3)) )

#  This function should now be obsolet.
def maclane_predecessor(v, s0):
    """ Find predecessor of v with given value on v.phi().

    INPUT:

    - v: a MacLane valuation on K[x]
    - s0: a rational number, 0 <= s0 <= s:=v(v.phi())

    OUTPUT:

    A MacLane valuation v0 with v0 <= v and v0(v.phi()) = s0

    """

    phi = v.phi()
    s = v(phi)
    if s == s0:
        return v
    assert 0 <= s0 and s0 < s , "s is too large or negative."
    v0 = v
    while True:
        # print "v0=",v0
        if v0(phi) == s0:
            return v0
        elif v0(phi) > s0:
            v0 = v0._base_valuation
        elif not v0.is_key(phi):
            psi, m = v0.equivalence_decomposition(phi)[0]
            v0 = v0.extension(psi,s0/m)
            # ToDo: prove that this is correct
        else:
            return v0.extension(phi, s0)




def maclane_infimum(v1, v2):
    """ Find the infimum of v1 and v2.

    INPUT:

    - v1, v2: a geometric valuation on the same domain K(x)
              with the same base valuation vK

    OUTPUT:

    A geometric valuation v3 on K(x) which is the infimum of
    v1 and v2 (w.r.t. the partial ordering on the Berkovich line
    with minimal element oo)

    """

    # check whether v1, v2 are comparable
    if maclane_leq(v1, v2):  # v1 <= v2
        return v1
    if maclane_leq(v2, v1):  # v2 <= v1
        return v2

    # v1, v2 are not comparable. In any case, the infimum of v1 and v2
    # is the boundary of the smallest discoid containing D_v1 and D_v2.
    phi = valuation_key(v1)
    F = v1.domain()
    try:
        vK = v1._base_valuation.restriction(F.constant_base_field())
    except NotImplementedError:
        vK = v1._base_valuation._base_valuation.restriction(F.constant_base_field())

    return valuation_from_discoid(vK, phi, v2(phi))


def maclane_median(v1, v2, v3):
    """ Find the median of v1, v2, v3.

    INPUT:

    - v1, v2, v3: pairwise  distinct geometric valuations
      on the same domain K(x) and the same base valuation.

    OUTPUT:

    A geometric valuation v which is the median of v1, v2, v3.
    This means that v lies on the interval between any two of
    the three valuations v1, v2, v3. In particular, if one
    of the three valuation lies between the other two, then it is
    equal to v.

    """

    if maclane_leq(v1, v2):
        if maclane_leq(v3, v1):
            return v1   # v1 lies between v2 and v3
        elif maclane_leq(v1, v3) and maclane_leq(v3, v2):
            return v3   # v3 lies between v1 and v2
        elif maclane_leq(v2, v3):
            return v2   # v2 lies between v1 and v3
        else:
            v4 = maclane_infimum(v2, v3)
            if maclane_leq(v4, v1):
                return v1
            else:
                return v4
    elif maclane_leq(v2, v1):
        if maclane_leq(v3, v2):
            return v2   # v2 lies between v1 and v3
        elif maclane_leq(v2, v3) and maclane_leq(v3, v1):
            return v3   # v3 lies between v2 and v1
        elif maclane_leq(v1, v3):
            return v1   # v1 lies between v2 and v3
        else:
            v4 = maclane_infimum(v1, v3)
            if maclane_leq(v4, v2):
                return v2
            else:
                return v4
    else:
        if maclane_leq(v1, v3):
            return v1
        elif maclane_leq(v2, v3):
            return v2
        elif maclane_leq(v3, v1) and not maclane_leq(v3, v2):
            return v3
        elif maclane_leq(v3, v2) and not maclane_leq(v3, v1):
            return v3
        else:
            # return maclane_infimum(v2, v3) looks wrong!
            return maclane_infimum(v1, v2)

def maclane_normalized_reduction(v, f):
    """ Return the normalized reduction of f with respect to v.

    INPUT:

    - v -- a MacLane valuation on a rational function field F = K(x)
    - f -- an irreducible polynom in K[x], or 1/x

    OUTPUT:

    a nonzero element fb in the residue field of v ???
    Precise definition needed!
    """

    F = v.domain()
    R = F._ring
    x = F.gen()
    r = v(f)
    m = abs(r.denominator())
    v1 = v._base_valuation
    if hasattr(v1, 'equivalence_unit'):
        fl = v.reduce(f^m*F(v1.equivalence_unit(-m*r))).factor()
        if len(fl)>0:
            return fl[0][0]^sign(fl[0][1])
        else:
            return 1/v.residue_field().gen()
    else:
        v1 = v1._base_valuation
        g = v1.equivalence_unit(-m*r)(1/x)
        fb = v.reduce(f^m*F(g)).factor()
        if len(fb) > 0:
            return fb[0][0]^sign(fb[0][1])
        else:
            return 1/v.residue_field().gen()


#---------------------------------------------------------------
