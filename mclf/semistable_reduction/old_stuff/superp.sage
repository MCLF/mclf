"""                     Superp
                        ======
                        
Computing the semistable reduction of a superelliptic curve

                     Y: y^p =f(x),
                     
over a p-adic field K. 

"""

load("~/main_project/semistable_reduction/papprox.sage")
load("~/main_project/MacLane_valuations/maclane_tree.sage")
load("~/main_project/MacLane_valuations/maclane.sage")
load("~/main_project/MacLane_valuations/affinoid.sage")
load("~/main_project/padic_extensions/padic_extensions.sage")

class Superp(SageObject):
    
    def __init__(self, f, v_K, p):
        
        R = f.parent()
        assert R.base_ring() is v_K.domain()
        assert p == v_K.residue_field().characteristic()
        self.base_ring = R
        self.f = f
        self.base_valuation = v_K
        self.p = p
        FX = FunctionField(v_K.domain(), names=R.variable_names())
        S.<T> = FX[]
        FY.<y> = FX.extension(T^p-FX(f))
        self.FX = FX
        self.FY = FY
        
    def compute_etale_locus(self):
        
        f = self.f
        p = self.p
        n = f.degree()
        m = floor(n/p)
        a, c, d = H_G_decomposition(f,p)

        pl = 1
        while pl <= m:
            pl = pl*p
        
        v0 = GaussValuation(self.base_ring,   
                            self.base_valuation)
        F = [f]
        for i in [1..n]:
            F.append(F[i-1].derivative()/i)
        delta=[]
        for k in [m+1..n]:
            if k != pl:
                delta_k_p = IncreasingDeltaFunction(v0, d[pl],
                                                    k, 0)
                delta_k_m = IncreasingDeltaFunction(v0, d[k],
                                                pl,(k-pl)*p/(p-1))
                delta.append(DeltaFunction(delta_k_p, delta_k_m))
        
        delta0_m = IncreasingDeltaFunction(v0, F[0], pl, p/(p-1))
        delta0_p = IncreasingDeltaFunction(v0, d[pl], 1, 0)
        delta.append(DeltaFunction(delta0_p, delta0_m))
        for k in [1..n]:
            delta_k_m = IncreasingDeltaFunction(v0,
                                 F[k]*F[0]^(k-1), pl, k*p/(p-1))
            delta_k_p = IncreasingDeltaFunction(v0,
                                                d[pl], k, 0)
            delta.append(DeltaFunction(delta_k_p, delta_k_m))
        FF = R.one()
        for k in [1..n-1]:
            FF = FF * F[k]
        for k in [m+1..n]:
            FF = FF *d[k]
        c = v0(FF)/v_K(v_K.uniformizer())
        FF = FF*v_K.uniformizer()^(-c)
        print "delta = ", delta
        print "F = ", F
        
        self.Xet = AffinoidDomain(v0, delta, FF)
        # self.Xet.print_tree()
       
    def compute_semistable_reduction(self):
        
        self.compute_etale_locus()
        self.maclane_tree = self.Xet.maclane_tree()
        
        components = []
        for c in self.maclane_tree.vertices():
            components.append(SuperpComponent(self, c))
        self.components = components    
            
        for c in components:
            c.compute_splitting_field()
            c.compute_inertial_reduction()
            c.compute_reduction()
            # c.alt_compute_reduction()
        
    
    def conductor_exponent():
        
        pass
    
        
class SuperpComponent(SageObject):
    
    def __init__(self, Y, c):
        """ Initialize a component.
        
        INPUT:
        
        - ``Y`` -- the superp object Y (the 'parent' of self)
        - ``c`` -- a component of a MacLane tree
        """
        
        self.Y = Y
        self.v = c.v
        self.reduction = []
        double_points = []
        for eta, c1 in c.edges:
            double_points.append(eta)
        self.double_points = double_points    
        
    def __repr__(self):
        
        return "Component of %s corresponding to %s."%(self.Y, self.v)
    
    def compute_splitting_field(self):   #  now obsolet !
        
        # print "calling <compute_splitting_field>"
        f = self.Y.f
        R = self.Y.base_ring
        v_K = self.Y.base_valuation
        K = v_K.domain()
        p = self.Y.p
        v = self.v
        # print "v = ", v
        gb = v.residue_ring().one()
        for eta in self.double_points:
            gb = gb*eta.phib()
        # print "gb = ", gb    
        m = v(f).denominator()
        # print v.equivalence_unit(-v(f))
        gb = gb*v.reduce(f^m*v.equivalence_unit(-m*v(f))) 
        # print "gb = ", gb
        hb = irreducible_polynomial_prime_to(gb)
        # print "hb = ", hb
        h = v.lift_to_key(hb)  
        # print "h = ", h
        
        v_L0 = padic_splitting_field(v_K, h)
        L0 = v_L0.domain()
        print "L0 = ", L0
        h = h.change_ring(L0)
        V = maclane_basefield_extensions(v, v_L0, h)
        # print "V = ",V
        g = V[0].phi()
        # print "g = ", g
        # print "v.F() =", V[0].F()
        if g.degree() == 1:
            alpha = L0(-g[0]/g[1])
            # print "alpha = ",alpha
            A.<y> = L0[]
            G = y^p - f(alpha)
            G = padic_irreducible_factor(v_L0, G)
            # it would be better to have a specialized function to
            # adjoin pth roots; if L0 is already very large, this
            # is rather slow
        else:
            G = pth_root_equation(f.change_ring(L0), g, p)
            G = padic_irreducible_factor(v_L0, G)
        if G.degree() > 1:
            # print "G = ", G
            v_L1 = padic_simple_extension(v_L0, G)
            L1 = v_L1.domain()
        else:
            v_L1 = v_L0
            L1 = L0
        print "L1 = ", L1
        
        v_L = padic_sufficiently_ramified_extension(v_L1, v.E())
        # print " L = ", v_L.domain()
        self.splitting_field = v_L
        return
    
    def compute_inertial_reduction(self):
        
        FX = self.Y.FX
        FY = self.Y.FY
        vx = RationalFunctionFieldValuation(FX, self.v)
        self.vx = vx
        inertial_reduction = vx.extension(FY) 
        # in the current version, this should be unique
        self.inertial_reduction = inertial_reduction
        print "Inertial reduction component:"
        print "    ", inertial_reduction.residue_field()
        print "    ", self.v
        print "--------------"      
        
    def compute_reduction(self):
        
        # v_L = self.splitting_field
        f = self.Y.f
        R = self.Y.base_ring
        v_K = self.Y.base_valuation
        K = v_K.domain()
        p = self.Y.p
        v = self.v
        gb = v.residue_ring().one()
        for eta in self.double_points:
            gb = gb*eta.phib()
        m = v(f).denominator()
        gb = gb*v.reduce(f^m*v.equivalence_unit(-m*v(f))) 
        hb = irreducible_polynomial_prime_to(gb)
        h = v.lift_to_key(hb)  
        # print "h = ", h
        
        v_L0 = padic_splitting_field(v_K, h)
        L0 = v_L0.domain()
        # print "L0 = ", L0
        h = h.change_ring(L0)
        V1 = maclane_basefield_extensions(v, v_L0, h)
        # print "V1 = ", V1
        for w in V1:
            g = w.phi()
            if g.degree() == 1:
                alpha = L0(-g[0]/g[1])
                A.<y> = L0[]
                G = y^p - f(alpha)
                G = padic_irreducible_factor(v_L0, G)
                # it would be better to have a specialized function to
                # adjoin pth roots; if L0 is already very large, this
                # is rather slow
            else:
                G = pth_root_equation(f.change_ring(L0), g, p)
                G = padic_irreducible_factor(v_L0, G)
            if G.degree() > 1:
                # print "G = ", G
                v_L1 = padic_simple_extension(v_L0, G)
                L1 = v_L1.domain()
            else:
                v_L1 = v_L0
                L1 = L0
            # print "L1 = ", L1
        
            # print "need ramification index multiple of ", v.E()
            v_L = padic_sufficiently_ramified_extension(v_L1, v.E())
            # print " L = ", v_L.domain()

            L = v_L.domain()
            p = self.Y.p
            f = self.Y.f
            FXL.<z> = FunctionField(L)
            # print FXL
            # print FXL._ring.base_ring()
            assert FXL._ring.base_ring() is L
            h = FXL._ring(self.v.phi())
            W = maclane_basefield_extensions(self.v, v_L, h)
            # print "W = ", W
            S.<T> = FXL[]
            FYL.<y> = FXL.extension(T^p-FXL(f))
            reduction = []
            for w in W:
                w = RationalFunctionFieldValuation(FXL, w)
                w = w.extension(FYL)
                print "Reduction component:"
                print "    ", w.residue_field()
                print "     constant field: ", w.residue_field().constant_base_field()
                print "    ", v
                print "     splitting field: ", L
                print "------------"
                reduction.append((v_L,w))
            self.reduction += reduction
        
    def alt_compute_reduction(self):
        """ Alternative method to compute reduction."""

        g = self.splitting_field.domain().polynomial()
        FY = self.Y.FY
        R.<T> = FY[]
        G =R(g.padded_list())
        FYL = FY.extension(G)
        reductions = self.inertial_reduction.extensions(FYL)
        # unforunately, there is no .extensions method yet

    def compute_ramification_filtration_reduction(self):
        
        f = self.Y.f
        R = self.Y.base_ring
        v_K = self.Y.base_valuation
        K = v_K.domain()
        p = self.Y.p
        v = self.v
    
        for vL, w in self.reduction:
            print "components over ", v
            print "the splitting field is ", vL.domain()
            filt = padic_ramification_filtration(vL, compute_subfields=True)
            print filt
            print "The ramification breaks are:", [filt[i][0]+1 for i in range(len(filt))]
            for i in range(len(filt)):
                m = filt[i][0]
                n = filt[i][1]
                vLm = filt[i][2]
                Lm = vLm.domain()
                print "Computing Y_m for m=%s and |Gm|=%s:"%(m,n)
                print "intermediate field: ", vLm.domain(), " with ramification index ", vLm(p)
                FXL.<z> = FunctionField(Lm)
                h = FXL._ring(v.phi())
                V = maclane_basefield_extensions(v, vLm, h)
                S.<T> = FXL[]
                FYL.<y> = FXL.extension(T^p-FXL(f))
                for w in V:
                    w = RationalFunctionFieldValuation(FXL, w)
                    w = w.extension(FYL)
                    print "    Reduction component:"
                    print "        ", w.residue_field()
                    print "        ", w



#--------------------------------------------------------------

def irreducible_polynomial_prime_to(f, min_deg=1):
    """ Return an irreducibel polynomial prime to f.
    
    INPUT:
    
    - f: an univariat polynomial over a finite field
    - min_deg: a positive integer (default = 1)
    
    OUTPUT:
    
    an irreducible polynomial prime to f, of degree >=min_deg
    
    """
    
    R = f.parent()
    x = R.gen()
    F = R.base_ring()
    assert F.is_finite(), "base field of f must be finite."
    for d in range(min_deg, 10):
        for g in all_polynomials(F, x, d):
            if g.is_irreducible() and g.gcd(f).is_one():
                return g

def all_polynomials(F, x, d):
    """ List all polynomials in x over F of degree d.
    
    INPUT:
    
    - F: a finite field F
    - x: generator of a polynomial ring over F
    
    OUTPUT:
    
    an iterator which list all elements of F[x] of degree d.
    """
    
    if d == 0:
        for a in F.list():
            yield a*x^0
    else:
        for e in range(0,d):
            for f in all_polynomials(F, x, e):
                yield x^d+f
                
        
def pth_root_equation(f, g, p):
    """" Return equation for pth root of f(a), where g(a)=0.
    
    INPUT: 
    
    - f, g -- elements of a polynomial ring K[x]
    - p    -- a prime number
    
    OUTPUT:
    
    an irreducible polynomial h in K[x] with the following 
    property:
    if b is a root of h then there exists a root a of g
    with b^p = a.
    """
    
    R = f.parent()
    assert R is g.parent()
    K = R.base_ring()
    S.<t> = R[]
    G = S(g.padded_list())
    print "G = ", G
    F = S(f.padded_list()) - R.gen()^p
    print "F = ", F
    return G.resultant(F).factor()[0][0]
        
        
        
    