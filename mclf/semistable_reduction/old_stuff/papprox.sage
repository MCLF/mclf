



def h_g_decomposition(f,p):

# f: a polynomial of degree n over a field K
# p: a prime number
# condition: f=a0+a1*x+.., mit a0<>0

# Output: polynomials h,g, such that
#    (a)  f=a_0*(h^p+g)
#    (b)  r:=deg(h)<=n/p
#    (c)  x^(r+1)|g

    R=f.parent()
    K=R.base_ring()
    x=R.gen()
    n=f.degree()
    r=floor(n/p)
    a0=f[0]
    assert a0.is_unit()

    h=R(1)
    f=f/a0
    g=f-1
    for k in [1..r]:
        h=h+g[k]/p*x^k
        g=f-h^p
    return h,g


def H_G_decomposition(f,p):

    R=f.parent()
    x=R.gen()
    K=R.fraction_field()
    S.<t>=K[]
    F=f(x+t)
    H,G=h_g_decomposition(F,p)
    d =[R(G[k]*f^k) for k in [0..f.degree()]]
    return H,G,d





