K = QQ
vK = pAdicValuation(K, 2)
F.<x> = FunctionField(K)
X = BerkovichLine(F, vK)
X

f = (x^4+2)*(2*x^2-1)*(x^4+1)*(x^8+2)*(x-1)*(x^2+x+1)
D = X.divisor(f)
D

T = BerkovichTree(X)
for xi, m in D:
    T, T_xi  = T.add_point(xi)
T.print_tree()

R = F._ring
y = R.gen()
