K = QQ
vK = pAdicValuation(K, 2)
F.<x> = FunctionField(K)
X = BerkovichLine(F, vK)
xi1 = X.point_from_discoid(x,1)
xi2 = X.point_from_discoid(x^2+4,3)
eta = TypeVPointOnBerkovichLine(xi1, xi2)
eta
