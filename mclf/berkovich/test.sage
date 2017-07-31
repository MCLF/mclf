

K = QQ
vK = pAdicValuation(K, 2)
F.<x> = FunctionField(K)
X = BerkovichLine(F, vK)

f = (x^2+2)*x/2/(x+1)/(x^4+4)

U = RationalDomainOnBerkovichLine(X, f)

 
