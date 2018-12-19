using Nemo
include("superelliptic.jl")

Br,w = FiniteField(521,4,"l")

Ri,x = PolynomialRing(Br,'x')

print(ZetaFunction(3, x^7+w*x+ 1))
