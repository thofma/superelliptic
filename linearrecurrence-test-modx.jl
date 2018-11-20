using Nemo
include("linearrecurrence.jl")

N = 3
p = 7
L = [11,13]
R = [13,15]

BrR= ResidueRing(ZZ,Int(p^N))
RiR,xR = PolynomialRing(BrR,'x')

print("Fakery\n")
FakeP,k = PolynomialRing(QQ, 'k')
BrF= ResidueRing(FakeP,k^N)
RiF,xF = PolynomialRing(BrF,'x')

MF = matrix(RiF,2,2,[xF+k,xF,1 + 3*k,xF+1])

o = [matrix(BrR,
            [ numerator(evaluate(data(coeff(t[i, j],0)),p)) for i = 1:rows(t),j = 1:cols(t)])
    for t in LinearRecurrence(MF, L, R)]
print(o,"\n")

print("\n\nReality\n")


MR = matrix(RiR,2,2,[xR + p, xR, 1 + 3*p, xR+1])

print(LinearRecurrence(MR, L, R))
