using Nemo
include("linearrecurrence.jl")


Br= ResidueRing(ZZ,ZZ(5^2))
Ri,x = PolynomialRing(Br,'x')
M = matrix(Ri,2,2,[x,x,1,x+1])
L = [11,13];
R = [13,15];
s=Int(floor(log(4,R[length(R)])));
DDi= UpperCaseDD(Br(1),Br(2)^s,2^s)^(-1);
LinearRecurrence(M, L, R, DDi, s);
