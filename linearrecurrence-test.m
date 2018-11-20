load "linearrecurrence.m";

Br:=Integers(5^2);
Ri<x> := PolynomialRing(Br);
M := Matrix(Ri,[[x, x],[1,x+1]]);
L := [11,13];
R := [13,15];
s:=Floor(Log(4,R[#R]));
DDi:= UpperCaseDD(Br!1,Br!(2^s),2^s)^(-1);
LinearRecurrence(M, L, R, DDi, s);
print "expected";
