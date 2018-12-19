AttachSpec("superelliptic");

Br:=GF( 101^2);
w := Br.1;
Ri<x> := PolynomialRing(Br);


print ZetaFunction(2, x^3+w*x+ 1);



