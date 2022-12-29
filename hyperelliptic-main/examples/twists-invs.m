SetVerbose("Hyperelliptic", 1);

P<x>:=PolynomialRing(GF(7));
//P<x>:=PolynomialRing(GF(NextPrime(10^6)));
f:=x^8+1;
time twists := TwistsOfHyperellipticPolynomials(f);
print twists;
