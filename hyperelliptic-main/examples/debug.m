SetVerbose("IsGL2Equiv", 0);

P<x> := PolynomialRing(Rationals());
P<x> := PolynomialRing(FiniteField(NextPrime(10^3)));

d := 5;
while true do
    print d;

    f1 := x^d - 1;
    C1 := HyperellipticCurve(f1);
    f2 := x^d + 1;
    C2 := HyperellipticCurve(f2);

    time test, Ts := IsIsomorphicHyperellipticCurves(C1, C1);
    time test, Ts := IsIsomorphicHyperellipticCurves(C1, C1 : geometric := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(C1, C1 : geometric := true, commonfield := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2);
    time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(C1, C2 : geometric := true, commonfield := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(C2, C2);
    time test, Ts := IsIsomorphicHyperellipticCurves(C2, C2 : geometric := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(C2, C2 : geometric := true, commonfield := true);

    g1 := x^d - x;
    D1 := HyperellipticCurve(g1);
    g2 := x^d + x;
    D2 := HyperellipticCurve(g2);

    time test, Ts := IsIsomorphicHyperellipticCurves(D1, D1);
    time test, Ts := IsIsomorphicHyperellipticCurves(D1, D1 : geometric := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(D1, D1 : geometric := true, commonfield := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(D1, D2);
    time test, Ts := IsIsomorphicHyperellipticCurves(D1, D2 : geometric := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(D1, D2 : geometric := true, commonfield := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(D2, D2);
    time test, Ts := IsIsomorphicHyperellipticCurves(D2, D2 : geometric := true);
    time test, Ts := IsIsomorphicHyperellipticCurves(D2, D2 : geometric := true, commonfield := true);

    d +:= 1;
end while;
