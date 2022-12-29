/* Determining quadratic points on X(ns3^o,b5) */
/* A. Caraiani and J. Newton */

R<x> := PolynomialRing(Rationals());

/* Compute fibre of j-invariant on X(ns3,b5) at j=1728*/
fx := (x^6+250*x^3+5^5)^3-1728*x^15;
Factorisation(fx);

/* Compute Jacobian of model for X(ns3^o,b5) */
M := GenusOneModel(-3*x^4 - 6*x^3 + 3*x^2 - 30*x -75);
Jacobian(M);
/*We get the elliptic Curve defined by y^2 = x^3 + 3*x^2 - 720*x - 8100 */
CremonaReference(Jacobian(M));
/*45a2*/
K<a> := NumberField(x^2+3);
C := HyperellipticCurve(-3*x^4 - 6*x^3 + 3*x^2 - 30*x -75);  

/* C acquires rational points over K = Q(sqrt(-3)) */
CK<X,Y,Z> := BaseExtend(C,K); 

/* Define some useful points on CK */
infp := CK![1,a,0];
infm := CK![1,-a,0];
zerop := CK![0,5*a,1]; zerom := CK![0,-5*a,1];
P1 := CK![-2,-a,1]; Q1 := CK![-2,a,1];
P2 := CK![-5/2,5*a/4,1]; Q2 := CK![-5/2,-5*a/4,1];

/*Define rational divisor classes and their conjugates*/
E0 := Divisor(zerop) + Divisor(infp); 
E0c := Divisor(zerom) + Divisor(infm);
E1 := Divisor(P1) + Divisor(infp); 
E1c := Divisor(Q1) + Divisor(infm);
E2 := Divisor(P2) + Divisor(infp); 
E2c := Divisor(Q2)+Divisor(infm);

/*Check rationality*/
IsPrincipal(E0-E0c); IsPrincipal(E1-E1c); IsPrincipal(E2-E2c);  

/* Check that we have found all rational points on the Jacobian of C */
D0 := Jacobian(CK)!(E0 - Divisor(infp) - Divisor(infm));
D1 := Jacobian(CK)!(E1 - Divisor(infp) - Divisor(infm));
D2 := Jacobian(CK)!(E2 - Divisor(infp) - Divisor(infm));
D0 + D1 eq D2;
/* true */
/* check D0 D1 generate group order 4*/
IsZero(D0);IsZero(D1);IsZero(D2);

/*Find basis for L(Ei) for i = 0,1,2 */
for E in [E0,E1,E2] do
Basis(E);
end for;

/* Get equations 7.2.1-7.2.3 in text */
FF<x,y> := FunctionField(CK);
fx := -3*x^4 - 6*x^3 + 3*x^2 - 30*x -75;
AFF<u,v> := RingOfIntegers(FF);
AFFalpha<alpha> := PolynomialRing(AFF);
F0 := Numerator(Basis(E0)[1])-alpha*Denominator(Basis(E0)[1]);
F0x := (F0-AFF!y)^2 - AFF!fx;
G0 := (u*alpha^2 + (-2*a*u^2 - 10*a)*alpha + 6*u^2 - 33*u + 30);
assert(F0x eq u*G0);

F1 := Numerator(Basis(E1)[1])-alpha*Denominator(Basis(E1)[1]);
F1x := (F1-AFF!y)^2 - AFF!fx;
G1:= (u+2)*alpha^2 + (2*a)*(5-u^2)*alpha + 3*u*(2*u+5);
assert(F1x eq (u+2)*G1);

F2 := Numerator(Basis(E2)[1])-alpha*Denominator(Basis(E2)[1]);
F2x := (F2-AFF!y)^2 - AFF!fx;
G2 := (u+5/2)*alpha^2 + (2*a)*(5-u^2)*alpha +3*u*(2*u+4);
assert(F2x eq (u+5/2)*G2);
