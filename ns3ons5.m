P<x,y,z>:=PolynomialRing(Rationals(),3);
AP:=AffineSpace(P);

/* X(ns3^\circ) is conic z^2=-3(x^2+12*x+12^2) with j-invariant x^3 */
/* j-invariant on X(ns5) is 5^3*y*(2*y+1)^3*(2*y^2+7*y+8)^3/(y^2+y-1)^5 */
fxy := x^3*(y^2+y-1)^5 - 5^3*y*(2*y+1)^3*(2*y^2+7*y+8)^3;
conic := z^2 + 3*(x^2+12*x+12^2);

/* define singular model for X(ns3^\circ, ns5) */
IC := ideal<P|fxy,conic>;
C := Curve(AP,IC);
assert(Genus(C) eq 3);

/* compute image of canonical map for C*/
CanMap := CanonicalMap(C);
D := CanonicalImage(C,CanMap);

/* check D still has genus 3, so curve was not hyperelliptic */
assert(Genus(D) eq 3);


/* check D is isomorphic to curve with simpler defining equation */
PD<X,Y,Z>:=AmbientSpace(D);
eqn := 9*X^4 + 19*X^2*Y^2 + Y^4 + 9*X^3*Z + 19*X^2*Y*Z + 22*X*Y^2*Z + 2*Y^3*Z + 10*X^2*Z^2 + 22*X*Y*Z^2 + 13*Y^2*Z^2 + 7*X*Z^3 + 12*Y*Z^3 + 11*Z^4;

Xns3ons5:= Curve(PD,eqn);
tf, Iso:=IsIsomorphic(D,Xns3ons5);
assert(tf);

AttachSpec("./hyperelliptic-main/magma/spec");
AttachSpec("./quartic-main/magma/spec");

/* compute automorphism group to find the bielliptic involution */
AutomorphismsOfPlaneQuartic(Xns3ons5);

/* here is the involution */
inv := iso<Xns3ons5->Xns3ons5|[X,-Y-Z,Z],[X,-Y-Z,Z]>;

/* Compute order of J(F_p) for J = Jac(Xns3circ,ns5), p small prime of good reduction */
primelist := [7,11,13];
Jacorderlist := [];
for p in primelist do
Fp:=GF(p);
Xpp:=ChangeRing(Xns3ons5,Fp);
assert(not IsSingular(Xpp));
CGp,phi,psi:=ClassGroup(Xpp);
Z:=FreeAbelianGroup(1);
degr:=hom<CGp->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CGp)]>;
JFp:=Kernel(degr); 
Append(~Jacorderlist,#JFp);
end for;

assert(GCD(Jacorderlist) eq 4); /* GCD of Jacobian orders is equal to 4 */

/* Check that 2-power-torsion in J(F_13) is C2 x C2*/
Fp:=GF(13);
Xpp:=ChangeRing(Xns3ons5,Fp);
assert(not IsSingular(Xpp));
CGp,phi,psi:=ClassGroup(Xpp);
ZAbGp:=FreeAbelianGroup(1);
degr:=hom<CGp->ZAbGp | [ Degree(phi(a))*ZAbGp.1 : a in OrderedGenerators(CGp)]>;
JFp:=Kernel(degr);
assert(pPrimaryInvariants(JFp,2) eq [2,2]);

load "./quadraticpoints-master/ozmansiksek.m";
load "./quadraticpoints-master/quadptssieve.m";

/* Search for some rational degree two divisors */
deg2,pls1,pls2,plsbig:=searchDiv2(Xns3ons5,10,true);

/* Here is the quotient map to Xns3ns5 */
Xns3ns5, quotMap := CurveQuotient(AutomorphismGroup(Xns3ons5,[inv]));

//We split deg2 into divisors pulled back from Xns3ns5(Q) and the rest
deg2pb:=[1*pl : pl in pls2 | quotMap(RepresentativePoint(pl)) in Xns3ns5(Rationals())] cat 
[1*pl1 + 1*pl2 : pl1 in pls1, pl2 in pls1 | inv(RepresentativePoint(pl1)) eq RepresentativePoint(pl2)];
deg2npb:=[DD : DD in deg2 | not DD in deg2pb];
assert Seqset(deg2) eq Seqset(deg2pb cat deg2npb);

assert(#pls1 eq 0); // there should be no rational points!
assert(#deg2npb eq 0); // no exceptional points either

//We convert to a minimal model for the elliptic curve Xns3ns5 and pullback a generator of the Mordell-Weil group to a degree 0 divisor on Xns3ons5
PO := Xns3ns5![71638930629/102022666304 , -5528833932101/153033999456 , -2703/464 , 1];
E,emap := EllipticCurve(Xns3ns5,PO);
MapDtoC := quotMap*emap;
Emin, eminmap := MinimalModel(E);
MapDtoEmin := MapDtoC*eminmap;
defMapmin := DefiningPolynomials(MapDtoEmin);
MapDtoEmincomp := map<Xns3ons5->Emin|defMapmin>;
MWE,phi,tf1,tf2:=MordellWeilGroup(Emin);
B := Pullback(MapDtoEmincomp,Place(phi(MWE.1)));
bp := Pullback(MapDtoEmincomp,Place(Zero(Emin))); 
B1 := B - bp; // B1 is the pull back to Jac(Xns3ons5) of a generator "D" as in Prop. 7.4.4

G:=AbelianGroup([0]);
divs := [2*B1]; // This divisor generates an Abelian group which contains 4 Jac_X(Q).
I := 4; 
genusC:=Genus(Emin);

auts:=[Transpose(Matrix(inv))]; // definition of the involution in format needed for Box's function

// Apply Box's Mordell--Weil sieve for the primes [43]
MWSieve(deg2,[43],Xns3ons5,G,divs,auts,genusC,deg2pb,deg2npb,I,bp);

// Output true means we succeeded and all non-pulled back degree two divisors already appear in deg2npb
assert(#deg2npb eq 0); // but we didn't have any non-pulled back divisors!
