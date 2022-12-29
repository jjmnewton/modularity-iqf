P<x,y>:=PolynomialRing(Rationals(),2);
AP:=AffineSpace(P);
/* X(ns3) is P^1 with j-invariant x^3 */
/* j-invariant on X(ns5) is 5^3*y*(2*y+1)^3*(2*y^2+7*y+8)^3/(y^2+y-1)^5 */
fxy := x^3*(y^2+y-1)^5 - 5^3*y*(2*y+1)^3*(2*y^2+7*y+8)^3;
IC := ideal<P|fxy>;
C := Curve(AP,IC);

E:=EllipticCurve([0,0,-1,0,1]);
assert(CremonaReference(E) eq "225a1");

/* Check X(ns4,ns5) is isomorphic to elliptic curve 225a1 as clamed */

MapCtoE:=map<C->E|[-(x/5)*(y^2+y-1)^2,(2*y+1)*(2*y^2+7*y+8),y*(2*y+1)*(2*y^2+7*y+8)]>;
assert(IsInvertible(MapCtoE)); /*checks that map is birational from C to E */

