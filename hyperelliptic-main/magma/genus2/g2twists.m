// freeze

/***
 *  Reconstruction and twists of Genus 2 Curves.
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2.1 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *  Copyright 2007-2020 R. Lercier & C. Ritzenthaler & J. Sijsling
 */

/***
 *
 * This file provides tools to obtain, in any fields, models of genus 2 curves
 * from absolute invariants, and automorphism groups from invariants or
 * genus 2 curves.
 *
 * In the geometric setting, i.e. when only one model is requested, routines
 * of this kind are available, except for very few cases in characteristic
 * 2 or 5 finite fields, in Kohel's CrvG2 package (cf D. Kohel's web page),
 * and in a less complete preliminary implementation by Howe et al.
 * (cf. MAGMA package). In the arithmetic case, that is when all the
 * twists are requested, we are not aware of any other implementation.
 *
 * All of this is based on numerous results due to Mestre, Cardona, Nart, etc.
 * Precise references are given in the enclosed bibliography and in the code.
 *
 *********************************************************************/

/***
 * Changes.
 *
 * 2007-09-26, v0.0 : R. Lercier, C. Ritzenthaler,
 *             Initial version.
 *
 * 2007-10-19, v1.0 : R. Lercier, C. Ritzenthaler,
 *             Placed under the Lesser General Public License
 *
 * 2009-02-25, v1.1 : R. Lercier, C. Ritzenthaler,
 *             Feedback by M. Harrison and E. Gonzalez-Jimenez.
 *
 * 2010-11-23, v1.2 : R. Lercier, C. Ritzenthaler,
 *             Feedback by J. Cannon.
 *
 * 2016-08-18, v1.3 : R. Lercier, C. Ritzenthaler,
 *             Add an option to avoid looking for a point on a conic over the
 *             rationals.
 *
 * 2020-11-13, v1.4 : R. Lercier, C. Ritzenthaler,
 *             Improved reconstruction for hyperelliptic curves defined
 *             over the rationals.
 *
 ********************************************************************/

/***
 * Bibliography
 *
 * [Mestre91] "Construction de courbes de genre 2 \`a partir de leurs modules"
 * Jean-Fran\,cois Mestre, in "Effective Methods in Algebraic Geometry",
 * vol 94 of Progress in Mathematics, 313-334, Birkhauser, 1991.
 *
 * [Cardona2003] "On the number of curves of genus 2 over a finite field",
 * G. Cardona, Finite Fields and Their Applications 9 (4), 505-526, 2003
 *
 * [ShVo2004] "Elliptic subfields and automorphisms of genus 2
 * function fields", T. Shaska, H. Volklein, Algebra, Arithmetic and
 * Geometry with Applications (West Lafayette, IN, 2000),703-723,
 * Springer, 2004
 *
 * [CaNaPu2005] "Curves of genus two over fields of even characteristic",
 * G. Cardona, E. Nart and J. Pujolas, Mathematische Zeitschrift,
 * 250, 177-201, Springer, 2005
 *
 * [CaQu2005] "Field of moduli and field of definition for curves of genus 2",
 * G. Cardona, J. Quer, Computational aspects of algebraic curves,  71-83,
 * Lecture Notes Ser. Comput., 13, World Sci. Publ., Hackensack, NJ, 2005.
 *
 * [CaNa2007] "Zeta Function and Cryptographic Exponent of Supersingular
 * Curves of Genus 2", G. Cardona, E. Nart, ArXiv e-prints 0704.1951C, 2007.
 *
 *********************************************************************/

/***
 * Exported intrinsics.
 *
 * intrinsic HyperellipticCurveFromIgusaInvariants(II::SeqEnum :
 *     RationalModel := false, minimize := true) -> CrvHyp, GrpPerm
 *
 * intrinsic HyperellipticCurveFromG2Invariants(GI::SeqEnum :
 *     RationalModel := false, minimize := true) -> CrvHyp, GrpPerm
 *
 * intrinsic TwistsFromG2Invariants(II::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
 *
 * intrinsic TwistsFromIgusaInvariants(JI::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
 *
 * intrinsic GeometricAutomorphismGroupFromIgusaInvariants(II::SeqEnum) -> GrpPerm
 *
 * intrinsic GeometricAutomorphismGroupGenus2Classification(FF::FldFin) -> SeqEnum, SeqEnum
 *
 ********************************************************************/

import "g2conic.m"          : Genus2ConicAndCubic;

import "../toolbox/diophantine.m" : ConicParametrization;

 /***
  *
  * Twists stuff in Characteristic 2 finite fields,
  * see [CaNaPu2005].
  *
  ********************************************************************/
function TraceOneElement(FF)
    if IsOdd(Degree(FF)) then
      return FF!1;
    end if;
    repeat
      x := Random(FF);
      t := Trace(x);
    until t ne 0;
    return x/t;
end function;

function G2ModelsInChar2FF_C2(GI : geometric := false)

    FF := Universe(GI);
    g1, g2, g3 := Explode(GI);
    x := PolynomialRing(FF).1;
    if not geometric then o := TraceOneElement(FF); end if;

    if g1 eq 0 then
	H1 := HyperellipticCurve([g2*x^5+g3*x^3+x,x]);
	if geometric then return [H1]; end if;
	H2 := HyperellipticCurve([g2*x^5+g3*x^3+o*x^2+x,x]);
	return [H1, H2];
    end if;
    F := Factorization(x^3+g3*x^2+g2*x+g1);
    splitF := Max([Degree(f[1]) : f in F]);
    if splitF eq 1 then
	rts := []; for f in F do
	    for i := 1 to f[2] do Append(~rts,Coefficient(f[1], 0)); end for;
	end for;
	a, b, c := Explode(rts);
	H1 := HyperellipticCurve([a*x^5+2*a*x^4+(c+b+a)*x^3+(2*b+c)*x^2+b*x,x*(x+1)]);
	if geometric then return [H1]; end if;
	H2 := HyperellipticCurve([a*x^5+(2*a+o)*x^4+(c+b+2*o+a)*x^3+(2*b+c+o)*x^2+b*x,x*(x+1)]);
	return [H1, H2];
    end if;
    if splitF eq 2 then
	for f in F do
	    if Degree(f[1]) eq 1 then
		a := Coefficient(f[1], 0);
	    else
		v := Coefficient(f[1], 0);
		u := Coefficient(f[1], 1);
	    end if;
	end for;
	H1 := HyperellipticCurve([a*x*(x^2+x+v/u^2)^2+(u*x+u)*(x^2+x+v/u^2), x^2+x+v/u^2]);
	if geometric then return [H1]; end if;
	H2 := HyperellipticCurve([(a*x+o)*(x^2+x+v/u^2)^2+(u*x+u)*(x^2+x+v/u^2), x^2+x+v/u^2]);
	return [H1, H2];
    end if;
    if g2 eq g3^2 then
	s := g1+g2*g3; t := 0; a := 0; b := g1+g2*g3; c := g3*(g1+g2*g3);
    else
	den := (g1+g2*g3);
	s := (g2+g3^2)^3/den^2; t := s; a := (g1+g3^3)*(g2+g3^2)^2/den^2; b := a;
	c := (g2+g3^2)^3*(g1*(g2+g3^2)^2+g3*(g1+g3^3)^2)/den^4;
    end if;
    H1 := HyperellipticCurve([a*x^5+b*x^4+(c+a*t)*x^3+(a*s+b*t)*x^2+(c*t+b*s)*x+c*s,x^3+t*x+s]);
    if geometric then return [H1]; end if;
    H2 := HyperellipticCurve([o*x^6+a*x^5+(2*o*t+b)*x^4+(2*o*s+a*t+c)*x^3+(a*s+t*(o*t+b))*x^2+(s*(o*t+b)+t*(o*s+c))*x+s*(o*s+c), x^3+t*x+s]);
    return [H1, H2];
end function;

function G2ModelsInChar2FF_C2bis(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    _, g2, _ := Explode(GI);

    H1 := HyperellipticCurve([g2*x^5+x,x]);
    if geometric then return [H1]; end if;

    o := TraceOneElement(FF);
    H2 := HyperellipticCurve([g2*x^5+o*x^2+x,x]);
    return [H1, H2];
end function;

function G2ModelsInChar2FF_C2xC2(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    _, g2, g3 := Explode(GI);
    a := g3; b := Sqrt(g2); c := b;

    H := HyperellipticCurve([a*x^5+2*a*x^4+a*x^3+c*x^2+c*x, x^2+x]);
    if geometric then return [H]; end if;

    o := TraceOneElement(FF);

    if Trace(g3) eq 0 then
	return [H,
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+a)*x^3+(c+o)*x^2+c*x,x^2+x]),
	    HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o]),
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+2*a*o+a)*x^3+(o^2+c+o+a*o+(o+a)*o)*x^2+(o^2+c+(o+a*o)*o)*x+(o^2+c)*o, x^2+x+o])
	    ];
    end if;
    return [H,
	HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o])
	];
end function;

function G2ModelsInChar2FF_C2xS3(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    _, _, g3 := Explode(GI);

    a := g3; b := a; c := b;

    H := HyperellipticCurve([a*x^5+2*a*x^4+a*x^3+c*x^2+c*x, x^2+x]);
    if geometric then return [H]; end if;

    o := TraceOneElement(FF);

    if Trace(g3) eq 0 then
	quads := [H,
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+a)*x^3+(c+o)*x^2+c*x,x^2+x]),
	    HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o]),
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+2*a*o+a)*x^3+(o^2+c+o+a*o+(o+a)*o)*x^2+(o^2+c+(o+a*o)*o)*x+(o^2+c)*o, x^2+x+o])
	    ];
    else
	quads := [H,
	    HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o])
	    ];
    end if;

    S := Random(FF);
    while not IsIrreducible(x^3+S*x+S) do S := Random(FF); end while;

    t := S; s := S; a := g3*S; b := g3*S; c := g3*S*(S+1);
    cubs := [
	HyperellipticCurve([a*x^5+b*x^4+(c+a*t)*x^3+(a*s+b*t)*x^2+(c*t+b*s)*x+c*s, x^3+t*x+s]),
	HyperellipticCurve([o*x^6+a*x^5+(2*o*t+b)*x^4+(2*o*s+a*t+c)*x^3+(a*s+t*(o*t+b))*x^2+(s*(o*t+b)+t*(o*s+c))*x+s*(o*s+c), x^3+t*x+s])
	];

    return quads cat cubs;
end function;

function G2ModelsInChar2FF_M32(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    _, _, g3 := Explode(GI);
    sg3 := Sqrt(g3);
    if geometric then return [HyperellipticCurve([sg3*x^5+sg3*x^3, 1])]; end if;

    o := TraceOneElement(FF);

    E := sg3^4*x^16+sg3^4*x^8+sg3^2*x^2+sg3*x;
    KE := Roots(E);
    V := VectorSpace(GF(2),Degree(FF));
    W, pi := quo< V | [ V!Eltseq(Evaluate(E,x)) where x is FF!Eltseq(v) : v in Basis(V) ] >;
    K := [FF!Eltseq(w@@pi) : w in W];

    twists := [];
    for b in K do
	H := HyperellipticCurve([sg3*x^5+b*x^4+sg3*x^3, 1]);
	twists cat:= [H];

	notwists := false;
	for k in KE do
	    if Trace(sg3*k[1]^5+b*k[1]^4+sg3*k[1]^3) eq 1 then notwists := true; break; end if;
	end for;

	if notwists eq false then
	    twists cat:= [HyperellipticCurve([sg3*x^5+b*x^4+sg3*x^3+o, 1])];
	end if;
    end for;

    return twists;
end function;

function G2ModelsInChar2FF_M160(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    if geometric then return [HyperellipticCurve([x^5, 1])]; end if;

    o := TraceOneElement(FF);
    prim := PrimitiveElement(FF);

    if (Degree(FF) mod 4) ne 0 then
	if (Degree(FF) mod 2) ne 0 then
	    H := HyperellipticCurve([x^5, 1]);
	    return [H,
		HyperellipticCurve([x^5+x^4, 1]),
		HyperellipticCurve([x^5+x^4+1, 1])
		];
	end if;
	F4 := GF(2^2); Embed(F4, FF); u := FF!F4.1;
	H := HyperellipticCurve([x^5, 1]);
	return [H,
	    HyperellipticCurve([x^5+x^4, 1]),
	    HyperellipticCurve([x^5+u*x^4, 1]),
	    HyperellipticCurve([x^5+(u+1)*x^4, 1]),
	    HyperellipticCurve([x^5+x^4+u, 1])
	    ];
    end if;

    A := Setseq(Seqset([prim^i : i in [0..4]]));
    MU5 := [r[1] : r in Roots(x^5-1)];

    twists := [];
    for a in A do
	H := HyperellipticCurve([a*x^5, 1]);
	twists cat:= [H];
	twists cat:= [HyperellipticCurve([a*x^5+o, 1])];
    end for;

    E1 := x^16+x;
    V := VectorSpace(GF(2),Degree(FF));
    W, pi := quo< V | [ V!Eltseq(Evaluate(E1,x)) where x is FF!Eltseq(v) : v in Basis(V) ] >;

    W := [w : w in W | w ne W!0];
    for i := 1 to 3 do
	a := FF!Eltseq(W[1]@@pi);
	H := HyperellipticCurve([x^5+a*x^4, 1]);
	twists cat:= [H];
	for mu in MU5 do
	    W := Setseq(Seqset(W) diff {pi(V!Eltseq(a*mu))});
	end for;
    end for;

    return twists;
end function;

/*
 * Genus 2 HyperElliptic Curves Twists in finite fields of characteristic > 2
 *
 ***************************************************************************/
function G2NonIsomorphic(Ecs)
   crvs := [];
   for E1 in Ecs do
       old := &or[ IsIsomorphicHyperellipticCurves(E1,E0) : E0 in crvs ];
       if not old then Append(~crvs,E1); end if;
  end for;
  return crvs;
end function;

function ClebschMestreConicAndCubic(JI : RationalModel := false, minimize := true)

    FF := Universe(JI);
    J2,J4,J6,_,J10 := Explode(JI);

    p := Characteristic(Parent(J2));
    P3 := PolynomialRing(Parent(J2), 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;

    /* Clebsch-Mestres conics & cubics, as a function of Igusa Invariants */
    if p eq 5 then

	if J2 eq 0 then

	    /* J4 <> 0 */
	    R2 := J6^5+3*J10*J4^5+3*J6^3*J4^3+J6*J4^6;
	    if not IsSquare(R2) then
		J4 *:= R2^2; J6 *:= R2^3; J10 *:= R2^5; R2 *:= R2^15;
	    end if;
	    R := Sqrt(R2);
	    L := J6*x1^2+4*J4^2*x2*x1+4*x3^2*J4^2;
	    M := (3*J4^4+4*J6^2*J4)*x1^2*x2+(4*J4^4+3*J6^2*J4)*x1*x3^2+
		2*J4^5*x2^3+J6*J4^2*x1^3+4*x1*J6*J4^3*x2^2+4*x3*x1^2*R;
	else

	    L := J2*x1^2+((J4*J2^2+2*J4^2+J2^4+4*J2*J6)*x2+(2*J2*J4^2+J6*J4+4*J2^5)*x3)*x1+(J4^
		2*J2^3+4*J2^7+3*J6*J4^2+3*J4*J2^5+2*J4^3*J2)*x2^2+(3*J2^3*J10+(3*J4+3*J2^2)*J6
		^2+(J2*J4^2+4*J2^5+J2^3*J4)*J6+2*J2^8+2*J2^6*J4+3*J2^2*J4^3+2*J2^4*J4^2)*x3*x2
		+((4*J4*J2^2+3*J2^4)*J10+2*J6^3+3*J6^2*J2^3+(2*J4*J2^4+3*J2^6+3*J4^2*J2^2)*J6+
		4*J2^9+J4^3*J2^3)*x3^2;

	    M := (3*J4*J2+3*J2^3)*x1^3+(((2*J2^3+2*J4*J2)*J6+3*J4*J2^4+J2^6+2*J4^3+2*J4^2*J2^2)
		*x2+(4*J6^2*J2+(J4^2+3*J4*J2^2+J2^4)*J6+2*J4^3*J2+J4^2*J2^3+4*J4*J2^5+J2^7)*x3
		)*x1^2+((4*J10*J2^4+2*J6^2*J2^3+(4*J2^6+3*J4^3+J4^2*J2^2+2*J4*J2^4)*J6+2*J4^2*
		J2^5+J4^4*J2+3*J4^3*J2^3+J4*J2^7)*x2^2+((4*J2^5+3*J2^3*J4)*J10+(J4*J2^2+2*J2^4
		+3*J4^2)*J6^2+(3*J4*J2^5+3*J2^7+2*J4^2*J2^3+J4^3*J2)*J6+2*J2^10+2*J4^4*J2^2+J4
		*J2^8+3*J4^2*J2^6)*x3*x2+((4*J4^2*J2^2+J4*J2^4+3*J6*J2^3)*J10+(2*J4+4*J2^2)*J6
		^3+(4*J2*J4^2+2*J2^5)*J6^2+(J2^2*J4^3+2*J2^4*J4^2+J2^6*J4)*J6+3*J2^11+2*J4^3*
		J2^5+J4^4*J2^3+2*J4^2*J2^7)*x3^2)*x1+((J4*J2^5+J2^7+J6*J2^4)*J10+(3*J2^6+2*J4^
		2*J2^2+J4*J2^4)*J6^2+(3*J4^3*J2^3+J2^9+2*J4^2*J2^5)*J6+2*J4*J2^10+2*J2^12+3*J4
		^3*J2^6+4*J4^5*J2^2+3*J4^2*J2^8)*x2^3+(((4*J2^5+2*J2^3*J4)*J6+J2^6*J4+4*J2^8+
		J2^2*J4^3+4*J2^4*J4^2)*J10+(2*J2^4+2*J4*J2^2)*J6^3+(J4*J2^5+4*J2^7+J4^2*J2^3+4
		*J4^3*J2)*J6^2+(4*J2^4*J4^3+2*J2^10+2*J4^2*J2^6+4*J4^4*J2^2+3*J4*J2^8)*J6+J4^5
		*J2^3+3*J4^2*J2^9+3*J4^3*J2^7+2*J2^13)*x3*x2^2+((J6^2*J2^3+(J4^2*J2^2+2*J2^6+2
		*J4*J2^4)*J6+2*J4^3*J2^3+J2^9+4*J4*J2^7)*J10+3*J6^4*J2^2+(2*J2^3*J4+J2^5+4*J2*
		J4^2)*J6^3+(3*J2^8+4*J2^4*J4^2+3*J2^2*J4^3)*J6^2+(J2^11+J4*J2^9+3*J4^4*J2^3)*
		J6+2*J4^5*J2^4+3*J4^4*J2^6+2*J4^2*J2^10)*x3^2*x2+(3*J10^2*J2^5+((4*J4*J2^2+2*
		J2^4)*J6^2+(3*J4*J2^5+3*J4^2*J2^3+J2^7)*J6+J4^2*J2^6+3*J2^4*J4^3+2*J4*J2^8+3*
		J2^10)*J10+(J2^3+J4*J2)*J6^4+(J4^2*J2^2+3*J2^6+3*J4*J2^4)*J6^3+(2*J4^2*J2^5+2*
		J4^3*J2^3+4*J4*J2^7+J2^9)*J6^2+(3*J4^2*J2^8+4*J4^3*J2^6+4*J4^4*J2^4)*J6+J2^15+
		3*J4*J2^13+3*J4^2*J2^11+J4^4*J2^7+2*J4^3*J2^9)*x3^3;
        end if;
        phi := ConicParametrization(L : RationalPoint := RationalModel);

        f := Evaluate(M, DefiningPolynomials(phi));
        f := UnivariatePolynomial(Evaluate(f, Parent(f).2, 1));

        return HyperellipticCurve(f);

    end if;

    f := Genus2ConicAndCubic(JI);

    if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
        f := MinRedBinaryForm(f : degree := 6);
    end if;

    return HyperellipticCurve(f);

end function;

/*
   y^2 = x^6 - 1 in char <> 3, 5,
   see [CaNa2007].
*/
function G2ModelsInFF_2D12(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    H0 := HyperellipticCurve(x^6 - 1);
    if geometric then return [H0]; end if;

    twists := [H0, QuadraticTwist(H0)];

    q := #FF;
    prim := PrimitiveElement(FF);
    t := prim;
    H := HyperellipticCurve(x^6 - t^3);
    twists cat:= [H,  QuadraticTwist(H)];

    t := prim;
    H := HyperellipticCurve(x*(t*x^2+3)*(3*t*x^2+1));
    twists cat:= [H,  QuadraticTwist(H)];

    Fq4 := GF(q^4); t := PrimitiveElement(Fq4);
    a := t^((q^2+1) div 2); b := a^q; c := -b; d := a;
    Ctwist := (Transformation(ChangeRing(H0,Fq4),[a,b,c,d]));
    pol := HyperellipticPolynomials(Ctwist);
    H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
    twists cat:= [H,  QuadraticTwist(H)];

    if IsSquare(FF!-3) then

	t := prim;
	H := HyperellipticCurve(x^6 - t^2);
	twists cat:= [H,  QuadraticTwist(H)];

	t := prim;
	H := HyperellipticCurve(x^6 - t);
	twists cat:= [H,  QuadraticTwist(H)];

    else

	Fq6 := GF(q^6); t := PrimitiveElement(Fq6);
	a := t^((q^4+q^2+1) div 3); b := a^4; c := a^q*t^((q^6-1) div 3); d := b^q*t^(((q^6-1) div 3));
	Fq6Pol := PolynomialRing(Fq6); X := Fq6Pol.1;
        pol := (a*X+b)^6-(c*X+d)^6;
        H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	Fq12 := GF(q^12); t := PrimitiveElement(Fq12);
	a := t^(((q^4+q^2+1)*(q^6+1)) div 6); b := a^7;
	c := a^q*t^((q^12-1) div 6); d := b^q*t^(((q^12-1) div 6));
	Fq12Pol := PolynomialRing(Fq12); X := Fq12Pol.1;
        pol := (a*X+b)^6-(c*X+d)^6;
        H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];
    end if;

    return G2NonIsomorphic(twists);
end function;

/*
   y^2 = x^5 - x in char 5,
   see [CaNa2007].
 */
function G2ModelsInChar5FF_G240(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    deg := Degree(FF);

    H0 := HyperellipticCurve(x^5 - x);
    twists := [H0];
    if geometric then return twists; end if;

    prim := PrimitiveElement(FF);
    t := TraceOneElement(FF);
    H := HyperellipticCurve(x^5-x-t);
    twists cat:= [H,  QuadraticTwist(H)];

    ok := false;
    while not ok do
	t := Random(FF);
	pol := x^6+t*x^5+(1-t)*x+2;
	ok := IsIrreducible(pol);
    end while;
    H1 := HyperellipticCurve(pol);
    twists cat:= [H1];

    if (deg mod 2) eq 1 then

	twists cat:= [HyperellipticCurve(x^5 - 2*x)];
	twists cat:= [HyperellipticCurve(x^5 - 4*x)];
	twists cat:= [HyperellipticCurve((x^2+2)*(x^2+4*x+2)*(x^2-4*x+2))];

	ok := false;
	while not ok do
	    t := Random(FF);
	    p1 := x^3-t*x^2+(t-3)*x+1;
	    ok := IsIrreducible(p1);
	end while;
	t := (3+2*t)/(3+3*t);
	p2 := x^3-t*x^2+(t-3)*x+1;
	twists cat:= [HyperellipticCurve(p1*p2)];

	return twists;
    end if;

    twists cat:= [QuadraticTwist(H0)];
    twists cat:= [QuadraticTwist(H1)];
    twists cat:= [HyperellipticCurve(x^5-prim^2*x)];

    H := HyperellipticCurve(x^5-prim*x);
    twists cat:= [H,  QuadraticTwist(H)];

    t := prim;
    H := HyperellipticCurve((x^2-t)*(x^4+6*t*x^2+t^2));
    twists cat:= [H];

    sq := Roots(x^2-3)[1][1];
    H := HyperellipticCurve((x^3-prim)*(x^3-(15*sq-26)*prim));
    twists cat:= [H,  QuadraticTwist(H)];

    return twists;
end function;

forward G2ModelsInFF_G48;

/*
   y^2 = x^5 - x in char <> 5,
   see [CaNa2007].
*/
function G2ModelsInFF_G48(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    H0 := HyperellipticCurve(x^5 - x);
    if geometric then return [H0]; end if;

    twists := [H0, QuadraticTwist(H0)];

    q := #FF;
    prim := PrimitiveElement(FF);
    ret, sqr := IsSquare(FF!-1);
    if ret then

	t := prim;
	H := HyperellipticCurve(x^5 -t*x);
	twists cat:= [H,  QuadraticTwist(H)];

	t := prim;
	H := HyperellipticCurve(x^5 -t^2*x);
	twists cat:= [H,  QuadraticTwist(H)];

	Fq8 := GF(q^8); t := PrimitiveElement(Fq8);
	a := t^((q^2+1)*(q^4+1) div 4); i := a^(q^2-1);
	b := a^5; c := a^q/i; d := b^q/i;
	Fq8Pol := PolynomialRing(Fq8); X := Fq8Pol.1;
	pol := (a*X+b)^5*(c*X+d)-(a*X+b)*(c*X+d)^5;
	H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	ok := false;
	while not ok do
	    t := Random(FF);
	    p1 := x^3-t*x^2+(t-3)*x+1;
	    ok := IsIrreducible(p1);
	end while;
	t := FF!((18+(5*sqr-3)*t)/((5*sqr+3)-2*t));
	p2 := x^3-t*x^2+(t-3)*x+1;
	H := HyperellipticCurve(p1*p2);
	twists cat:= [H,  QuadraticTwist(H)];

    else

	H := HyperellipticCurve(x^5 + x);
	twists cat:= [H,  QuadraticTwist(H)];

	Fq4 := GF(q^4); t := PrimitiveElement(Fq4);
	a := t^((q^2+1) div 2); b := a^q; c := -b; d := a;
	Ctwist := (Transformation(ChangeRing(H0,Fq4),[a,b,c,d]));
	pol := HyperellipticPolynomials(Ctwist);
	H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	Fq8 := GF(q^8); t := PrimitiveElement(Fq8);
	a := t^((q^2+1)*(q^4+1) div 4); i := -a^(q^2-1);
	b := a^5; c := a^q/i; d := b^q/i;
	Fq8Pol := PolynomialRing(Fq8); X := Fq8Pol.1;
	pol := (a*X+b)^5*(c*X+d)-(a*X+b)*(c*X+d)^5;
	H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	repeat
	    repeat
		t := Random(FF);
		ret, s := IsSquare(-2-t^2);
	    until ret;
	    pol := x^6-(t+3)*x^5+5*(2+t-s)/2*x^4+5*(s-1)*x^3+5*(2-t-s)/2*x^2+(t-3)*x+1;
	    ok := IsIrreducible(pol);
	until ok;
	H := HyperellipticCurve(pol);
	twists cat:= [H,  QuadraticTwist(H)];
   end if;

   return G2NonIsomorphic(twists);
end function;

/*
   y^2 = x^5 - 1,
   see [CaNa2007].
*/
function G2ModelsInFF_C10(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    H1 := HyperellipticCurve(x^5 - 1);
    if geometric then return [H1]; end if;

    prim := PrimitiveElement(FF);
    H2 := QuadraticTwist(H1);
    twists :=  [H1, H2];
    if (GF(5)!Characteristic(FF))^Degree(FF) ne 1 then
	return twists;
    end if;

    A := Setseq(Seqset([prim^i : i in [0..4]]));
    for a in A do
	H1 := HyperellipticCurve(a*x^5-1);
	H2 := QuadraticTwist(H1);
	twists cat:=  [H1, H2];
    end for;

    return G2NonIsomorphic(twists);

end function;

/* y^2 = 1/t*x^6+x^4+x^2+1 in char 3, and its twists */
function G2ModelsInChar3FF_D12(JI : geometric := false)

    FF := Universe(JI);
    x := PolynomialRing(FF).1;
    J2, J4, J6, _, J10 := Explode(JI);

    _, t := IsPower(-J2^3/J6, 3);

    H0 := HyperellipticCurve(x^6+t*x^4+(t-1)*x^3+t*x^2+1);
    if geometric then return [H0]; end if;

    twists := [H0, QuadraticTwist(H0)];

    q := #FF; Fq2 := GF(q^2);
    a := PrimitiveElement(Fq2); b := a^q; c := b; d := a;
    Ctwist := (Transformation(ChangeRing(H0,Fq2),[a,b,c,d]));
    H := HyperellipticCurve(Parent(x)!(HyperellipticPolynomials(Ctwist)));
    twists cat:= [H,  QuadraticTwist(H)];

    ok := false;
    while not ok do
	a0 := Random(FF);
	a1 := Random(FF);
	pol := x^3 + a1*x + a0;
	ok := IsIrreducible(pol);
    end while;
    Fq3 := ext<FF | pol>;
    a := Fq3.1; b:=-a^q-a; c:=a^q; d:=-c^q-c;
    Ctwist:=(Transformation(ChangeRing(H0,Fq3),[a,b,c,d]));
    H := HyperellipticCurve(Parent(x)!(HyperellipticPolynomials(Ctwist)));
    twists cat:= [H,  QuadraticTwist(H)];

    return twists;
end function;

/*
   y^2 = x^6 + x^3 + t in char <> 3,
   see [CaNa2007].
*/
function G2ModelsInFF_D12(JI : geometric := false, minimize := true)

    FF := Universe(JI);
    x := PolynomialRing(FF).1;
    p := Characteristic(FF);

    J2, J4, J6, _, J10 := Explode(JI);
    if p eq 5 then
	a := -1-J4/J2^2;
    else
	C2, C4, C6, C10 := Explode(
	    IgusaClebschToClebsch([8*J2,4*J2^2-96*J4,8*J2^3-160*J2*J4-576*J6, 4096*J10]));
	a := (3*C4*C6-C10)/50/C10;
    end if;

    f := x^6+x^3+a;
    if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
        f := MinRedBinaryForm(f : degree := 6);
    end if;

    H := HyperellipticCurve(f); twists := [ H ];
    if geometric then return twists; end if;

    n := Degree(FF);
    prim := PrimitiveElement(FF);
    q := #FF;

    if q mod 3 eq 2 then

	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;

	A := Roots(x^3-a)[1][1];
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4/A;
	    ok := not IsSquare(delta);
	end while;
	/* To be improved, but ok. */
	Fq2 := GF(q^2); Pq2 := PolynomialRing(Fq2); X := Pq2.1;
	sq := Sqrt(Fq2!delta);
	theta1 := (t+sq)/2;
	theta2 := (t-sq)/2;
	f := Parent(x)!((X-theta1)^6/theta1^3-(X^2-t*X+1/A)^3+a*theta1^3*(X-theta2)^6);
	H := HyperellipticCurve(f);
	twists cat:= [H];
	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;

	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4*a;
	    if not IsSquare(delta) then
		sq := Sqrt(Fq2!delta);
		theta := (t+sq)/2;
		ok := IsIrreducible(X^3-theta);
	    end if;
	end while;
	/* To be improved, but ok. */
	eta :=  Roots(X^2+X+1)[1][1];
	f := Parent(x)!((X-eta)^6*theta-(X^2+X+1)^3+a*(X-eta^2)^6/theta);
	H := HyperellipticCurve(f);
	twists cat:= [H, QuadraticTwist(H)];

	return twists;
    end if;

    if IsPower(a, 3) then
	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;
    else
	twists cat:= [QuadraticTwist(H)];
    end if;

    if not IsPower(a, 3) then
	t := a;
    else
	t :=  prim;
    end if;

    H := HyperellipticCurve(x^6 + t * x^3 + a * t^2);
    twists cat:= [H];
    if IsPower(a, 3) then
	twists cat:= [QuadraticTwist(H)];
    else
	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;
    end if;

    if IsPower(a, 3) then
	A := Roots(x^3-a)[1][1];
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4/A;
	    ok := not IsSquare(delta);
	end while;
	/* To be improved, but ok. */
	Fq2 := GF(q^2); Pq2 := PolynomialRing(Fq2); X := Pq2.1;
	sq := Sqrt(Fq2!delta);
	theta1 := (t+sq)/2;
	theta2 := (t-sq)/2;
	f := Parent(x)!((X-theta1)^6/theta1^3-(X^2-t*X+1/A)^3+a*theta1^3*(X-theta2)^6);
	H := HyperellipticCurve(f);
	twists cat:= [H];
    else
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4/a;
	    ok := not IsSquare(delta);
	end while;
	/* To be improved, but ok. */
	Fq2 := GF(q^2); Pq2 := PolynomialRing(Fq2); X := Pq2.1;
	sq := Sqrt(Fq2!delta);
	theta1 := (t+sq)/2;
	theta2 := (t-sq)/2;
	f := Parent(x)!((X-theta1)^6/theta1-(X^2-t*X+1/a)^3+a*theta1*(X-theta2)^6);
	H := HyperellipticCurve(f);
	twists cat:= [H];
    end if;

    if IsSquare(a) then
	twists cat:= [QuadraticTwist(H)];
    end if;

    return twists;

end function;

/*
   y^2 = x^5 + x^3 + t*x,
   see [CaNa2007].
*/
function G2ModelsInFF_D8(JI : geometric := false, minimize := true)

    FF := Universe(JI);
    x := PolynomialRing(FF).1;
    p := Characteristic(FF);

    J2, J4, J6, _, J10 := Explode(JI);

    if p eq 3 then
	t := -J2^2/J4;
    elif p eq 5 then
	t:= 1+J4/J2^2;
    else
	C2, C4, C6, C10 := Explode(
	    IgusaClebschToClebsch([8*J2, 4*J2^2-96*J4,8*J2^3-160*J2*J4-576*J6, 4096*J10]));
	t := (8*C6*(6*C4-C2^2)+9*C10)/900/C10;
    end if;

    f := x^5+x^3+t*x;
    if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
        f := MinRedBinaryForm(f : degree := 6);
    end if;

    if geometric then return [HyperellipticCurve(f)]; end if;

    if IsSquare(t) then
	/* 1-z0^2*t = s0^2*t*v */

	/* v a square */
	v := 1;  z0 := 1/Sqrt(t); s0 := 0;

	Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	    v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));

	prim := PrimitiveElement(FF);
	Cpt:=QuadraticTwist(Cp);
	twists := [Cp, Cpt];

	ok := false;
	while not ok do
	    v := Random(FF);
	    if v eq 0 or not IsSquare(v) then continue; end if;
	    z0 := Random(FF);
	    if z0^2*t eq 1 or not IsSquare(1-z0^2*t) then continue; end if;
	    if IsSquare((1-z0*Sqrt(t))/2) then continue; end if;
	    ok := true;
	end while;
	s0 := Sqrt((1-z0^2*t)/v/t);

	Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	    v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));
	twists cat:= [Cp];

	/* v not a square */
	v := prim; s0 := 0; z0 := 1/Sqrt(t);

	Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	    v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));
	Cm:=HyperellipticCurve((1-2*t*z0)*x^6+(8*s0*t*v)*x^5+v*(3+10*t*z0)*x^4+
	    v^2*(3+10*t*z0)*x^2-8*s0*t*v^3*x+v^3*(1-2*t*z0));
	twists cat:= [Cp, Cm];

	return twists;
    end if;

    /* 1-z0^2*t = s0^2*t*v (To be improved) */
    AS:=AffineSpace(FF,2); s := AS.1; z := AS.2;
    v := 1;
    Q:=Curve(AS, s^2*t*v+z^2*t-1);
    pt:=Random(Points(Q));
    s0:=pt[1];z0:=pt[2];

    Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));

    prim := PrimitiveElement(FF);

    Cpt:=QuadraticTwist(Cp);
    twists := [Cp, Cpt];

    v := prim;
    Q:=Curve(AS, s^2*t*v+z^2*t-1);
    pt:=Random(Points(Q));
    s0:=pt[1];z0:=pt[2];

    Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));
    twists cat:= [Cp];

    return twists;
end function;


/* V4 case,
   see [ShVo2004], [CaQu2005] */
function G2ModelsInFF_V4(JI : geometric := false, minimize := true)

    FF := Universe(JI);

    x := PolynomialRing(FF).1;
    J2, J4, J6, _, J10 := Explode(JI);

    Au:=J2^5*J4^2-64*J2^3*J4^3+1024*J2*J4^4+3*J2^6*J6-202*J2^4*J4*J6+4014*J2^2*J4^2*J6
	-20160*J4^3*J6+666*J2^3*J6^2-20520*J2*J4*J6^2+48600*J6^3-30*J2^4*J10+2800*J2^2*J4*J10
	-192000*J4^2*J10-360000*J2*J6*J10;

    Bu:=2*J2^4*J4*J6-114*J2^2*J4^2*J6+1344*J4^3*J6+6*J2^3*J6^2+216*J2*J4*J6^2-3240*J6^3+
	18*J2^4*J10-1040*J2^2*J4*J10+12800*J4^2*J10+4800*J2*J6*J10;

    Av:=J2^6*J4^2-96*J2^4*J4^3+3072*J2^2*J4^4-32768*J4^5+3*J2^7*J6-164*J2^5*J4*J6
	+1250*J2^3*J4^2*J6+29760*J2*J4^3*J6+858*J2^4*J6^2-22680*J2^2*J4*J6^2
	-172800*J4^2*J6^2+81000*J2*J6^3+1176*J2^5*J10-79600*J2^3*J4*J10
	+1344000*J2*J4^2*J10-72000*J2^2*J6*J10-12960000*J4*J6*J10-134400000*J10^2;

    Bv:=3*J2^3*J4^2*J6-160*J2*J4^3*J6+J2^4*J6^2-36*J2^2*J4*J6^2+3456*J4^2*J6^2-1188*J2*J6^3
	+24*J2^3*J4*J10-1280*J2*J4^2*J10+160*J2^2*J6*J10+105600*J4*J6*J10+640000*J10^2;

    u:=Au/Bu;v:=Av/Bv;
    if u ne 0 then
	t:=v^2-4*u^3;
	a0:=v^2+u^2*v-2*u^3;
	a1:=2*(u^2+3*v)*(v^2-4*u^3);
	a2:=(15*v^2-u^2*v-30*u^3)*(v^2-4*u^3);
	a3:=4*(5*v-u^2)*(v^2-4*u^3)^2;
    else
	t:=FF!1;
	a0:=1+2*v;
	a1:=2*(3-4*v);
	a2:=15+14*v;
	a3:=4*(5-4*v);
    end if;

    f := a0*x^6+a1*x^5+a2*x^4+a3*x^3+t*a2*x^2+t^2*a1*x+t^3*a0;
    if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
        f := MinRedBinaryForm(f : degree := 6);
    end if;
    if geometric then return [HyperellipticCurve(f)]; end if;

    H1 := HyperellipticCurve(f);
    if geometric then return [H1]; end if;

    q := #FF;

    if IsSquare(t) then
	Fq2 := GF(q^2);
	a:=PrimitiveElement(Fq2);
	b:=a^q*Sqrt(t);c:=a^q;d:=a*Sqrt(t);
	C2:=ChangeRing(H1,Fq2);
	Ctwist:=(Transformation(C2,[a,b,c,d]));
	f2:=Parent(x)!(HyperellipticPolynomials(Ctwist));
	H2:=HyperellipticCurve(f2);
	return [H1, QuadraticTwist(H1),
	        H2, QuadraticTwist(H2)];
    end if;

    Fq4 := GF(q^4);
    s:=PrimitiveElement(Fq4);
    a := s^((q^2+1) div 2);
    sq := Sqrt(Fq4!t);
    c := a^q;
    b := sq*c;
    d := sq*c^q;
    C2:=ChangeRing(H1,Fq4);
    Ctwist:=(Transformation(C2,[a,b,c,d]));
    f2:=Parent(x)!(HyperellipticPolynomials(Ctwist));
    H2:=HyperellipticCurve(f2);
    return [H1, H2];

end function;

/*
   Generic case.

   Everything here is based on [Mestre91], especially the conic and
   cubic used in finite fields of characteristic 3 or > 5.

   In characteristic 5, we had to face difficulties, mostly because
   the covariants used to define the cubics and conics given
   in [Mestre91] are no more a basis, and we had to consider other covariants.
   This yields new conics and cubics that we use here.

 */
function G2ModelsInFF_C2(JI : geometric := false, RationalModel := false, minimize := true)

    FF := Universe(JI);
    x := PolynomialRing(FF).1;
    p := Characteristic(FF);
    J2, J4, J6, _, J10 := Explode(JI);

    if p eq 5 and J2 eq 0 and J4 eq 0 then
        _, _, g3 := Explode(IgusaToG2Invariants(JI));
	repeat
	    c := Random(FF);
	    ret, a := IsPower(3*c^2/g3, 3);
	until c ne 0 and ret;
        f := x^5+c*x^2+a*c;

        if minimize and Type(BaseRing(Parent(f))) in {RngInt, FldRat} then
            f := MinRedBinaryForm(f : degree := 6);
        end if;
        H := HyperellipticCurve(f);
    else
	H := ClebschMestreConicAndCubic(JI : RationalModel := RationalModel, minimize := minimize);
    end if;
    if geometric then return [H]; end if;

    return [H, QuadraticTwist(H)];
end function;

/* Switching routine
 *******************/

/* Model + possibly twists and reduced automorphism group */
function G2Models(JI : geometric := false, models := true, RationalModel := false, minimize := true)

    FF := Universe(JI); p := Characteristic(FF);

    GI := IgusaToG2Invariants(JI); g1, g2, g3 := Explode(GI);
    J2, J4, J6, _, J10 := Explode(JI);

    twists := [];

    if p eq 2 then
        if   g1 ne g2*g3                               then
            if models then
                twists := G2ModelsInChar2FF_C2(GI : geometric := geometric);
            end if;
            aut := CyclicGroup(2);
        elif g1 eq 0     and g2 ne 0    and g3 eq 0    then
            if models then
                twists := G2ModelsInChar2FF_C2bis(GI : geometric := geometric);
            end if;
            aut := CyclicGroup(2);
        elif g1 eq g2*g3 and g1 ne 0    and g2 ne g3^2 then
            if models then
                twists := G2ModelsInChar2FF_C2xC2(GI : geometric := geometric);
            end if;
            aut := DirectProduct(CyclicGroup(2), CyclicGroup(2));
        elif g1 eq g3^3  and g2 eq g3^2 and g3 ne 0    then
            if models then
                twists := G2ModelsInChar2FF_C2xS3(GI : geometric := geometric);
            end if;
            aut := DirectProduct(SymmetricGroup(3), CyclicGroup(2));
        elif g1 eq 0     and g2 eq 0    and g3 ne 0    then
            if models then
                if models then
                    twists := G2ModelsInChar2FF_M32(GI : geometric := geometric);
                end if;
            end if;
            aut := DirectProduct([CyclicGroup(2): i in [1..5]]);
        else
            if models then
                twists := G2ModelsInChar2FF_M160(GI : geometric := geometric);
            end if;
            aut := DirectProduct( CyclicGroup(2),
                sub<Sym(10)| (1, 9, 3, 7, 5)(2, 10, 4, 8, 6), (1, 2)(9, 10), (5, 6)(9, 10), (7, 8)(9, 10)> );
        end if;
        return twists, aut, aut;
    end if;

    /* y^2 = x^6-1 */
    if p ne 3 and p ne 5 and GI eq [ FF!6400000/3, FF!440000/9, FF!-32000/81 ] then
        if models then
            twists := G2ModelsInFF_2D12(GI : geometric := geometric);
        end if;
        return twists,
            sub<Sym(7) | (3, 4), (1, 4)(2, 6)(3, 5), (2, 6, 7), (1, 5)(3, 4)>,
            DihedralGroup(6);
    end if;

    /* y^2 = x^5-x */
    if GI eq [ 50000, 3750, -125 ] then
        if p eq 5 then
            if models then
                twists := G2ModelsInChar5FF_G240(GI : geometric := geometric);
            end if;
            return twists,
                sub<Sym(240)|
                [ 7, 8, 9, 10, 11, 12, 14, 15, 13, 17, 18, 16, 43, 44, 45, 46, 47, 48, 1, 2, 3, 4, 5,
                6, 21, 19, 20, 24, 22, 23, 73, 74, 75, 76, 77, 78, 85, 86, 87, 88, 89, 90, 51, 49, 50,
                54, 52, 53, 68, 69, 67, 71, 72, 70, 97, 98, 99, 100, 101, 102, 109, 110, 111, 112,
                113, 114, 25, 26, 27, 28, 29, 30, 121, 122, 123, 124, 125, 126, 31, 32, 33, 34, 35,
                36, 145, 146, 147, 148, 149, 150, 37, 38, 39, 40, 41, 42, 157, 158, 159, 160, 161,
                162, 55, 56, 57, 58, 59, 60, 181, 182, 183, 184, 185, 186, 61, 62, 63, 64, 65, 66, 91,
                92, 93, 94, 95, 96, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 130,
                131, 132, 128, 129, 127, 79, 80, 81, 82, 83, 84, 136, 137, 138, 134, 135, 133, 115,
                116, 117, 118, 119, 120, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228,
                174, 172, 173, 169, 170, 171, 103, 104, 105, 106, 107, 108, 168, 166, 167, 163, 164,
                165, 216, 214, 215, 211, 212, 213, 210, 208, 209, 205, 206, 207, 139, 140, 141, 142,
                143, 144, 151, 152, 153, 154, 155, 156, 232, 233, 234, 230, 231, 229, 238, 239, 240,
                236, 237, 235, 175, 176, 177, 178, 179, 180, 187, 188, 189, 190, 191, 192 ],
                [ 13, 14, 15, 16, 17, 18, 31, 32, 33, 34, 35, 36, 49, 50, 51, 52, 53, 54, 55, 56, 57,
                58, 59, 60, 1, 2, 3, 4, 5, 6, 68, 69, 67, 71, 72, 70, 7, 8, 9, 10, 11, 12, 63, 61, 62,
                66, 64, 65, 25, 26, 27, 28, 29, 30, 44, 45, 43, 47, 48, 46, 19, 20, 21, 22, 23, 24,
                39, 37, 38, 42, 40, 41, 127, 128, 129, 130, 131, 132, 139, 140, 141, 142, 143, 144,
                133, 134, 135, 136, 137, 138, 151, 152, 153, 154, 155, 156, 163, 164, 165, 166, 167,
                168, 175, 176, 177, 178, 179, 180, 169, 170, 171, 172, 173, 174, 187, 188, 189, 190,
                191, 192, 181, 182, 183, 184, 185, 186, 85, 86, 87, 88, 89, 90, 73, 74, 75, 76, 77,
                78, 91, 92, 93, 94, 95, 96, 157, 158, 159, 160, 161, 162, 79, 80, 81, 82, 83, 84, 121,
                122, 123, 124, 125, 126, 109, 110, 111, 112, 113, 114, 97, 98, 99, 100, 101, 102, 115,
                116, 117, 118, 119, 120, 145, 146, 147, 148, 149, 150, 103, 104, 105, 106, 107, 108,
                213, 211, 212, 216, 214, 215, 207, 205, 206, 210, 208, 209, 194, 195, 193, 197, 198,
                196, 200, 201, 199, 203, 204, 202, 236, 237, 235, 239, 240, 238, 230, 231, 229, 233,
                234, 232, 219, 217, 218, 222, 220, 221, 225, 223, 224, 228, 226, 227 ]
                >,
                PGL(2, GF(5));
        end if;
        if models then
            twists := G2ModelsInFF_G48(GI : geometric := geometric);
        end if;
        return twists,
            sub<Sym(8)|[2,1,3,4,7,8,5,6],[3,4,5,6,1,2,7,8]>, /* GL(2, GF(3)) */
            sub<Sym(4)|(3, 4), (2, 3, 4), (1, 4)(2, 3)>;
    end if;

    /* y^2 = x^5-1, p <> 5 */
    if GI eq [ 0, 0, 0 ] then
        if models then
            twists := G2ModelsInFF_C10(GI : geometric := geometric);
        end if;
        return twists, CyclicGroup(10), CyclicGroup(5);
    end if;

    if p eq 3 then
        /* y^2 = 1/t*x^6+x^4+x^2+1 */
        if J4 eq 0 and J10 + 2*J6*J2^2 eq 0 then
            if models then
                twists := G2ModelsInChar3FF_D12(JI : geometric := geometric);
            end if;
            return twists, DihedralGroup(6), DihedralGroup(3);
        end if;
    elif p eq 5 then
        /* y^2 = x^6+x^3+t */
        if J10*J4*J2^2 + J6^3 + 3*J6*J4^3 + 2*J4^4*J2 eq 0 and
            J10*J2^3 + 3*J6^2*J4 + 4*J4^4 + 2*J4^3*J2^2 eq 0 and
            J6*J2 + 2*J4^2 eq 0 then
            if models then
                twists := G2ModelsInFF_D12(JI : geometric := geometric);
            end if;
            return twists, DihedralGroup(6), DihedralGroup(3);
        end if;
    else
        /* y^2 = x^6+x^3+t */
        if 750*J10+90*J6*J4-3*J6*J2^2-J4^2*J2 eq 0 and
            2700*J6^2+540*J6*J4*J2-27*J6*J2^3+160*J4^3-9*J4^2*J2^2 eq 0 then
            if models then
                twists := G2ModelsInFF_D12(JI : geometric := geometric, minimize := minimize);
            end if;
            return twists, DihedralGroup(6), DihedralGroup(3);
        end if;
    end if;

    /* y^2 = x^5+x^3+t*x */
    if p ne 5 then
        if 172800*J6^2-23040*J6*J4*J2+592*J6*J2^3-40960*J4^3+3584*J4^2*J2^2-104*J4*J2^4+J2^6 eq 0
            and 128000*J10+5760*J6*J4-192*J6*J2^2-1024*J4^2*J2+64*J4*J2^3-J2^5 eq 0 then
            if models then
                twists := G2ModelsInFF_D8(JI : geometric := geometric, minimize := minimize);
            end if;
            return twists, DihedralGroup(4),  DirectProduct(CyclicGroup(2), CyclicGroup(2));
        end if;
    else
        if [
            J10*J4^5 + 4*J6^5 + 2*J6^3*J4^3 + 2*J4^6*J2^3 + 2*J4^4*J2^7 + 4*J4^3*J2^9 + 2*J2^15,
            J10*J4^3*J2 + 2*J6^4 + 3*J6^2*J4^3 + 3*J4^6 + J4^5*J2^2 + 3*J4^4*J2^4 + 2*J4^3*J2^6 + J4^2*J2^8 + 2*J4*J2^10 + 3*J2^12,
            J10*J4*J2^2 + J6^3 + 3*J4^4*J2 + 2*J4^2*J2^5 + 4*J4*J2^7 + 2*J2^9,
            J10*J2^3 + 3*J6^2*J4 + 3*J4^4 + J4^2*J2^4 + 3*J2^8,
            J6*J2 + 2*J4^2 + 3*J4*J2^2 + 3*J2^4
            ]
            eq [0,0,0,0,0] then
            if models then
                twists := G2ModelsInFF_D8(JI : geometric := geometric);
            end if;
            return twists, DihedralGroup(4), DirectProduct(CyclicGroup(2), CyclicGroup(2));
        end if;
    end if;

    /* J15^2 */
    R := J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2 + J2^4*J4^4*J6
        + 8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10 + 136*J2^3*J4^3*J6^2
        + 4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2 + 216*J2^3*J6^4 -
        64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10 + 1080*J2^2*J4^2*J6^3 -
        12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2 - 2304*J2*J4^4*J6^2 -
        84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2 - 7776*J2*J4*J6^4 -
        129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10 + 6912*J4^3*J6^3 +
        691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2 + 11664*J6^5 + 51200000*J10^3;

    if R eq 0 then
        if models then
            twists := G2ModelsInFF_V4(JI : geometric := geometric, minimize := minimize);
        end if;
        return twists, DirectProduct(CyclicGroup(2),CyclicGroup(2)), CyclicGroup(2);
    end if;

    if models then
        twists := G2ModelsInFF_C2(JI : geometric := geometric, RationalModel := RationalModel, minimize := minimize);
    end if;
    return twists, CyclicGroup(2), CyclicGroup(1);

end function;

intrinsic HyperellipticCurveFromIgusaInvariants(II::SeqEnum :
    RationalModel := false, minimize := true) -> CrvHyp, GrpPerm
    {Compute a hyperelliptic curve and its automorphism group from given
    Igusa invariants J2, J4, J6, J8 and J10. This function behaves slightly
    better over the rationals when J15 is also given in input (see IgusaInvariantsWithR).}

    require #II eq 5 or  #II eq 6:
	"Argument must be a sequence of 5 or 6 Igusa invariants.";
    if Universe(II) cmpeq Integers() then
        II := ChangeUniverse(II,Rationals());
    end if;

    twists, aut := G2Models(II : geometric := true, RationalModel := RationalModel, minimize := minimize);
    return twists[1], aut;

end intrinsic;

intrinsic HyperellipticCurveFromG2Invariants(GI::SeqEnum :
    RationalModel := false, minimize := true) -> CrvHyp, GrpPerm
    {Compute a hyperelliptic curve and its automorphism group from given
    Cardona-Quer-Nart-Pujolas absolute invariants.}

    require #GI eq 3 :
	"Argument must be a sequence of three absolute invariants.";

    H, aut := HyperellipticCurveFromIgusaInvariants(G2ToIgusaInvariants(GI) : RationalModel := RationalModel, minimize := minimize);
    return H, aut;

end intrinsic;

 /***
  * Twists
  *
  ********************************************************************/
intrinsic TwistsFromG2Invariants(II::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
    {Compute genus 2 twisted  hyperelliptic curves and their automorphism group from
    Cardona-Quer-Nart-Pujolas invariants.}

    require #II eq 3  :
	"Argument must be a sequence of three absolute invariants.";

    require Type(Universe(II)) eq FldFin :
	"Twist computations only available in finite fields";

    twists, aut := G2Models(G2ToIgusaInvariants(II));
    return twists, aut;

end intrinsic;

intrinsic TwistsFromIgusaInvariants(JI::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
    {Compute twisted  hyperelliptic curves and their automorphism groups from
    Igusa invariants.}

    require #JI eq 5 or #JI eq 6 :
	"Argument must be a sequence of 5 (or possibly 6) Igusa invariants.";

    require Type(Universe(JI)) eq FldFin :
	"Twist computations only available in finite fields";

    twists, aut := G2Models(JI);
    return twists, aut;

end intrinsic;

 /***
  * Geometric Automorphism group
  *
  ********************************************************************/
intrinsic GeometricAutomorphismGroupFromIgusaInvariants(II::SeqEnum) -> GrpPerm
    {Compute the automorphism group from
    given Igusa (or Cardona-Quer-Nart-Pujolas) invariants.}

    require #II eq 3 or #II eq 5 or #II eq 6 :
	"Argument must be a sequence of three absolute invariants or 5 (or possibly 6) Igusa invariants.";

    JI := II; if #II eq 3 then JI := G2ToIgusaInvariants(II); end if;

    if Universe(JI) cmpeq Integers() then
        JI := ChangeUniverse(JI,Rationals());
    end if;

    _, aut := G2Models(JI : models := false, minimize := false);
    return aut;

end intrinsic;


/* Geometric automorphism group classification
   see [Cardona2003] and [CaNaPu2005] */
intrinsic GeometricAutomorphismGroupGenus2Classification(FF::FldFin) -> SeqEnum, SeqEnum
    {Give all possible automorphism groups of a genus 2 curve, and the
    corresponding number of curves (up to isomorphism and twists) with
    this group, defined over the finite field given in input.}

    p := Characteristic(FF); q := #FF;

    nbth_C2 := 0; nbth_C2xC2 := 0; nbth_C2xS3 := 0; nbth_M32 := 0;
    nbth_M160 := 0; nbth_2D12 := 0; nbth_G240 := 0; nbth_G48  := 0;
    nbth_C10  := 0; nbth_D12  := 0; nbth_D8   := 0; nbth_V4   := 0;

    if p eq 2 then
	nbth_C2    := q^3-q^2+q-1;
	nbth_C2xC2 := q^2-3*q+2;
	nbth_C2xS3 := q-1;
	nbth_M32   := q-1;
	nbth_M160  := 1;
    end if;
    if p eq 3 then
	nbth_G48  := 1;
	nbth_C10  := 1;
	nbth_D12  := q-2;
	nbth_D8   := q-2;
	nbth_V4   := q^2-3*q+4;
	nbth_C2   := q^3-q^2+q-2;
    end if;
    if p eq 5 then
	nbth_G240 := 1;
	nbth_D12  := q-2;
	nbth_D8   := q-2;
	nbth_V4   := q^2-3*q+4;
	nbth_C2   := q^3-q^2+q-1;
    end if;
    if p ge 7 then
	nbth_2D12 := 1;
	nbth_G48  := 1;
	nbth_C10  := 1;
	nbth_D12  := q-3;
	nbth_D8   := q-3;
	nbth_V4   := q^2-3*q+5;
	nbth_C2   := q^3-q^2+q-2;
    end if;

    Grps := []; Nmbs := [];
    if nbth_C2 ne 0 then
	Grps cat:= [CyclicGroup(2)]; Nmbs cat:= [nbth_C2];
    end if;
    if nbth_C2xC2 ne 0 then
	Grps cat:= [DirectProduct(CyclicGroup(2),CyclicGroup(2))]; Nmbs cat:= [nbth_C2xC2];
    end if;
    if nbth_V4 ne 0 then
	Grps cat:= [DirectProduct(CyclicGroup(2),CyclicGroup(2))]; Nmbs cat:= [nbth_V4];
    end if;
    if nbth_C2xS3 ne 0 then
	Grps cat:= [DirectProduct(SymmetricGroup(3),CyclicGroup(2))]; Nmbs cat:= [nbth_C2xS3];
    end if;
    if nbth_D8 ne 0 then
	Grps cat:= [DihedralGroup(4)]; Nmbs cat:= [nbth_D8];
    end if;
    if nbth_C10 ne 0 then
	Grps cat:= [CyclicGroup(10)]; Nmbs cat:= [nbth_C10];
    end if;
    if nbth_D12 ne 0 then
	Grps cat:= [DihedralGroup(6)]; Nmbs cat:= [nbth_D12];
    end if;
    if nbth_2D12 ne 0 then
	Grps cat:= [sub<Sym(7) | (3, 4), (1, 4)(2, 6)(3, 5), (2, 6, 7), (1, 5)(3, 4)>]; Nmbs cat:= [nbth_2D12];
    end if;
    if nbth_M32 ne 0 then
	Grps cat:= [DirectProduct([CyclicGroup(2): i in [1..5]])]; Nmbs cat:= [nbth_M32];
    end if;
    if nbth_G48 ne 0 then
	Grps cat:= [sub<Sym(8)|[2,1,3,4,7,8,5,6],[3,4,5,6,1,2,7,8]>]; Nmbs cat:= [nbth_G48];
    end if;
    if nbth_M160 ne 0 then
        Grps cat:= [ DirectProduct( CyclicGroup(2),
            sub<Sym(10)| (1, 9, 3, 7, 5)(2, 10, 4, 8, 6), (1, 2)(9, 10), (5, 6)(9, 10), (7, 8)(9, 10)> ) ];
        Nmbs cat:= [nbth_M160];
    end if;
    if nbth_G240 ne 0 then
	Grps cat:= [sub<Sym(240)|
            [ 7, 8, 9, 10, 11, 12, 14, 15, 13, 17, 18, 16, 43, 44, 45, 46, 47, 48, 1, 2, 3, 4, 5,
            6, 21, 19, 20, 24, 22, 23, 73, 74, 75, 76, 77, 78, 85, 86, 87, 88, 89, 90, 51, 49, 50,
            54, 52, 53, 68, 69, 67, 71, 72, 70, 97, 98, 99, 100, 101, 102, 109, 110, 111, 112,
            113, 114, 25, 26, 27, 28, 29, 30, 121, 122, 123, 124, 125, 126, 31, 32, 33, 34, 35,
            36, 145, 146, 147, 148, 149, 150, 37, 38, 39, 40, 41, 42, 157, 158, 159, 160, 161,
            162, 55, 56, 57, 58, 59, 60, 181, 182, 183, 184, 185, 186, 61, 62, 63, 64, 65, 66, 91,
            92, 93, 94, 95, 96, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 130,
            131, 132, 128, 129, 127, 79, 80, 81, 82, 83, 84, 136, 137, 138, 134, 135, 133, 115,
            116, 117, 118, 119, 120, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228,
            174, 172, 173, 169, 170, 171, 103, 104, 105, 106, 107, 108, 168, 166, 167, 163, 164,
            165, 216, 214, 215, 211, 212, 213, 210, 208, 209, 205, 206, 207, 139, 140, 141, 142,
            143, 144, 151, 152, 153, 154, 155, 156, 232, 233, 234, 230, 231, 229, 238, 239, 240,
            236, 237, 235, 175, 176, 177, 178, 179, 180, 187, 188, 189, 190, 191, 192 ],
            [ 13, 14, 15, 16, 17, 18, 31, 32, 33, 34, 35, 36, 49, 50, 51, 52, 53, 54, 55, 56, 57,
            58, 59, 60, 1, 2, 3, 4, 5, 6, 68, 69, 67, 71, 72, 70, 7, 8, 9, 10, 11, 12, 63, 61, 62,
            66, 64, 65, 25, 26, 27, 28, 29, 30, 44, 45, 43, 47, 48, 46, 19, 20, 21, 22, 23, 24,
            39, 37, 38, 42, 40, 41, 127, 128, 129, 130, 131, 132, 139, 140, 141, 142, 143, 144,
            133, 134, 135, 136, 137, 138, 151, 152, 153, 154, 155, 156, 163, 164, 165, 166, 167,
            168, 175, 176, 177, 178, 179, 180, 169, 170, 171, 172, 173, 174, 187, 188, 189, 190,
            191, 192, 181, 182, 183, 184, 185, 186, 85, 86, 87, 88, 89, 90, 73, 74, 75, 76, 77,
            78, 91, 92, 93, 94, 95, 96, 157, 158, 159, 160, 161, 162, 79, 80, 81, 82, 83, 84, 121,
            122, 123, 124, 125, 126, 109, 110, 111, 112, 113, 114, 97, 98, 99, 100, 101, 102, 115,
            116, 117, 118, 119, 120, 145, 146, 147, 148, 149, 150, 103, 104, 105, 106, 107, 108,
            213, 211, 212, 216, 214, 215, 207, 205, 206, 210, 208, 209, 194, 195, 193, 197, 198,
            196, 200, 201, 199, 203, 204, 202, 236, 237, 235, 239, 240, 238, 230, 231, 229, 233,
            234, 232, 219, 217, 218, 222, 220, 221, 225, 223, 224, 228, 226, 227 ]
            > /* SmallGroup(240,90) */ ]; Nmbs cat:= [nbth_G240];
    end if;

    return Grps, Nmbs;

end intrinsic;
