//freeze;

/***
 *  Twists of curves.
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
 *  Copyright 2020, R. Lercier, C. Ritzenthaler & J. Sijsling
 */

/***
 * Exported intrinsics.
 *
 * intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(f::RngUPolElt, Autos::List :
 *     explicit := false) -> GrpPerm, Map
 * intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(X::CrvHyp, Autos::List :
 *     explicit := false) -> GrpPerm, Map
 *
 * intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(f::RngUPolElt :
 *     geometric := false, explicit := false) -> GrpPerm, Map
 * intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(X::CrvHyp :
 *     geometric := false, explicit := false) -> GrpPerm, Map
 *
 * intrinsic AutomorphismGroupOfHyperellipticCurve(f::RngUPolElt, Autos::List :
 *     explicit := false) -> GrpPerm, Map
 * intrinsic AutomorphismGroupOfHyperellipticCurve(X::CrvHyp, Autos::List :
 *     explicit := false) -> GrpPerm, Map
 * intrinsic AutomorphismGroupOfHyperellipticCurve(f::RngUPolElt :
 *     geometric := false, explicit := false) -> GrpPerm, Map
 * intrinsic AutomorphismGroupOfHyperellipticCurve(X::CrvHyp :
 *     geometric := false, explicit := false) -> GrpPerm, Map
 *
 * intrinsic GeometricAutomorphismGroup(Ec::CrvEll) -> GrpPerm
 *     {Compute the geometric automorphism group of an elliptic curve.}
 * intrinsic GeometricAutomorphismGroup(X::CrvHyp) -> GrpPerm
 *     {Compute the geometric automorphism group of an hyperelliptic curve.}
 *
 * intrinsic Twists(X::CrvHyp :
 *     AutomorphismGroup := false) -> SeqEnum[CrvHyp], GrpPerm
 *     {Compute twisted hyperelliptic curves and their geometric reduced automorphism groups}
 *
 * intrinsic TwistsOfHyperellipticPolynomials(f::RngUPolElt :
 *     AutomorphismGroup := false) -> SeqEnum[RngUPolElt], GrpPerm
 *     {Compute twisted  hyperelliptic polynomials from
 *     a polynomial that defines the curve y^2 = f(x).}
 * intrinsic TwistsOfHyperellipticPolynomials(fh::SeqEnum[RngUPolElt] :
 *     AutomorphismGroup := false) -> SeqEnum, GrpPerm
 *     {Compute twisted hyperelliptic polynomials and their automorphism groups from
 *     a list [f, h] of two polynomials that defines the curve y^2 + h(x) * y = f(x).}
 * intrinsic Twists(C::Crv, Autos::SeqEnum  :
 *     AutomorphismGroup := false) -> SeqEnum[Crv], GrpPerm
 *
 ********************************************************************/

 /***
  *
  * Given a finite field Fq and a curve C, either hyperelliptic or a plane smooth quartic
  * Twists(C) compute a set of representatives of the twists of C. This works
  * - for C hyperelliptic g=2 and 3 without restriction on q
  * - For C hyperelliptic g>3 with q odd
  * - For C plane smooth quartic and q a power of a prime>7.
  *
  * Note that the function TwistsOverFiniteField can also be useful if you already know
  * a subgroup H of the group of all automorphisms of C given as a list of
  * linear projective transformations (i.e. matrices) of the ambient projective space. In
  * that case you can compute twists with respect to these elements for any non-hyperelliptic
  * curve (not necessarily plane). Caution: all matrices in H
  * have been normalized so that they have a 1 as first non-zero coefficient runnning
  * the matrix in column.
  *
  *********************************************************************/

import "../genus2/g2twists.m" : G2Models;
import "../genus3/g3twists.m" : G3Models;

/* return f.M when f is seen as a form of degree n
   (M lives in an extension of the field of definition of f)
*/

function TransformForm(A,f,n)
  F2 := BaseRing(Parent(A));
  F := BaseRing(Parent(f));
  Embed(F,F2);
  f2 := ChangeRing(f,F2);
  P2 := PolynomialRing(F2,2); x := P2.1; z := P2.2;
  P := PolynomialRing(F2); u := P.1;
  phi := hom<P2 -> P | u,1>;
  f3 := P2!(Evaluate(f2,x/z)*z^n);
  f4 := Evaluate(f3,[A[1,1]*x+A[1,2]*z,A[2,1]*x+A[2,2]*z]);
  co := Coefficients(f4);
  return phi(f4)/co[1];
end function;


/* This function return a list [*m, lamda*] such that
   FrobeniusImage(M,e)^m-1 .. FrobeniusImage(M,e)M = lambda Id
   Where M is a NXN matrix defined over the finite field Fs, #Fs = q^r.
   F is the field other which my curve is defined. #F = p^e = q
   FrobeniusImage(M,e)^m = FrobeniusImage(..FrobeniusImage(M,e)..,e) m times.
*/
function FrobeniusOrderAutomorphism(M, F)

    e := Degree(F);
    P := M;
    m := 1;
    while IsScalar(P) eq false or P[1,1] notin F do
        P := FrobeniusImage(P,e)*M;
        m := m+1;
    end while;

    return [*m, P[1, 1]*];
end function;


/* This function return a Matrix with a 1 which is a multiple of M
*/

function NormalizedM(M)

    for j := 1 to Nrows(M) do
        for i := 1 to Nrows(M) do
            if M[i,j] ne 0 then return (1 / M[i,j]) * M; end if;
        end for;
    end for;

    return M;
end function;

/* check if the projective matrix M is defined over F
*/

function IsDefinedOver(M,F)

    if M eq 0 then return true, ChangeRing(M,F); end if;
    e:=Degree(F);
    if NormalizedM(M) eq FrobeniusImage(NormalizedM(M),e) then
        return true, ChangeRing(NormalizedM(M),F);
    end if;

    return false, M;
end function;

/* smallest field of definition
*/

function SmallestField(M,F)
    Fs := BaseRing(M);
    r := Degree(Fs,F);
    for d in Divisors(r) do
        Fd := ext<F | d>;
        if IsDefinedOver(M, Fd) then
            return ChangeRing(NormalizedM(M), Fd);
        end if;
    end for;

end function;

/* Given the (reduced) automorphism group H and the finite field F,
   this function compute it cohomology classes.
*/
function CohomologyClass(H, F)
    L := H;
    e := Degree(F);
    CohoClass := [* Identity(Parent(H[1])) *];
    while not IsEmpty(L) do
        for h in H do
            EqClassCoho := h^(-1)*CohoClass[#CohoClass]*FrobeniusImage(h,e);
            Exclude(~L, NormalizedM(EqClassCoho));
        end for;
        if IsEmpty(L) eq false then
            Append(~CohoClass, SmallestField(L[1],F));
        end if;
    end while;
    return CohoClass;
end function;



/* Given a finite field F of size q = p^e and a matrix M defined over an extension of F,
   this function compute an invertible matrix A such that FrobeniusImage(A,e)^(-1)*A=Mb.
   Where Mb = 1/X*M verify FrobeniusImage(Mb,e)^m-1 .. FrobeniusImage(Mb,e)Mb = Id
*/

function ComputationCobord(M, F)

    Fs := BaseRing(M);
    N := Nrows(M);
    r := Degree(Fs);
    e := Degree(F);
    L := FrobeniusOrderAutomorphism (M,F);
    m := L[1] ;
    K := ext<F | m>;
    _, X := NormEquation(K,F!L[2]);
    //  n:=Degree(Fs,F);
    //  K2:=ext<Fs | Lcm(m,n)>;

    Mb := ChangeRing(M,K)*1/X;
    // check S:=Mb;for i:=1 to m-1 do S:=FrobeniusImage(S,e)*Mb; end for;S;

    repeat
        Pb := RandomMatrix(K,N,N);
        A := Pb;
        for i := 1 to m-1 do
            Pb := FrobeniusImage(Pb,e)*Mb;
            A :=  A + Pb;
        end for;
    until IsUnit(A);

    // in this step we have computed A such that FrobeniusImage(A,e)*Mb-A =0
    // in this step we have computed A such that A*FrobeniusImage(A,e)^(-1)-Mb =0

    return A;
end function;

/* Given the reduced Automorphism group G of the hyperelliptic curve C/F,
   the cocycle 2x2 matrix A from above,
   this function compute the reduced automorphism  group defined over F of
   the twist associated to A.
*/

function ReducedAutomorphismGroupOfTwistDefinedOverF(Aut, f, A, g)

    F := BaseRing(f);
    K := BaseRing(A);
    P := Parent(f); x := P.1;
    Embed(F, K);
    L := []; // List of the reduced Automorphism on the twist
    eN := []; // List of the associate constant to find the Automorphisms
    ft:=P!TransformForm(A,f,2*g+2);
    for M in Aut do
        B := A^(-1)*M*A;
        boo, B := IsDefinedOver(B,F);
        if boo then
            Append(~L,B);
            // M; Evaluate(ft,(B[1,1]*x+B[1,2])/(B[2,1]*x+B[2,2]))*(B[2,1]*x+B[2,2])^(2*g+2)/ft;
            Append (~eN,F!(Evaluate(ft,(B[1,1]*x+B[1,2])/(B[2,1]*x+B[2,2]))*(B[2,1]*x+B[2,2])^(2*g+2)/ft));
        end if;
    end for;

    return [* L, eN *];
end function;

/* test of self duality for the twist of C  given by the cocycle A
*/

function IsSelfDual(Aut,f,A,g)
    F := BaseRing(f);
    RAGT := ReducedAutomorphismGroupOfTwistDefinedOverF(Aut,f,A,g);
    return 2*#[e : e in RAGT[2] | IsSquare(e)] eq #RAGT[2];
end function;


function ProjectiveMatrixGroup(L)

    _L := [a : a in L];
    GG, psi := GenericGroup(_L : Mult := func<a,b | NormalizedM(a*b)>);

    for i := NumberOfGenerators(GG) to 1 by -1 do
        pmp, GPrm := CosetAction(GG, sub< GG | [ GG | GG.j : j in [1..i-1] ] >);
        if #GPrm eq #GG then break; end if;
    end for;
    ReduceGenerators(~GPrm);

    return GPrm, Inverse(pmp)*psi;

    /* Computing  [ psi(g@@pmp) : g in GPrm ] can take time ?! */
    /*
    FF := CoefficientRing(Universe(_L)); GMat := sub<GL(2, FF) | _L>;
    phi := hom<GPrm->GMat | [ psi(g@@pmp) : g in Generators(GPrm) ]>;
    return GPrm, phi;
    */
end function;

function Normalize22Column(T)
    col := Eltseq(Rows(Transpose(T))[1]);
    i0 := Minimum([ i : i in [1..#col] | col[i] ne 0 ]);
    return (1/col[i0]) * T;
end function;

/* Given a projective curve C and its Automorphism group Aut
   (given by a list of matrix N x N), this function compute the twists of C
*/

function TwistsOverFiniteField(C, Aut)

    F := BaseRing(C);

    g := Genus(C);

    ishyper, H :=  IsHyperelliptic(C);
    if ishyper then
        twists :=  TwistsOfHyperellipticPolynomials(HyperellipticPolynomials(H));
        return [ HyperellipticCurve(f) : f in twists];
    end if;

    Coh := CohomologyClass(Aut, F);

    T := [C];
    for M in Coh do
        if M ne Identity(Parent(M)) then
            A := ComputationCobord(M^(-1),F);
            C2 := ChangeRing(C, BaseRing(A));
            X2 := Automorphism(AmbientSpace(C2), A^(-1));
            Append(~T, ChangeRing(X2(C2), F));
        end if;
    end for;

    return T;

end function;



/***
 * Reduced automorphism group routines
 *************************************/

 /* Automorphism group with given automorphisms */
intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(f::RngUPolElt, Autos::List :
    explicit := false) -> GrpPerm, Map
    {Return the automorphisms group defined by the sequence Autos, as a permutation group (and its representation if explicit is set to true)}

    aut, phi := ProjectiveMatrixGroup(Autos);

    if explicit then return aut, phi; end if;
    return aut;

end intrinsic;

intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(X::CrvHyp, Autos::List :
    explicit := false) -> GrpPerm, Map
    {Return the automorphisms group defined by the sequence Autos, as a permutation group (and its representation if explicit is set to true)}

    aut, phi := ProjectiveMatrixGroup(Autos);

    if explicit then return aut, phi; end if;
    return aut;

end intrinsic;


 /* Automorphism group */
intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(f::RngUPolElt :
    geometric := false, explicit := false) -> GrpPerm, Map
    {Return the automorphisms group of the curve y^2 = f(x), as a permutation group (and its representation if explicit is set to true)}

    F := CoefficientRing(f);
    p := Characteristic(F);

    d := Degree(f);

    require Discriminant(f) ne 0 :
        "The argument must be non singular";

    g := (d - 1) div 2;

    require g gt 1 :
        "The argument must define an hyperelliptic curve of genus >= 2";

    if geometric and g eq 2 then
        _, _, autred := G2Models(IgusaInvariants(f) : models := false);
        if not explicit then return autred; end if;
    end if;

    if geometric and g eq 3 and p ne 5 then
        _, _, autred := G3Models(ShiodaInvariants(f) : models := false);
        if not explicit then return autred; end if;
    end if;

    Autos := ReducedAutomorphismsOfHyperellipticCurve(f : geometric := geometric, commonfield := true);
    aut, phi := ProjectiveMatrixGroup(Autos);

    if explicit then
        if geometric and ((g eq 2) or (g eq 3 and p ne 5)) then
            ret, iso := IsIsomorphic(autred, aut);
            assert ret eq true;
            return autred, iso*phi;
        end if;
        return aut, phi;
    end if;
    return aut;

    /*
    ret, iso := IsIsomorphic(autred, aut);
    (iso*p)(aut.1);
     */

end intrinsic;

intrinsic ReducedAutomorphismGroupOfHyperellipticCurve(H::CrvHyp :
    geometric := false, explicit := false) -> GrpPerm, Map
    {Return the automorphisms group of the polynomial f(x) (assumed to be of even degree), as a permutation group (and its representation if explicit is set to true)}

    f, h := HyperellipticPolynomials(H);
    g := h eq 0 select f else 4*f + h^2;

    return ReducedAutomorphismGroupOfHyperellipticCurve(g :
        geometric := geometric, explicit := explicit);

end intrinsic;

/***
 * Full automorphism group routines
 ***********************************/
function Normalize22Column(T)
    col := Eltseq(Rows(Transpose(T))[1]);
    i0 := Minimum([ i : i in [1..#col] | col[i] ne 0 ]);
    return (1/col[i0]) * T, col[i0];
end function;


function ProjectiveAutomorphismGroup(L, d)

    function AutoMultiply(A1, A2)
        M, c := Normalize22Column(A1[1]*A2[1]);
        return < M, A1[2] * A2[2] / c^(d div 2) >;
    end function;

    _L := [<a[1],a[2]> : a in L];
    GG, psi := GenericGroup(_L : Mult := AutoMultiply);

    for i := NumberOfGenerators(GG) to 1 by -1 do
        pmp, GPrm := CosetAction(GG, sub< GG | [ GG | GG.j : j in [1..i-1] ] >);
        if #GPrm eq #GG then break; end if;
    end for;
    ReduceGenerators(~GPrm);

    return GPrm, Inverse(pmp)*psi;

end function;


 /* Automorphism group with given automorphisms */
intrinsic AutomorphismGroupOfHyperellipticCurve(f::RngUPolElt, Autos::List :
    explicit := false) -> GrpPerm, Map
    {Return the automorphisms group defined by the sequence Autos, as a permutation group (and its representation if explicit is set to true)}

    d := 2*((Degree(f) + 1) div 2);

    aut, phi := ProjectiveAutomorphismGroup(Autos, d);

    if explicit then return aut, phi; end if;
    return aut;

end intrinsic;

intrinsic AutomorphismGroupOfHyperellipticCurve(X::CrvHyp, Autos::List :
    explicit := false) -> GrpPerm, Map
    {Return the automorphisms group defined by the sequence Autos, as a permutation group (and its representation if explicit is set to true)}

    d := 2*((Degree(X) + 1) div 2);

    aut, phi := ProjectiveAutomorphismGroup(Autos, d);

    if explicit then return aut, phi; end if;
    return aut;

end intrinsic;


 /* Automorphism group */
intrinsic AutomorphismGroupOfHyperellipticCurve(f::RngUPolElt :
    geometric := false, explicit := false) -> GrpPerm, Map
    {Return the automorphisms group of the curve y^2 = f(x), as a permutation group (and its representation if explicit is set to true)}

    F := CoefficientRing(f);
    p := Characteristic(F);

    d := 2*((Degree(f) + 1) div 2);

    require Discriminant(f) ne 0 :
        "The argument must be non singular";

    g := (d - 1) div 2;

    require g gt 1 :
        "The argument must define an hyperelliptic curve of genus >= 2";

    if geometric and g eq 2 then
        _, aut, _ := G2Models(IgusaInvariants(f) : models := false);
        if not explicit then return aut; end if;
    end if;

    if geometric and g eq 3 and p ne 5 then
        _, aut, _ := G3Models(ShiodaInvariants(f) : models := false);
        if not explicit then return aut; end if;
    end if;

    Autos := AutomorphismsOfHyperellipticCurve(f : geometric := geometric, commonfield := true);

    Aut, phi := ProjectiveAutomorphismGroup(Autos, d);

    if explicit then
        if geometric and ((g eq 2) or (g eq 3 and p ne 5)) then
            ret, iso := IsIsomorphic(aut, Aut);
            assert ret eq true;
            return aut, iso*phi;
        end if;
        return Aut, phi;
    end if;
    return Aut;

end intrinsic;

intrinsic AutomorphismGroupOfHyperellipticCurve(H::CrvHyp :
    geometric := false, explicit := false) -> GrpPerm, Map
    {Return the automorphisms group of the polynomial f(x) (assumed to be of even degree), as a permutation group (and its representation if explicit is set to true)}

    f, h := HyperellipticPolynomials(H);
    g := h eq 0 select f else 4*f + h^2;

    return AutomorphismGroupOfHyperellipticCurve(g :
        geometric := geometric, explicit := explicit);

end intrinsic;


/***
 * Geometric automorphism group routines
 ***************************************/

intrinsic GeometricAutomorphismGroup(Ec::CrvEll) -> GrpPerm
    {Compute the geometric automorphism group of the elliptic curve Ec.}

    p := Characteristic(BaseRing(Ec));
    j := jInvariant(Ec);

    if j ne 0 and j ne 12^3 then
        Aut := CyclicGroup(2);
    elif p eq 2 then
        Aut := sub<Sym(24) |
            (1, 17, 9)(2, 18, 10)(3, 19, 11)(4, 20, 12)(5, 21, 13)(6, 22, 14)(7, 23, 15)(8, 24, 16),
            (1, 6, 2, 5)(3, 8, 4, 7)(9, 12, 10, 11)(13, 15, 14, 16)(17, 24, 18, 23)(19, 21, 20, 22)>;
    elif p eq 3 then
        Aut := sub<Sym(12) |
            (1, 3, 2)(4, 6, 5)(7, 8, 9)(10, 11, 12),
            (1, 10, 4, 7)(2, 11, 5, 8)(3, 12, 6, 9)>;
    elif j eq 0 then
        Aut := CyclicGroup(6);
    elif j eq 12^3 then
        Aut := CyclicGroup(4);
    end if;

    return Aut;

end intrinsic;

intrinsic GeometricAutomorphismGroup(H::CrvHyp) -> GrpPerm
    {Compute the geometric automorphism group of the hyperelliptic curve H.}

    g := Genus(H);

    if g eq 1 then return GeometricAutomorphismGroup(EllipticCurve(H)); end if;

    return AutomorphismGroupOfHyperellipticCurve(H : geometric := true);

end intrinsic;

/***
 * Twists
 *********/
intrinsic Twists(H::CrvHyp :
    AutomorphismGroup := false) -> SeqEnum[CrvHyp], GrpPerm
    {Compute twisted hyperelliptic curves and their geometric reduced automorphism groups}

    F := CoefficientRing(H);
    p := Characteristic(F);

    require Type(F) eq FldFin :
	"Twist computations only available in finite fields";

    g := Genus(H);

    if g eq 1 then
        Ec := EllipticCurve(H);
        twists := Twists(Ec);
        if not AutomorphismGroup then return twists; end if;
        return twists, GeometricAutomorphismGroup(Ec);
    end if;

    if g eq 2 then
        twists, _, autred := G2Models(IgusaInvariants(H));
        if AutomorphismGroup then return twists, autred; end if;
        return twists;
    end if;

    if g eq 3 and p ne 5 then
        twists, _, autred := G3Models(ShiodaInvariants(H));
        twists := [ HyperellipticCurve(f) : f in twists];
        if AutomorphismGroup then return twists, autred; end if;
        return twists;
    end if;

    require IsUnit(F!2) :
        "2 must be invertible in the base ring.";

    f, h := HyperellipticPolynomials(H);
    g := h eq 0 select f else 4*f + h^2;
    d := 2*((Degree(g) + 1) div 2);

    _, Aut := IsGL2EquivalentExtended(f, f, d : geometric := true, commonfield := true);

    twists := TwistsOverFiniteField(HyperellipticCurve(g), [ Normalize22Column(A) : A in Aut ]);

    if AutomorphismGroup then
        aut, _ := ProjectiveMatrixGroup(Aut);
        return twists, aut;
    end if;
    return twists;

end intrinsic;

function TwistsOfHyperellipticPolynomialsMain(f :
    AutomorphismGroup := false)

    F := CoefficientRing(f);

    d := Degree(f);
    g := (d - 1) div 2;

    t := PrimitiveElement(F);
    P := Parent(f);

    _, Aut := IsGL2EquivalentExtended(f, f, 2*g+2 : geometric := true, commonfield := true);
    Aut := [ Normalize22Column(A) : A in Aut ];

    Coh := CohomologyClass(Aut, F);

    T := [f];
    if not IsSelfDual(Aut, f, Identity(Parent(Coh[1])), g) then Append(~T, t*f); end if;

    for M in Coh do
        if M ne Identity(Parent(M)) then
            A := ComputationCobord(M^(-1),F);

            ft := P!TransformForm(A^(-1), f, 2*g+2); Append(~T, ft);
            if not IsSelfDual(Aut, f, A^(-1), g) then Append(~T,t*ft); end if;
        end if;
    end for;

    if AutomorphismGroup then
        aut, phi := ProjectiveMatrixGroup(Aut);
        return T, aut;
    end if;

    return T;

end function;

intrinsic TwistsOfHyperellipticPolynomials(f::RngUPolElt :
    AutomorphismGroup := false) -> SeqEnum[RngUPolElt], GrpPerm
    {Compute twisted  hyperelliptic polynomials from
    a polynomial that defines the curve y^2 = f(x), and their geometric reduced automorphism groups.}

    F := CoefficientRing(f);
    p := Characteristic(F);

    require Type(F) eq FldFin :
        "Twist computations only available in finite fields";

    require IsUnit(F!2) :
        "2 must be invertible in the base ring.";

    g := (Degree(f) - 1) div 2;

    require g gt 1 :
        "Degree(f) > 4 is required";

    if g eq 2 then
        twists, _, autred := G2Models(IgusaInvariants(f));
        twists := [HyperellipticPolynomials(H) : H in twists];
        if AutomorphismGroup then return twists, autred; end if;
        return twists;
    end if;

    if g eq 3 and p ne 5 then
        twists, autred := G3Models(ShiodaInvariants(f));
        if AutomorphismGroup then return twists, autred; end if;
        return twists;
    end if;

    return TwistsOfHyperellipticPolynomialsMain(f : AutomorphismGroup := AutomorphismGroup);

end intrinsic;

intrinsic TwistsOfHyperellipticPolynomials(fh::SeqEnum[RngUPolElt] :
    AutomorphismGroup := false) -> SeqEnum, GrpPerm
    {Compute twisted hyperelliptic polynomials and their automorphism groups from
    a list [f, h] of two polynomials that defines the curve y^2 + h(x) * y = f(x).}

    F := CoefficientRing(fh[1]);
    p := Characteristic(F);

    require Type(F) eq FldFin :
	"Twist computations only available in finite fields";

    f, h := Explode(fh);

    if not IsUnit(F!2) then
        g := Genus(HyperellipticCurve(fh));

        require g in {2,3} :
            "The argument must define an hyperelliptic curve of genus <= 3";

        if g eq 2 then
            twists, _, autred := G2Models(IgusaInvariants(f));
            Twists := []; for H in twists do
                f, h := HyperellipticPolynomials(H);
                Append(~Twists, [f, h]);
            end for;
            if AutomorphismGroup then return Twists, autred; end if;
            return Twists;
        end if;

        if g eq 3 and p ne 5 then
            twists, _, autred := G3Models(ShiodaInvariants(f));
            if AutomorphismGroup then return twists, autred; end if;
            return twists;
        end if;

        return fh;
    end if;
    g := h eq 0 select f else 4*f + h^2;

    return TwistsOfHyperellipticPolynomials(g : AutomorphismGroup := AutomorphismGroup);

end intrinsic;

intrinsic Twists(C::Crv, Autos::SeqEnum  :
    AutomorphismGroup := false) -> SeqEnum[Crv], GrpPerm
    {Compute twists of a curve, given the list of its automorphisms (given by a list of N x N matrices).}

    F := CoefficientRing(C);

    require Type(F) eq FldFin :
        "Twist computations only available in finite fields";

    Aut := [ NormalizedM(Transpose(A^(-1))) : A in Autos ];
    twists := TwistsOverFiniteField(C, Aut);
    if AutomorphismGroup then
        aut, _ := ProjectiveMatrixGroup(Aut);
        return twists, aut;
    end if;

    return twists;

end intrinsic;
