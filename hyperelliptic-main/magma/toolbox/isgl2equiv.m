//freeze;

/***
 *  Computing Geometric Isomorphisms between two polynomials of even degree
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
 *  Copyright 2013-2020, R. Lercier, C. Ritzenthaler & J. Sijsling
 */

 /***
 * Exported intrinsics.
 *
 * intrinsic IsGL2EquivalentExtended(f1::RngUPolElt, f2::RngUPolElt, deg::RngIntElt :
 *     geometric := false, covariant := true, commonfield := false) -> BoolElt, List
 *
 *
 * intrinsic IsReducedIsomorphicHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
 *     geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
 * intrinsic IsReducedIsomorphicHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
 *     geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
 *
 * intrinsic ReducedIsomorphismsOfHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
 *     geometric := false, covariant := true, commonfield := true) ->  List
 * intrinsic ReducedIsomorphismsOfHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
 *     geometric := false, covariant := true, commonfield := true) ->  List
 *
 * intrinsic ReducedAutomorphismsOfHyperellipticCurve(f::RngUPolElt :
 *     geometric := false, commonfield := true, covariant := true) -> List
 * intrinsic ReducedAutomorphismsOfHyperellipticCurve(X::CrvHyp :
 *     geometric := false, commonfield := true, covariant := true) -> List
 *
 *
 * intrinsic IsIsomorphicHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
 *     geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
 * intrinsic IsIsomorphicHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
 *     geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
 *
 * intrinsic IsomorphismsOfHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
 *     geometric := false, covariant := true, commonfield := true) -> List
 *   intrinsic IsomorphismsOfHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
 *     geometric := false, covariant := true, commonfield := true) ->  List
 *
 * intrinsic AutomorphismsOfHyperellipticCurve(f::RngUPolElt :
 *     geometric := false, commonfield := true, covariant := true) -> List
 * intrinsic AutomorphismsOfHyperellipticCurve(X::CrvHyp :
 *     geometric := false, commonfield := true, covariant := true) -> List
 *
 *
 ********************************************************************/

 /* The definitive algebraic versions of [LRS13]

  [LRS13] Fast computation of isomorphisms of hyperelliptic curves and explicit Galois descent.
          Proceedings of the Tenth Algorithmic NumberTheory Symposium, volume 1 of The Open Book Series,
          pages 463-486. Mathematical SciencesPublishers, 2013


  Step 1: Up to a linear change of variable, we start with f and g of deg. 2*n

  Step 2: We send to zero the 2*n-1-th coefficient by the transformation
           x = X - a7*Y/8/a8, y = Y

  Step 3: We assume that both coefficients on the diagonal of the isomorphism are non-zero
  (if it appears that it is not true, we apply a random change of variable on f)

  a7 := 0; b7 := 0;

  f := a0*y^8+a1*x*y^7+a2*x^2*y^6+a3*x^3*y^5+a4*x^4*y^4+a5*x^5*y^3+a6*x^6*y^2+a7*x^7*y+a8*x^8;
  g := b0*Y^8+b1*X*Y^7+b2*X^2*Y^6+b3*X^3*Y^5+b4*X^4*Y^4+b5*X^5*Y^3+b6*X^6*Y^2+b7*X^7*Y+b8*X^8;

  # We look for isomorphims in the following form (maple code)

  EQ := subs(x = 1/m11 * X + m12*Y/m22, y = 1/m11 * m21*X + Y/m22, f) - g;
  EQ  := collect(numer(EQ), [X, Y], distributed);

  # We isolate m12 = -subs(y=m21, x=1, diff(f, y)/diff(f, x))

  V12 := factor(isolate(coeff(subs(Y=1, EQ), X^7), m12));

  # deg 8
  subs(x=1, y=m21, f - m11^8*b8);

  # deg 7
  subs(x=1, y=m21, m12 * diff(f, x) + diff(f, y))

  # deg 6
  subs(x=1, y=m21, m12^2 * diff(f, x$2) + 2*m12*diff(f, x, y) + diff(f, y$2)) - 2*m11^6*m22^2*b6;

  # deg 5
  subs(x=1, y=m21, m12^3 * diff(f, x$3) + 3*m12^2*diff(f, x$2, y) + 3*m12*diff(f, x, y$2) + diff(f, y$3)) - 6*m11^5*m22^3*b5;

  # deg 4
  subs(x=1, y=m21,
                  m12^4 * diff(f, x$4)
              + 4*m12^3 * diff(f, x$3, y)
              + 6*m12^2 * diff(f, x$2, y$2)
              + 4*m12   * diff(f, x, y$3)
              +           diff(f, y$4)
       ) - 24*m11^4*m22^4*b4;

*/
function HomFromRoot(K, L, rt)

    if IsPrimeField(K) then
        return hom< K -> L | >;
    else
        return hom< K -> L | rt >;
    end if;

end function;


function ConjugateMatrix(h, A)

    return Matrix([ [ h(c) : c in Eltseq(row) ] : row in Rows(A) ]);

end function;


function ConjugatePolynomial(h, f)

    K := Codomain(h); R := PolynomialRing(K);
    return &+[ h(Coefficient(f, i))*R.1^i : i in [0..Degree(f)] ];

end function;


function PullbackPolynomial(h, f)

    if IsPrimeField(Domain(h)) or (Type(Domain(h)) eq FldFin) then
        K := Domain(h); R := PolynomialRing(K);
        return &+[ (K ! Coefficient(f, i))*R.1^i : i in [0..Degree(f)] ];
    end if;
    hi := Inverse(h); K := Codomain(hi); R := PolynomialRing(K);
    return &+[ hi(Coefficient(f, i))*R.1^i : i in [0..Degree(f)] ];

end function;


function CombineSplittingFields(K, L1, L2);

    if IsPrimeField(L1) and IsPrimeField(L2) then
        L  := K;
        h1 := hom< K -> L | >;
        h2 := hom< K -> L | >;
        h  := hom< K -> L | >;
        return L, h1, h2, h;
    end if;

    if IsPrimeField(L1) then
        L  := L2;
        h1 := hom< L1 -> L | >;
        h2 := hom< L2 -> L | L2.1 >;
        h  := hom< K  -> L | >;
        return L, h1, h2, h;
    end if;

    if IsPrimeField(L2) then
        L  := L1;
        h1 := hom< L1 -> L | L1.1 >;
        h2 := hom< L2 -> L | >;
        h  := hom< K  -> L | >;
        return L, h1, h2, h;
    end if;

    /* Create inclusions of K */
    r1 := L1 ! K.1;
    r2 := L2 ! K.1;
    K1 := sub< L1 | r1 >;
    K2 := sub< L2 | r2 >;
    if IsPrimeField(K) then
        h1 := hom< K -> K1 | >;
        h2 := hom< K -> K2 | >;
        i1 := hom< K -> L1 | >;
        i2 := hom< K -> L2 | >;
    else
        h1 := hom< K -> K1 | r1 >;
        h2 := hom< K -> K2 | r2 >;
        i1 := hom< K -> L1 | r1 >;
        i2 := hom< K -> L2 | r2 >;
    end if;

    /* Create common splitting field */
    f1 := MinimalPolynomial(L1.1, K1);
    f2 := MinimalPolynomial(L2.1, K2);
    f1 := PullbackPolynomial(h1, f1);
    f2 := PullbackPolynomial(h2, f2);
    f2 := ConjugatePolynomial(i1, f2);
    if Type(K) eq FldFin then
        L := CommonOverfield(L1, L2);
    else
        L := SplittingField(f2);
    end if;

    /* Inclusion of K */
    if IsPrimeField(K) then
        h := hom< K -> L | >;
    else
        h := hom< K -> L | L ! K.1 >;
    end if;

    /* Inclusion of L1 and L2 */
    f1 := ConjugatePolynomial(h, f1);
    f2 := ConjugatePolynomial(h, f2);
    h1 := hom< L1 -> L | Roots(f1)[1][1] >;
    h2 := hom< L2 -> L | Roots(f2)[1][1] >;

    /* Sanity check */
    assert h1(K.1) eq h2(K.1);
    assert Domain(h)  eq K ; assert Codomain(h)  eq L;
    assert Domain(h1) eq L1; assert Codomain(h1) eq L;
    assert Domain(h2) eq L2; assert Codomain(h2) eq L;
    assert MinimalPolynomial(K.1) eq MinimalPolynomial(h(K.1));
    assert MinimalPolynomial(L1.1) eq MinimalPolynomial(h1(L1.1));
    assert MinimalPolynomial(L2.1) eq MinimalPolynomial(h2(L2.1));
    return L, h1, h2, h;

    /* Final optional polredabs */
    /*
    if Type(L) eq FldNum then
        L0, h0 := Polredabs(L);
        return L0, h1*h0, h2*h0, h*h0;
    else
        return L, h1, h2, h;
    end if;
    */

end function;


function MakeRelativeFromRoot(K, L, r)

    if IsPrimeField(K) then
        h := HomFromRoot(L, L, L.1);
        return h;
    end if;
    KinL := sub< L | r >;
    h := HomFromRoot(K, KinL, r);
    f := MinimalPolynomial(L.1, KinL);
    f := PullbackPolynomial(h, f);
    Lrel := NumberField(f);
    h := HomFromRoot(L, Lrel, Lrel.1);
    ftest := MinimalPolynomial(Lrel.1, K) ;
    ftest /:= LeadingCoefficient(ftest);
    assert ftest eq f;
    return h;

end function;


function CovOrd4Deg2(F)

    f, d, n := Explode(F); n := IntegerRing()!n;

    x := Parent(f).1;
    FF := BaseRing(Parent(f));

    a := func<i | Coefficient(f, i)>;

    // (n-2)!*(2)!*(2)!/(n)!/(n)!

    // 1/4 * sum( (-1)^k*(n-k)!*(k+2)!*a(n-2-k)*a(k) , k = 0..(n-2));
    h0 := FF!1/4 * &+[ (-1)^k*Factorial(n-k)*Factorial(k+2)*a(n-2-k)*a(k) : k in [0..(n-2)]];
    h0 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    //1/4 * sum((-1)^k*(n-k)!*(k+2)!*((n-1-k)*a(n-1-k)*a(k)+(1+k)*a(n-2-k)*a(1+k)), k = 0 .. (n-2))
    h1 := FF!1/4*&+[(-1)^k*Factorial(n-k)*Factorial(k+2)*((n-1-k)*a(n-1-k)*a(k)+(1+k)*a(n-2-k)*a(1+k)) : k in [0 .. (n-2)]] ;
    h1 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    // 1/8 * sum((-1)^k*(n-k)!*(k+2)!*(	(k+2)*(k+1)*a(2+k)*a(n-2-k) +	2*(n-1-k)*(k+1)*a(1+k)*a(n-1-k) +	(n-k)*(n-1-k)*a(k)*a(n-k)), k = 0 .. (n-2))
    h2 := FF!1/8*&+[
        (-1)^k*Factorial(n-k)*Factorial(k+2)*(
        (k+2)*(k+1)*a(2+k)*a(n-2-k) +
        2*(n-1-k)*(k+1)*a(1+k)*a(n-1-k) +
        (n-k)*(n-1-k)*a(k)*a(n-k)
        )
        : k in [0 .. (n-2)]] ;
    h2 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    h3 := FF!1/4*&+[(-1)^k*Factorial(n-k)*Factorial(k+2)*((n-1-k)*a(n-k)*a(k+1)+(1+k)*a(n-1-k)*a(2+k)) : k in [0 .. (n-2)]] ;
    h3 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    h4 := FF!1/4 * &+[ (-1)^k*Factorial(n-k)*Factorial(k+2)*a(n-2-k+2)*a(k+2) : k in [0..(n-2)]];
    h4 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    return [* h4 * x^4 + h3 * x^3 + h2 * x^2 + h1 * x + h0, 2*d, 4 *];

end function;


function TransformPolynomial(f,n,mat)
    a,b,c,d := Explode(mat);
    x1 := a*Parent(f).1 + b; z1 := c*Parent(f).1 + d;
    return &+[Coefficient(f,i)*x1^i*z1^(n-i) : i in [0..n]];
end function;


function MyRandom(FF : BD := 7)
    if Characteristic(FF) eq 0 then
        return Random(-BD, BD);
    end if;
    return Random(FF);
end function;


procedure GeometricRoots(f, ~LST : geometric := true, commonfield := false)

    vprintf IsGL2Equiv, 2 : "Working on the polynomial %o\n", f;
    if not geometric then
        Rts := Roots(f);
        for tup in Rts do Append(~LST, tup[1]); end for;
        return;
    end if;

    Q := CoefficientRing(f);

    /* Single splitting field extension */
    if commonfield then
        if Type(Q) eq FldFin then
            L := SplittingField(f);
            for tup in Roots(f, L) do Append(~LST, tup[1]); end for;
            return;
        else
            _, Rts := SplittingField(f);
            for r in Rts do Append(~LST, r); end for;
            return;
        end if;
    end if;

    X := Parent(f).1;
    g := f;

    Rts := Roots(f);
    for r in Rts do
        Append(~LST, r[1]);
        g := g div (X-r[1])^r[2] ;
    end for;

    vprintf IsGL2Equiv, 2 : "Non-rational part is %o\n", g;

    /* Repeated extension (by roots of polynomials over the original base field) */
    Fct := Factorization(g);
    for fct in Fct do
        vprintf IsGL2Equiv, 2 : "Factor = %o\n", fct;
        $$(PolynomialRing(ext<Q | fct[1]>)!fct[1], ~LST : commonfield := commonfield);
        //$$(PolynomialRing(SplittingField(fct[1]))!fct[1], ~LST : commonfield := commonfield);
    end for;
end procedure;


/* Filter function: Returns those elements of MF that actually induce isomorphisms */
function CheckResult(MF, f, F, deg)

    RM := [* *];
    d := Max(Degree(f), Degree(F));

    for L in MF do

        /* Check is done over the universe of the transformations */
        FF := Parent(L[1]);

        fp := PolynomialRing(FF)!f;
        Fp := PolynomialRing(FF)!F;

        _F := TransformPolynomial(fp, deg, L);

        /* Check equality up to leading coefficients */
        if _F * Coefficient(Fp, d) eq Fp * Coefficient(_F, d) then
            Append(~RM, L);
        end if;

    end for;

    return RM;

end function;


function IsGL2GeometricEquivalentAlphaEq0(_f, _F, d : geometric := true, commonfield := false)

    Q := BaseRing(Parent(_f)); Q1 := Q.1;
    Z := PolynomialRing(Q).1;

    if not IsInvertible(Q!d) then
        vprintf IsGL2Equiv, 1 : "Unable to invert the degree of the form in the field, I give up\n";
        return true, [* *], 1;
    end if;

    a0  := Coefficient(_f, 0); a1  := Coefficient(_f, 1);
    a2  := Coefficient(_f, 2); a3  := Coefficient(_f, 3);

    bm0 := Coefficient(_F, d);   bm1 := Coefficient(_F, d-1);
    bm2 := Coefficient(_F, d-2); bm3 := Coefficient(_F, d-3);

    if a0 eq 0 then
        vprintf IsGL2Equiv, 1 : "a0 cannot be equal to zero with an isomorphism with diagonal 0\n";
        return false, [* *], 1;
    end if;

    EQ2 :=
        bm0^2*(-d*a1^2+a1^2+2*a2*d*a0)*Z^2
        -a0^2*(2*bm2*d*bm0+bm1^2-d*bm1^2);

    EQ3 :=
        2*bm0^3*(-3*d*a1^3+3*a3*d^2*a0^2+2*a1^3-3*a2*d^2*a0*a1+d^2*a1^3+6*a2*d*a0*a1)*Z^3+
        3*a0*(d-2)*bm1*bm0^2*(-d*a1^2+a1^2+2*a2*d*a0)*Z^2 -
        a0^3*(6*bm3*d^2*bm0^2-2*bm1^3-d^2*bm1^3+3*d*bm1^3);

    PG := GCD(EQ2, EQ3);

    vprintf IsGL2Equiv, 1 : "GCD = %o\n", PG;
    vprintf IsGL2Equiv, 1 : "It is of degree %o\n", Degree(PG);

    if PG eq 0 then
        vprintf IsGL2Equiv, 1 : "HUM... No algebraic condition found on beta, I give up\n";
        vprintf IsGL2Equiv, 1 : "\n";
        return true, [* *], 1;
    end if;

    if Degree(PG) eq 0 then
        vprintf IsGL2Equiv, 1 : "No such isomorphism possible\n";
        vprintf IsGL2Equiv, 1 : "\n";
        return false, [* *], 1;
    end if;

    GF := [* *]; GeometricRoots(PG, ~GF : geometric := geometric, commonfield := commonfield);

    ret := false; LST := [* *];
    for bet in GF do

        vprintf IsGL2Equiv, 1 : "Handling RootOf(%o)\n", MinimalPolynomial(bet);

        EF := Parent(bet);
        Z := PolynomialRing(EF).1;

        del := (bm1 * a0 - a1 * bet * bm0) / bm0 / a0 / d;

        L := [EF | 0, bet, 1, del];

        RM := CheckResult([* L *], _f, _F, d);

        if #RM ne 0 then
            LF := RM[1];

            if Index(LST, LF) eq 0 then
                vprintf IsGL2Equiv, 1 :  "%o\n", LF;
                Append(~LST, LF);
            end if;

        end if;

        ret or:= #RM ne 0;
    end for;

    /* Terminate early without further improvements */
    if ret then
        L := Parent(LST[1][1]);
        Q1 := L ! Q1;
    end if;
    return ret, LST, Q1;

    /* Keep only those elements that work */
    if ret then
        LST := CheckResult(LST, _f, _F, d);
    end if;

    /* Make field smaller */
    if ret and commonfield then
        L := Parent(LST[1][1]);
        Q1 := L ! Q1;
        if IsPrimeField(L) then
            L0 := L;
        else
            L0 := sub< L | [ Q1 ] cat &cat[ lst : lst in LST ] >;
        end if;
        LST := [* [ L0 ! c : c in lst ] : lst in LST *];
        Q1 := L0 ! Q1;
    end if;

    /* Make field even smaller */
    /*
    if ret and commonfield and Type(L0) eq FldNum then
        L00, h := Polredabs(L0);
        LST := [* [ h(c) : c in lst ] : lst in LST *];
        Q1 := h(Q1);
    end if;
    */

    return ret, LST, Q1;

end function;


function IsGL2GeometricEquivalentHeart(_f, _F, deg : geometric := true, commonfield := false)

    Q := BaseRing(Parent(_f)); Q1 := Q.1;
    Z := Parent(_f).1;

    if not IsInvertible(Q!deg) then
        vprintf IsGL2Equiv, 1 : "Unable to invert the degree of the form in the field, I give up\n";
        return true, [* *], 1;
    end if;

    P1 := ProjectiveSpace(Q, 1);
    x  := P1.1; y := P1.2;

    f1 := &+[ Coefficient(_f,j)*x^j*y^(deg-j) : j in [0..deg]];
    F := &+[ Coefficient(_F,j)*x^j*y^(deg-j) : j in [0..deg]];

    /* Set the (deg-1)-th coefficient of F  */
    M12 := MonomialCoefficient(F, x^(deg-1)*y );
    if M12 eq 0 then
        M21 := Q!0; f2 := F;
    else
        M12 := -M12 / ( deg * MonomialCoefficient(F,x^deg) );
        M21 := Q!0;
        f2 := Evaluate(F, x, x + M12*y);
    end if;

    vprintf IsGL2Equiv, 1 : "f2 is %o\n", f2;

    // F2 := UnivariatePolynomial(Evaluate(CoordinateRing(P1)!f2, y, 1));
    bm0 := MonomialCoefficient(f2, x^deg);
    bm2 := MonomialCoefficient(f2, x^(deg-2)*y^2);
    bm3 := MonomialCoefficient(f2, x^(deg-3)*y^3);
    if deg gt 3 then
        bm4 := MonomialCoefficient(f2, x^(deg-4)*y^4);
    end if;

    // deg coeff.
    // Evaluate(f1, [1, m21])-m11^deg*bm0;

    // deg - 1 coeff.
    // Evaluate(m12*Derivative(f1, 1, x) + Derivative(f1, 1, y), [1, m21]);

    // deg - 2 coeff.
    // Evaluate(Nm2*Evaluate(f1, [1, Z]), m21) - 2*m11^(deg-2)*m22^2*bm2*Evaluate(Derivative(f1, 1, x), [1, m21])^2;
    Nm2 := Evaluate(
        Derivative(f1, 2, x) * Derivative(f1, 1, y)^2
        - 2 * Derivative(f1, 1, x) * Derivative(f1, 1, y) * Derivative(Derivative(f1, 1, x), 1, y)
        +     Derivative(f1, 2, y) * Derivative(f1, 1, x)^2,
        [1, Z]) div  Evaluate(f1, [1, Z]);
    vprintf IsGL2Equiv, 1 : "Nm2 is of degree %o\n", Degree(Nm2);

    if deg gt 3 then

        // deg - 4 coeff.
        // Evaluate(Nm4*Evaluate(f1, [1, Z]), m21) - 24*m11^(deg-4)*m22^4*bm4*Evaluate(Derivative(f1, 1, x), [1, m21])^4;
        Nm4 := Evaluate(
            Derivative(f1, 4, x) * Derivative(f1, 1, y)^4
            - 4 * Derivative(Derivative(f1, 3, x), 1, y) * Derivative(f1, 1, y)^3 * Derivative(f1, 1, x)
            + 6 * Derivative(Derivative(f1, 2, x), 2, y) * Derivative(f1, 1, y)^2 * Derivative(f1, 1, x)^2
            - 4 * Derivative(Derivative(f1, 1, x), 3, y) * Derivative(f1, 1, y)   * Derivative(f1, 1, x)^3
            +     Derivative(f1, 4, y) * Derivative(f1, 1, x)^4,
            [1, Z]) div Evaluate(f1, [1, Z]);
        vprintf IsGL2Equiv, 1 : "Nm4 is of degree %o\n", Degree(Nm4);

        // Evaluate(6*bm0*bm4*Nm2^2 - bm2^2 * Nm4, m21);
        EQ1 := 6*bm0*bm4*Nm2^2 - bm2^2 * Nm4;
        vprintf IsGL2Equiv, 1 : "EQ1 is of degree %o\n", Degree(EQ1);

        /*
	if Degree(EQ1) eq -1 then
	    vprintf IsGL2Equiv, 1 : "No algebraic condition given by the first equation, I give up\n";
	    vprintf IsGL2Equiv, 1 : "\n";
	    return true, [* *];
	end if;
        */
    end if;

    // deg - 3 coeff.
    // Evaluate(Nm3*Evaluate(f1, [1, Z]), m21) - 6*m11^(deg-3)*m22^3*bm3*Evaluate(Derivative(f1, 1, x), [1, m21])^3;
    Nm3 := Evaluate(
        -     Derivative(f1, 3, x) * Derivative(f1, 1, y)^3
        + 3 * Derivative(Derivative(f1, 2, x), 1, y) * Derivative(f1, 1, y)^2 * Derivative(f1, 1, x)
        - 3 * Derivative(Derivative(f1, 1, x), 2, y) * Derivative(f1, 1, y)   * Derivative(f1, 1, x)^2
        +     Derivative(f1, 3, y) * Derivative(f1, 1, x)^3,
        [1, Z]) div Evaluate(f1, [1, Z]);
    vprintf IsGL2Equiv, 1 : "Nm3 is of degree %o\n", Degree(Nm3);

    // Evaluate(9*bm0* bm3^2*Nm2^3 - 2*bm2^3 * Nm3^2, m21);
    EQ2 := 9*bm0* bm3^2*Nm2^3 - 2*bm2^3 * Nm3^2;
    vprintf IsGL2Equiv, 1 : "EQ2 is of degree %o\n", Degree(EQ2);

    if deg gt 3 then PG := GCD(EQ1, EQ2); else PG := EQ2; end if;

    vprintf IsGL2Equiv, 1 : "GCD = %o\n", PG;
    vprintf IsGL2Equiv, 1 : "It is of degree %o\n", Degree(PG);

    if PG eq 0 then
        vprintf IsGL2Equiv, 1 : "No algebraic condition found on gamma, I give up\n";
        vprintf IsGL2Equiv, 1 : "\n";
        return true, [* *], 1;
    end if;

    if Degree(PG) eq 0 then
        vprintf IsGL2Equiv, 1 : "No such isomorphism possible\n";
        vprintf IsGL2Equiv, 1 : "\n";
        return false, [* *], 1;
    end if;

    GF := [* *]; GeometricRoots(PG, ~GF : geometric := geometric, commonfield := commonfield);

    LST := [* *];
    for m21 in GF do

        EF := Parent(m21); Z := PolynomialRing(EF).1;

        PEF := ProjectiveSpace(EF, 1);
        X := PEF.1; Y := PEF.2;

        F1 := &+[ MonomialCoefficient(f1,x^j*y^(deg-j))*X^j*Y^(deg-j) : j in [0..deg]];
        F2 := &+[ MonomialCoefficient(f2,x^j*y^(deg-j))*X^j*Y^(deg-j) : j in [0..deg]];

        vprintf IsGL2Equiv, 1 : "\n";
        vprintf IsGL2Equiv, 1 : "**************************************************************\n";
        vprintf IsGL2Equiv, 1 : "Testing RootOf(%o)\n", MinimalPolynomial(m21);
        vprintf IsGL2Equiv, 1 : "gamma =  %o\n", m21;

        if Evaluate(Derivative(F1, 1, X), [1, m21]) eq 0 then
            vprintf IsGL2Equiv, 1 : "HUM the derivative in m21 = 0, I give up\n";
            return true, [* *], 1;
        end if;

        m12 := - Evaluate(Derivative(F1, 1, Y), [1, m21]) / Evaluate(Derivative(F1, 1, X), [1, m21]);

        vprintf IsGL2Equiv, 1 : "Then beta = %o\n", m12;

        // Let us check the compatibility conditions
        g1 := Evaluate(F1, [X + m12*Y, m21*X + Y]);
        Pg1 := Parent(g1); w := Pg1.1;

        for i := 1 to deg-1 do

            am1 := MonomialCoefficient(g1, X^(i-1)*Y^(deg-i+1));
            am0 := MonomialCoefficient(g1, X^(i)*Y^(deg-i));
            ap1 := MonomialCoefficient(g1, X^(i+1)*Y^(deg-i-1));

            bm1 := MonomialCoefficient(F2, X^(i-1)*Y^(deg-i+1));
            bm0 := MonomialCoefficient(F2, X^(i)*Y^(deg-i));
            bp1 := MonomialCoefficient(F2, X^(i+1)*Y^(deg-i-1));

            if am1*ap1*bm0^2 - bm1*bp1*am0^2 ne 0 then
                vprintf IsGL2Equiv, 1 : "Bad compatibility conditions 1? I give up\n";
                continue m21;
            end if;

        end for;

        /* Looking for non-zero coeffs in f2 */
        degs := [j : j in [2..deg] | MonomialCoefficient(F2, X^(deg-j)*Y^j) ne 0];
        g, U := XGCD(degs);
        if g ne 1 then
            vprintf IsGL2Equiv, 1 : "HUM g =  %o\n", g;
            //		return [* *];
        end if;

        /* Are there corresponding coefficients in g1 non-zero ? */
        for d := 0 to deg do

            if ((MonomialCoefficient(g1, X^(deg-d)*Y^d) eq 0 and
                MonomialCoefficient(F2, X^(deg-d)*Y^d) ne 0) or
                (MonomialCoefficient(g1, X^(deg-d)*Y^d) ne 0 and
                MonomialCoefficient(F2, X^(deg-d)*Y^d) eq 0)) then

                vprintf IsGL2Equiv, 1 : "Bad compatibility conditions 2? I give up\n";
                vprintf IsGL2Equiv, 1 : "F2 = %o\n", F2;
                vprintf IsGL2Equiv, 1 : "g1 = %o\n", g1;
                continue m21;
            end if;
        end for;

        m := MonomialCoefficient(g1, X^(deg)) / MonomialCoefficient(F2, X^(deg));

        R :=
            &*[ (m * MonomialCoefficient(F2, X^(deg-degs[j])*Y^degs[j]))^U[j]: j in [1..#degs]]
            /
            &*[ MonomialCoefficient(g1, X^(deg-degs[j])*Y^degs[j])^U[j]: j in [1..#degs]];

        vprintf IsGL2Equiv, 1 : "R = %o\n", R;
        RR := [* *]; GeometricRoots(Z^g - R, ~RR : geometric := geometric, commonfield := commonfield);

        vprintf IsGL2Equiv, 1 : "F2 = %o\n", F2;
        vprintf IsGL2Equiv, 1 : "g1 = %o\n", g1;

        for RL in RR do

            EF3 := Parent(RL); Z := PolynomialRing(EF3).1;

            Mat :=
                1/(1 - M12*M21) *
                Matrix(2, 2, [1, RL * m12, m21, RL]) *
                Matrix(2, 2, [1, -M12, -M21, 1]);

            Mat *:= 1 / Mat[1,1];

            FF := Q; LF := Eltseq(Mat);

            RM := CheckResult([* LF *], _f, _F, deg);

            if #RM ne 0 then

                if Index(LST, LF) eq 0 then
                    vprintf IsGL2Equiv, 1 : "%o\n", LF;
                    Append(~LST, LF);
                end if;

            end if;

        end for;

    end for;

    ret := #LST ne 0;
    /* Terminate early without further improvements */
    if ret then
        L := Parent(LST[1][1]);
        Q1 := L ! Q1;
    end if;
    return ret, LST, Q1;

    /* Keep only those elements that work */
    if ret then
        LST := CheckResult(LST, _f, _F, deg);
    end if;

    /* Make field smaller */
    if ret and commonfield then
        L := Parent(LST[1][1]);
        Q1 := L ! Q1;
        if IsPrimeField(L) then
            L0 := L;
        else
            L0 := sub< L | [ Q1 ] cat &cat[ lst : lst in LST ] >;
        end if;
        LST := [* [ L0 ! c : c in lst ] : lst in LST *];
        Q1 := L0 ! Q1;
    end if;

    /* Make field even smaller */
    /*
    if ret and commonfield and Type(L0) eq FldNum then
        L00, h := Polredabs(L0);
        LST := [* [ h(c) : c in lst ] : lst in LST *];
        Q1 := h(Q1);
    end if;
    */

    return ret, LST, Q1;

end function;


function IsGL2GeometricEquivalentMain(_f, _F, deg : geometric := true, commonfield := false)

    PX := Parent(_f); Q := BaseRing(PX);

    vprintf IsGL2Equiv, 1 : "\n\n";
    vprintf IsGL2Equiv, 1 : "------------------------------\n";
    vprintf IsGL2Equiv, 1 : " f = %o\n", _f;
    vprintf IsGL2Equiv, 1 : " F = %o\n", _F;

    /* Special case: alpha equals zero */
    ret0, MF0, Q10 := IsGL2GeometricEquivalentAlphaEq0(_f, _F, deg : geometric := geometric, commonfield := commonfield);
    if ret0 and #MF0 eq 0 then
        return ret0, MF0, [* *];
    end if;

    vprintf IsGL2Equiv, 1 : "After the Alpha = 0 step\n";
    vprintf IsGL2Equiv, 1 : "ret = %o, MF = %o\n", ret0, MF0;

    /* Generic case */
    retp, MFp, Q1p := IsGL2GeometricEquivalentHeart(_f, _F, deg : geometric := geometric, commonfield := commonfield);
    if retp and #MFp eq 0 then
        return retp, MFp, [* *];
    end if;

    ret := ret0 or retp;
    MFL := [* MF0, MFp *];
    Q1L := [* Q10, Q1p *];

    return ret, MFL, Q1L;
end function;


function CheckNormalizeToCommonBase(ret, MFL, Q1L, _f, _F, deg : geometric := true, commonfield := false);

    MFL := [* [* Eltseq(M) : M in MF *] : MF in MFL *];
    Q := BaseRing(Parent(_f));

    /* Throw away irrelevant entries */
    ks := [ k : k in [1..#MFL] | #MFL[k] ne 0 ];
    MFL := [* MFL[k] : k in ks *]; Q1L := [* Q1L[k] : k in ks *];
    assert ret eq (#MFL ne 0);
    if #MFL eq 0 then
        return false, [ ];
    end if;

    /* Throw away non-solutions */
    MFL := [* CheckResult(MF, _f, _F, deg) : MF in MFL *];
    ks := [ k : k in [1..#MFL] | #MFL[k] ne 0 ];
    MFL := [* MFL[k] : k in ks *]; Q1L := [* Q1L[k] : k in ks *];
    if #MFL eq 0 then
        return false, [ ];
    end if;

    /* Normalize by row */
    MFL0 := [ ];
    for MF in MFL do
        MF0 := [* *];
        for mf in MF do
            i0 := Minimum([ i : i in [1..#mf] | mf[i] ne 0 ]);
            mf0 := [ c/mf[i0] : c in mf ];
            Append(~MF0, mf0);
        end for;
        Append(~MFL0, MF0);
    end for;
    MFL := MFL0;

    if not geometric then
        ret := #MFL ne 0; assert ret;
        return ret, MFL;
    end if;

    /* Make the individual fields small */
    if commonfield then
        MFL0 := [ ]; Q1L0 := [* *];
        for i in [1..#MFL] do

            /* Make field smaller */
            MF := MFL[i]; Q1 := Q1L[i];
            L := Parent(MF[1][1]);
            if IsPrimeField(L) then
                L0 := L;
            else
                L0 := sub< L | [ Q1 ] cat &cat[ mf : mf in MF ] >;
            end if;
            MF0 := [* [ L0 ! c : c in mf ] : mf in MF *];
            Q10 := L0 ! Q1;
            Append(~MFL0, MF0); Append(~Q1L0, Q10);

            /* Make field even smaller */
            /*
            L00, h := Polredabs(L0);
            MF00 := [* [ h(c) : c in mf ] : mf in MF0 *];
            Q100 := h(Q10);
            Append(~MFL0, MF00); Append(~Q1L0, Q100);
            */
        end for;
        MFL := MFL0; Q1L := Q1L0;
    end if;

    /* Merge the solutions */
    if not commonfield then
        if #MFL eq 1 then
            MF := MFL[1];
        else
            MF := MFL[1] cat MFL[2];
        end if;
    else
        if #MFL eq 1 then
            MF := MFL[1];
        else
            L1 := Parent(MFL[1][1][1]); Q1 := Q1L[1]; assert Q1 in L1;
            L2 := Parent(MFL[2][1][1]);
            L, h1, h2, h := CombineSplittingFields(Q, L1, L2);
            Q1L := [ h(Q.1) ];
            MF1 := [* [ h1(c) : c in M ] : M in MFL[1] *];
            MF2 := [* [ h2(c) : c in M ] : M in MFL[2] *];
            MF := MF1 cat MF2;
        end if;
    end if;

    /* Make the field small again */
    /*
    if commonfield then
        L := Universe(MF[1]); Q1 := Q1L[1];
        if IsPrimeField(L) then
            L0 := L;
        else
            L0 := sub< L | [ Q1 ] cat &cat[ mf : mf in MF ] >;
        end if;
        MF0 := [* [ L0 ! c : c in mf ] : mf in MF *];
        Q10 := L0 ! Q1;
        MF := MF0; Q1L := [ Q10 ];
    end if;
    */

    /* Make field even smaller */
    /*
    if commonfield then
        L00, h := Polredabs(L0);
        MF00 := [* [ h(c) : c in mf ] : mf in MF0 *];
        Q100 := h(Q10);
        MF := MF00; Q1 := [ Q100 ];
    end if;
    */

    /* Make the field relative */
    if commonfield and Type(L) eq FldNum then
        h := MakeRelativeFromRoot(Q, L, Q1L[1]);
        MF := [* [ h(c) : c in M ] : M in MF *];
    end if;

    /* Flatten list */
    if commonfield then
        MF := [ M : M in MF ];
    end if;

    ret := #MF ne 0; assert ret;
    return ret, MF;

end function;


function IsGL2GeometricEquivalentCandidates(_f, _F, deg :
    geometric := false, covariant := true, commonfield := false)

    Q := BaseRing(Parent(_f));

/* To be improved
    if  not IsInvertible(Q!deg) then
        f0 := Sort([ PF[1] : PF in Factorization(_f) ], func<a,b|Degree(a)-Degree(b)>)[1];
        F0 := Sort([ PF[1] : PF in Factorization(_F) ], func<a,b|Degree(a)-Degree(b)>)[1];
        L := Q;
        if Degree(f0) gt 1 or Degree(F0) gt 1 then
            L := SplittingField(f0*F0);
        end if;
        f := PolynomialRing(L)!_f;
        r := Roots(f)[1, 1];
        f := TransformPolynomial(f, deg, [r, r, 1, 0]);


        F := PolynomialRing(L)!_F;
        R := Roots(F)[1, 1];
        F := TransformPolynomial(F, deg, [R, R, 1, 0]);

        ret, ML := IsGL2GeometricEquivalentCandidates(f, F, deg-1);
    end if;
*/

    if covariant then

        /* Covariant reduction, when possible */
        p := Characteristic(Q) eq 0 select Infinity() else Characteristic(Q);

        if Degree(_f) gt 4 and Degree(_f) lt p and
            Degree(_F) gt 4 and Degree(_F) lt p then

            vprintf IsGL2Equiv, 1 : "Covariant reduction step\n";
            Cf := CovOrd4Deg2([* _f, 1, deg *])[1];
            CF := CovOrd4Deg2([* _F, 1, deg *])[1];

            if Degree(Cf) ge 3 and Discriminant(Cf) ne 0 and
                Degree(CF) ge 3 and Discriminant(CF) ne 0 then

                ret, MFL, Q1L := $$(Cf, CF, 4 : geometric := geometric, covariant := covariant, commonfield := commonfield);
                if not (ret eq true and #MFL eq 0) then
                    return ret, MFL, Q1L;
                end if;

            end if;
        else
            vprintf IsGL2Equiv, 1 : "Covariant reduction is not possible\n";
        end if;
    end if;

    /* Main algorithm */
    nbtry := 0; ret := true; MFL := [* *];
    while IsInvertible(Q!deg) and ret eq true and #MFL eq 0 and nbtry lt 20 do
        nbtry +:= 1; f := _f; F := _F; ML := IdentityMatrix(Q, 2);

        if nbtry ne 1 then
            repeat
                ML := Matrix(2, 2, [Q | MyRandom(Q : BD := Degree(_f)+1) : i in [1..4]]);
            until &*Eltseq(ML) ne 0 and Determinant(ML) ne 0;
            f := TransformPolynomial(_f, deg, Eltseq(ML));
            F := TransformPolynomial(_F, deg, Eltseq(ML));
        end if;

        vprintf IsGL2Equiv, 1 : "ML is %o\n", ML;

        if Degree(f) ne deg or Degree(F) ne deg then continue; end if;
        MLi := ML^(-1);

        ret, MFL, Q1L := IsGL2GeometricEquivalentMain(f, F, deg : geometric := geometric, commonfield := commonfield);
        /* Throw away irrelevant entries */
        ks := [ k : k in [1..#MFL] | #MFL[k] ne 0 ];
        MFL := [* MFL[k] : k in ks *]; Q1L := [* Q1L[k] : k in ks *];

        /* Convert to matrices, conjugate, and convert back */
        MFML := [* [* Matrix(2, 2, A) : A in MF *] : MF in MFL *];
        MFL := [* *];
        for i in [1..#MFML] do
            L := BaseRing(MFML[i][1]);
            if commonfield then
                h := HomFromRoot(Q, L, Q1L[i]);
                T := ConjugateMatrix(h, ML);
                Ti := ConjugateMatrix(h, MLi);
                Append(~MFL, [* T*A*Ti : A in MFML[i] *]);
            else
                MF := [* *];
                for A in MFML[i] do
                    L := BaseRing(A);
                    TL := Matrix(L, 2, 2, Eltseq(ML));
                    TLi := Matrix(L, 2, 2, Eltseq(MLi));
                    Append(~MF, TL*A*TLi);
                end for;
                Append(~MFL, MF);
            end if;
        end for;
        MFL := [* [* Eltseq(A) : A in MF *] : MF in MFL *];

        /* Return if problem case not encountered */
        if not (ret eq true and #MFL eq 0) then
            return ret, MFL, Q1L;
        end if;
    end while;

    if not IsInvertible(Q!deg) then
       vprintf IsGL2Equiv, 1 : "Unable to invert the degree of the form in the field, I give up\n";
    end if;

    /* Classical one in the very rare cases where nothing else was possible
   (this may happen by accident and over small finite fields) */
   if not geometric then
       ret, MF := IsGL2Equivalent(_f, _F, deg);
       MFL := [* MF *]; Q1L := [* Q.1 *];
       return ret, MFL, Q1L;
   end if;

   if Type(Q) eq FldFin then
       L := SplittingField(_f*_F);
   else
       L := SplittingField([_f, _F]);
   end if;
   ret, MF := IsGL2Equivalent(PolynomialRing(L)!_f, PolynomialRing(L)!_F, deg);
   MFL := [* MF *]; Q1L := [* L ! Q.1 *];
   return ret, MFL, Q1L;

end function;


intrinsic IsGL2EquivalentExtended(f1::RngUPolElt, f2::RngUPolElt, deg::RngIntElt :
    geometric := false, covariant := true, commonfield := false) -> BoolElt, List
    {Returns a boolean indicating whether a matrix T exists such that the change of variable induced on f1 by T, f1*T, is a multiple of f2, as well as a full list of all such matrices.}

    /* Refer and normalize back */
    if not geometric then commonfield := false; end if;

    ret, MFL, Q1L := IsGL2GeometricEquivalentCandidates(f1, f2, deg : geometric := geometric, covariant := covariant, commonfield := commonfield);

    test, seqs := CheckNormalizeToCommonBase(ret, MFL, Q1L, f1, f2, deg : commonfield := commonfield);

    return test, [* Matrix(2, 2, seq) : seq in seqs *];

end intrinsic;


/***
 * Reduced isomorphism routines
 ******************************/

/* Isomorphism test */
intrinsic IsReducedIsomorphicHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
    geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
    {Returns a boolean indicating whether a matrix T exists that induces an isomorphism f1(x) --> f2(x) (f1 and f2 are assumed to be of even degree), as well as a full list of all such matrices.}

    K := CoefficientRing(f1);
    require K eq CoefficientRing(f2) :
        "The coefficient rings of f1 and f2 must be equal";
    require IsUnit(K!2) :
        "2 must be a unit in the coefficient ring of f1 and f2";

    d1 := 2*((Degree(f1) + 1) div 2); d2 := 2*((Degree(f2) + 1) div 2);
    if d1 ne d2 then return false, [* *]; end if;
    ret, Ts := IsGL2EquivalentExtended(f2, f1, d1 :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

    return ret, Ts;

end intrinsic;

intrinsic IsReducedIsomorphicHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
    geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
    {Returns a boolean indicating whether a matrix T exists that induces an isomorphism f1(x) --> f2(x) (f1 and f2 resp. define X1 and X2), as well as a full list of all such matrices.}

    K := BaseRing(X1);
    require K eq BaseRing(X2) :
        "The base rings of X1 and X2 must be equal";
    require IsUnit(K!2) :
        "2 must be a unit in the base ring of X1 and X2";

    f1, h1 := HyperellipticPolynomials(X1);
    f2, h2 := HyperellipticPolynomials(X2);
    g1 := h1 eq 0 select f1 else 4*f1 + h1^2;
    g2 := h2 eq 0 select f2 else 4*f2 + h2^2;

    return  IsReducedIsomorphicHyperellipticCurves(g1, g2 :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

end intrinsic;


/* Isomorphism list */
intrinsic ReducedIsomorphismsOfHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
    geometric := false, covariant := true, commonfield := true) ->  List
    {Returns a full list of matrices T that induce an isomorphism f1(x) --> f2(x) (f1 and f2 are assumed to be of even degree).}

    _, Ts := IsReducedIsomorphicHyperellipticCurves(f1, f2 :
        geometric := geometric, covariant := covariant, commonfield := commonfield);
    return Ts;

end intrinsic;

intrinsic ReducedIsomorphismsOfHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
    geometric := false, covariant := true, commonfield := true) ->  List
    {Returns a full list of matrices T that induce an isomorphism f1(x) --> f2(x) (f1 and f2 resp. define X1 and X2).}

    _, Ts := IsReducedIsomorphicHyperellipticCurves(X1, X2 :
        geometric := geometric, covariant := covariant, commonfield := commonfield);
    return Ts;

end intrinsic;


/* Automorphism list */
intrinsic ReducedAutomorphismsOfHyperellipticCurve(f::RngUPolElt :
    geometric := false, commonfield := true, covariant := true) -> List
    {Return the automorphisms of the polynomial f(x) (assumed to be of even degree), as a full list of matrices T.}

    K := CoefficientRing(f);
    require IsUnit(K!2) :
        "2 must be a unit in the base ring of f";

    return ReducedIsomorphismsOfHyperellipticCurves(f, f :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

end intrinsic;

intrinsic ReducedAutomorphismsOfHyperellipticCurve(X::CrvHyp :
    geometric := false, commonfield := true, covariant := true) -> List
    {Return the automorphism group of the defining polynomial of X, as a full list of matrices T.}

    K := BaseRing(X);
    require IsUnit(K!2) :
        "2 must be a unit in the base ring of X";

    return ReducedIsomorphismsOfHyperellipticCurves(X, X :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

end intrinsic;


/***
 * Isomorphism routines
 ***********************/

/* Isomorphism test */
intrinsic IsIsomorphicHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
    geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
    {Returns a boolean indicating whether a matrix T and a scalar e exist that induce an isomorphism y^2 = f1(x) --> y^2 = f2(x), as well as a full list of all such pairs.}

    function Normalize22Column(T)
        col := Eltseq(Rows(Transpose(T))[1]);
        i0 := Minimum([ i : i in [1..#col] | col[i] ne 0 ]);
        return (1/col[i0])*T;
    end function;

    K := CoefficientRing(f1);
    require K eq CoefficientRing(f2) :
        "The coefficient rings of f1 and f2 must be equal";
    require IsUnit(K!2) :
        "2 must be a unit in the coefficient ring of f1 and f2";

    g1 := f1; g2 := f2;
    d1 := 2*((Degree(g1) + 1) div 2); d2 := 2*((Degree(g2) + 1) div 2);
    if d1 ne d2 then return false, []; end if;
    test, Ts := IsGL2EquivalentExtended(g2, g1, d1 : geometric := geometric, covariant := covariant, commonfield := commonfield);
    if not test then return false, []; end if;

    if not geometric then
        pairs := [* *];
        for T in Ts do
            U := Normalize22Column(T);
            K := BaseRing(U);
            R := PolynomialRing(K);
            h1 := &+[ (K ! Coefficient(g1, j))*R.1^j : j in [0..Degree(g1)] ];
            h2 := &+[ (K ! Coefficient(g2, j))*R.1^j : j in [0..Degree(g2)] ];
            scal := K ! (TransformPolynomial(h2, d2, Eltseq(U))/h1);
            test, e := IsSquare(scal);
            if test then
                Append(~pairs, < U,  e >);
                Append(~pairs, < U, -e >);
            end if;
        end for;
        return #pairs ne 0, pairs;
    end if;

    /* Either elementwise */
    if not commonfield then
        pairs := [* *];
        for T in Ts do
            U := Normalize22Column(T);
            K := BaseRing(U);
            R := PolynomialRing(K);
            h1 := &+[ (K ! Coefficient(g1, j))*R.1^j : j in [0..Degree(g1)] ];
            h2 := &+[ (K ! Coefficient(g2, j))*R.1^j : j in [0..Degree(g2)] ];
            scal := K ! (TransformPolynomial(h2, d2, Eltseq(U))/h1);
            test, e := IsSquare(scal);
            if test then
                Append(~pairs, < U,  e >);
                Append(~pairs, < U, -e >);
            else
                L := ext< BaseRing(U) | R.1^2 - scal >;
                e := L.1; assert e^2 eq scal;
                Append(~pairs, < ChangeRing(U, L),  e >);
                Append(~pairs, < ChangeRing(U, L), -e >);
            end if;
        end for;
        return #pairs ne 0, pairs;
    end if;

    /* Or keep extending */
    pairs := [* *]; i := 0;
    Us := [* Normalize22Column(T) : T in Ts *];
    repeat
        i +:= 1;
        U := Us[i];
        K := BaseRing(U);
        R := PolynomialRing(K);
        h1 := &+[ (K ! Coefficient(g1, j))*R.1^j : j in [0..Degree(g1)] ];
        h2 := &+[ (K ! Coefficient(g2, j))*R.1^j : j in [0..Degree(g2)] ];
        scal := K ! (TransformPolynomial(h2, d2, Eltseq(U))/h1);
        test, e := IsSquare(scal);
        if test then
            Append(~pairs, < U,  e >);
            Append(~pairs, < U, -e >);
        else
            L := SplittingField(R.1^2 - scal);
            RL := PolynomialRing(L);
            e := Roots(RL.1^2 - (L ! scal))[1][1]; assert e^2 eq (L ! scal);
            hom1 := HomFromRoot(K, L, L ! K.1);
            Us := [* ConjugateMatrix(hom1, U) : U in Us *];
            pairs := [* < ConjugateMatrix(hom1, pair[1]), hom1(pair[2]) > : pair in pairs *];
            U := ConjugateMatrix(hom1, U);

            if Type(K) eq FldNum then
                F := BaseRing(K);
                rt := hom1(K ! F.1);
                hom2 := MakeRelativeFromRoot(F, L, rt);
                Us := [* ConjugateMatrix(hom2, U) : U in Us *];
                pairs := [* < ConjugateMatrix(hom2, pair[1]), hom2(pair[2]) > : pair in pairs *];
                U := ConjugateMatrix(hom2, U);
                e := hom2(e);
            end if;
            Append(~pairs, < U, -e >);
            Append(~pairs, < U,  e >);
        end if;
    until i eq #Ts;
    return #pairs ne 0, pairs;

end intrinsic;

intrinsic IsIsomorphicHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
    geometric := false, covariant := true, commonfield := true) ->  BoolElt, List
    {Returns a boolean indicating whether a matrix T and a scalar e exist that induce an isomorphism X1 --> X2, as well as a full list of all such pairs.}

    K := BaseRing(X1);
    require K eq BaseRing(X2) :
        "The base rings of X1 and X2 must be equal";
    require IsUnit(K!2) :
        "2 must be a unit in the base ring of X1 and X2";

    f1, h1 := HyperellipticPolynomials(X1);
    f2, h2 := HyperellipticPolynomials(X2);
    g1 := h1 eq 0 select f1 else 4*f1 + h1^2;
    g2 := h2 eq 0 select f2 else 4*f2 + h2^2;

    return IsIsomorphicHyperellipticCurves(g1, g2  :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

end intrinsic;

/* Isomorphisms */
intrinsic IsomorphismsOfHyperellipticCurves(f1::RngUPolElt, f2::RngUPolElt :
    geometric := false, covariant := true, commonfield := true) -> List
    {Returns a full list of pairs of matrices T and scalars e that induce an isomorphism y^2 = f1(x) --> y^2 = f2(x).}

    _, pairs := IsIsomorphicHyperellipticCurves(f1, f2 :
        geometric := geometric, covariant := covariant, commonfield := commonfield);
    return pairs;

end intrinsic;

intrinsic IsomorphismsOfHyperellipticCurves(X1::CrvHyp, X2::CrvHyp :
    geometric := false, covariant := true, commonfield := true) ->  List
    {Returns a full list of pairs of matrices T and scalars e that induce an isomorphism X1 --> X2.}

    _, pairs := IsIsomorphicHyperellipticCurves(X1, X2 :
        geometric := geometric, covariant := covariant, commonfield := commonfield);
    return pairs;

end intrinsic;

/* Automorphisms */
intrinsic AutomorphismsOfHyperellipticCurve(f::RngUPolElt :
    geometric := false, commonfield := true, covariant := true) -> List
    {Returns a full list of pairs of matrices T and scalars e that induce an automorphism of the curve y^2 = f(x).}

    return IsomorphismsOfHyperellipticCurves(f, f :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

end intrinsic;

intrinsic AutomorphismsOfHyperellipticCurve(X::CrvHyp :
    geometric := false, commonfield := true, covariant := true) -> List
    {Returns a full list of pairs of matrices T and scalars e that induce an automorphism of the curve X.}

    return IsomorphismsOfHyperellipticCurves(X, X :
        geometric := geometric, covariant := covariant, commonfield := commonfield);

end intrinsic;
