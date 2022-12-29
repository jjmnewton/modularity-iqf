/***
 *  Enumerating, up to isomorphism, all the genus 3 hyperelliptic curves
 *  defined over a finite field.
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
 *  Copyright 2011-2020, R. Lercier & C. Ritzenthaler
 */

 /*

  This program enumerates all the isomorphic classes of gneus 3 hyperelliptic
  models modulo some prime p.


  Three possible uses:

     _ If you type "magma p:=11 hg3enum.m", the script enumerates modulo 11
     (or p = any other prime power, up to you) all the posible shioda invariants
     modulo 11, and read from them the geometric automorphism
     groups. Statistics are regularly printed.

     _ If you type "magma p:=11 reconstruct:=true twists:=true hg3enum.m",
     the script enumerates modulo 11 (or p = any other prime power, up to you) all
     the posible shioda invariants modulo 11, and reconstruct from them a model
     for the twists that share these invariants. Statistics are regularly
     printed. Records of the form
                        1. Shioda Invariants
                        2. Automorphism group
                        3. Singular curve or not
                        4. Number of models
                        5. Models
     for all the curves are stored in the file CurvesMod_11.dat.gz.
     See the functions WriteCurves() and ReadCurves() for a precise description
     of the format of these records.

     _ If you type "magma p:=11 reload:=true hg3enum.m", the script
     read the file CurvesMod_11.dat.gz (or p = any other prime, up to you),
     one record by one record. Statistics are regularly printed too

     Databases "CurvesMod_p.dat.gz" of curves for all the primes p between 11
     and 47 have been computed by the authors and are available on request.
 */

/* Is p defined on the command line ? */
if not assigned(p) then
  "Usage: \"magma p:=11 [reconstruct:=true] [reload:=true] hg3enum.m\""; quit;
end if;

/* Defaults */
//SetHistorySize(0);
if not assigned(reconstruct) then reconstruct := false; end if;
if not assigned(reload) then reload := false; end if;
if not assigned(twists) then twists := false; end if;

/* Convert arguments provided on the command line */
if Type(p) eq MonStgElt then
    p := StringToInteger(p);
end if;
if not IsPrime(p) then
    "The integer p must be a prime, I give up";
    quit;
end if;

if Type(reconstruct) eq MonStgElt and reconstruct eq "true" then
    reconstruct := true;
else
    reconstruct := false;
end if;

if Type(reload) eq MonStgElt and reload eq "true" then
    reload := true;
else
    reload := false;
end if;

if Type(twists) eq MonStgElt and twists eq "true" then
    twists := true;
else
    twists := false;
end if;

if reconstruct and reload then
    "The Options \"reconstruct\" and \"reload\" can not be both set to true, I give up";
    quit;
end if;

function NbTwists(q)

    if q mod 2 ne 0 then
	return
	    2 * q^5
	    + 2 * q^3
	    - 2
	    - 2 * ( ((q+1) mod 4 eq 0)                    select q^2-q else 0 )
	    + 2 * ( ((q mod 2) ne 0) and ((q mod 3) ne 0) select q-1   else 0 )
	    + ( ((q-1) mod 8 eq 0)                        select 4     else 0 )
	    + ( ((q-1) mod 7 eq 0)                        select 12    else 0 )
	    + ( (q mod 7 eq 0)                            select 2     else 0 )
	    + ( ((q mod 12) in {1, 5})                    select 2     else 0
	    );
    end if;

    n := Round(Log(2, q));
    NbAriTheo := 0;

    /* (1,1,1,1)-split case */
    NbAriTheo +:= (q-2)*(q-1)^2*(q^2-2*q+4)/12;

    /* (1,1,1,1)-split+quad case */
    NbAriTheo +:= q^3*(q-1)^2/2;

    /* (1,1,1,1)-quad case */
    NbAriTheo +:= q*(q-1)*(q-2)*(q^2+q+2)/4;

    /* (1,1,1,1)-cubic case */
    NbAriTheo +:= 2*(q^2-1)*(q^3-1)/3;

    /* (1,1,1,1)-quartic case */
    NbAriTheo +:= q*(q^2-1)*(q^2+2)/2;

    /* (1,1,3)-split case */
    NbAriTheo +:= q*(q-1)*(2*q^2-4*q+3)/2;

    /* (1,1,3)-quad case */
    NbAriTheo +:= q*(q-1)*(2*q^2-1)/2;

    /* (3,3)-split case */
    NbAriTheo +:= q*(q^2-1)+((n mod 2 eq 0) select 2*(q-1) else 0);

    /* (3,3)-quad case */
    NbAriTheo +:= q*(q^2-1)+(((n mod 2) eq 0) select 0    else 2*(q-1));

    /* (1,5) case */
    NbAriTheo +:= 2*q^2*(q-1);

    /* (7) case */
    NbAriTheo +:= 2*q^2+((n mod 3 eq 0) select 12 else 0);

    return NbAriTheo;

end function;

/* Some tools */
procedure PrintStats(tm, nbfree, nball, S8, G672, D12, C14, C2D8, C2, U6, V8, C4, D4, C2S4, C2C4, C2p3)

    m := Degree(GF(p));

    "";
    "************";
    "*", nbfree, "/", p^5+p^4+p^3+p^2+p+2, " inv. tested in", Cputime(tm), "s";
    "";

    TotGen3 := S8[1] + G672[1] + D12[1] + C14[1] + C2D8[1] + C2[1] + U6[1] + V8[1] + C4[1] + D4[1] + C2S4[1] + C2C4[1] + C2p3[1];
    TotTwists := S8[3] + G672[3] + D12[3] + C14[3] + C2D8[3] + C2[3] + U6[3] + V8[3] + C4[3] + D4[3] + C2S4[3] + C2C4[3] + C2p3[3];
    TotSing := S8[2] + G672[2] + D12[2] + C14[2] + C2D8[2] + C2[2] + U6[2] + V8[2] + C4[2] + D4[2] + C2S4[2] + C2C4[2] + C2p3[2];

    "  ", nbfree, "free invariants obtained,", p^5+p^4+p^3+p^2+p+2, "awaited";
    "  ", nball,  "invariants obtained";
    "  ", TotGen3,"curves found up to some geo. isomorphism,", p^5, "awaited";
    "  ", TotTwists+TotGen3,"curves found up to some arith. isomorphism,", NbTwists(p), "awaited";
    "";

    "Automorphism group statistics are:";"";
    /* C2 */
    L1 := Sprintf( "      & C2         ");
    L2 := Sprintf( "Gen 3 & %7o    ",  C2[1]);
    L3 := Sprintf( "Twist & %7o    ",  C2[3]);
    L4 := Sprintf( "Sing. & %7o    ",  C2[2]);
    L5 := Sprintf( "Total & %7o    ", &+C2);

    /* C2xC2 */
    if &+D4 ne 0 then
	L1 cat:= Sprintf( "& D4         ");
	L2 cat:= Sprintf( "& %7o    ",  D4[1]);
	L3 cat:= Sprintf( "& %7o    ",  D4[3]);
	L4 cat:= Sprintf( "& %7o    ",  D4[2]);
	L5 cat:= Sprintf( "& %7o    ",  &+D4);
    end if;

    /* C4 */
    if &+D4 ne 0 then
	L1 cat:= Sprintf("& C4         ");
	L2 cat:= Sprintf("& %7o    ",  D4[1]);
	L3 cat:= Sprintf("& %7o    ",  D4[3]);
	L4 cat:= Sprintf("& %7o    ",  D4[2]);
	L5 cat:= Sprintf("& %7o    ",  &+D4);
    end if;

    /* C2p3 */
    if &+D4 ne 0 then
	L1 cat:= Sprintf("& C2p3       ");
	L2 cat:= Sprintf("& %7o    ",  D4[1]);
	L3 cat:= Sprintf("& %7o    ",  D4[3]);
	L4 cat:= Sprintf("& %7o    ",  D4[2]);
	L5 cat:= Sprintf("& %7o    ",  &+D4);
    end if;

    /* C2C4 */
    if &+C2C4 ne 0 then
	L1 cat:= Sprintf("& C2C4       ");
	L2 cat:= Sprintf("& %7o    ",  C2C4[1]);
	L3 cat:= Sprintf("& %7o    ",  C2C4[3]);
	L4 cat:= Sprintf("& %7o    ",  C2C4[2]);
	L5 cat:= Sprintf("& %7o    ",  &+C2C4);
    end if;

    /* D12 */
    if &+D12 ne 0 then
	L1 cat:= Sprintf("& D12        ");
	L2 cat:= Sprintf("& %7o    ",  D12[1]);
	L3 cat:= Sprintf("& %7o    ",  D12[3]);
	L4 cat:= Sprintf("& %7o    ",  D12[2]);
	L5 cat:= Sprintf("& %7o    ",  &+D12);
    end if;

    /* C2D8 */
    if &+C2D8 ne 0 then
	L1 cat:= Sprintf("& C2D8       ");
	L2 cat:= Sprintf("& %7o    ",  C2D8[1]);
	L3 cat:= Sprintf("& %7o    ",  C2D8[3]);
	L4 cat:= Sprintf("& %7o    ",  C2D8[2]);
	L5 cat:= Sprintf("& %7o    ",  &+C2D8);
    end if;

    /* C14 */
    if &+C14 ne 0 then
	L1 cat:= Sprintf("& C14        ");
	L2 cat:= Sprintf("& %7o    ",  C14[1]);
	L3 cat:= Sprintf("& %7o    ",  C14[3]);
	L4 cat:= Sprintf("& %7o    ",  C14[2]);
	L5 cat:= Sprintf("& %7o    ",  &+C14);
    end if;

    /* U6 */
    if &+U6 ne 0 then
	L1 cat:= Sprintf("& U6         ");
	L2 cat:= Sprintf("& %7o    ",  U6[1]);
	L3 cat:= Sprintf("& %7o    ",  U6[3]);
	L4 cat:= Sprintf("& %7o    ",  U6[2]);
	L5 cat:= Sprintf("& %7o    ",  &+U6);
    end if;

    /* V8 */
    if &+V8 ne 0 then
	L1 cat:= Sprintf("& V8         ");
	L2 cat:= Sprintf("& %7o    ",  V8[1]);
	L3 cat:= Sprintf("& %7o    ",  V8[3]);
	L4 cat:= Sprintf("& %7o    ",  V8[2]);
	L5 cat:= Sprintf("& %7o    ",  &+V8);
    end if;

    /* C2S4 */
    if &+C2S4 ne 0 then
	L1 cat:= Sprintf("& C2S4       ");
	L2 cat:= Sprintf("& %7o    ",  C2S4[1]);
	L3 cat:= Sprintf("& %7o    ",  C2S4[3]);
	L4 cat:= Sprintf("& %7o    ",  C2S4[2]);
	L5 cat:= Sprintf("& %7o    ",  &+C2S4);
    end if;

    /* G672 */
    if &+G672 ne 0 then
	L1 cat:= Sprintf("& G672       ");
	L2 cat:= Sprintf("& %7o    ",  G672[1]);
	L3 cat:= Sprintf("& %7o    ",  G672[3]);
	L4 cat:= Sprintf("& %7o    ",  G672[2]);
	L5 cat:= Sprintf("& %7o    ",  &+G672);
    end if;

    /* S8 */
    if &+S8 ne 0 then
	L1 cat:= Sprintf("& S8         ");
	L2 cat:= Sprintf("& %7o    ",  S8[1]);
	L3 cat:= Sprintf("& %7o    ",  S8[3]);
	L4 cat:= Sprintf("& %7o    ",  S8[2]);
	L5 cat:= Sprintf("& %7o    ",  &+S8);
    end if;

    /* Total */
    L2 cat:= Sprintf("& %7o\\\\\n", TotGen3);
    L3 cat:= Sprintf("& %7o\\\\\n", TotTwists);
    L4 cat:= Sprintf("& %7o\\\\\n", TotSing);
    L5 cat:= Sprintf("& %7o\\\\\n", TotGen3+TotTwists+TotSing);

    printf "%o\n%o\n%o\n%o\n%o\n", L1, L2, L3, L4, L5;

end procedure;

forward WriteFFSequence;
procedure WriteFFSequence(F, S)
    U := Universe(S);
    if IsPrimeField(U) then
	for s in S do Put(F, Sprintf("%o ", s)); end for; Puts(F, "");
    else
	for s in S do WriteFFSequence(F, Eltseq(s)); end for;
    end if;
end procedure;

forward ReadFFSequence;
function ReadFFSequence(F, FF, L)
    if IsPrimeField(FF) then
	str := Gets(F);
	if IsEof(str) then return []; end if;
	S := [FF!c : c in StringToIntegerSequence(str)];
    else
	S := [];
	for i := 1 to L do
	    Append(~S, ReadFFSequence(F, BaseField(FF), Degree(FF, BaseField(FF))));
	end for;
    end if;
    return S;
end function;

procedure WriteCurves(F, CC)

    J, IG, singular, Hs := Explode(CC);
    FF := Universe(J);

    Puts(F, Sprintf("%o", #J));
    WriteFFSequence(F, J);
    Puts(F, Sprintf("%o %o", IG[1], IG[2]));
    Puts(F, singular select "1" else "0");
    Puts(F, Sprintf("%o", #Hs));
    for H in Hs do
	if Characteristic(FF) ne 2 then
	    WriteFFSequence(F, [Coefficient(H, i) : i in [0..8]]);
	else
	    WriteFFSequence(F, [Coefficient(H[1], i) : i in [0..8]]);
	    WriteFFSequence(F, [Coefficient(H[2], i) : i in [0..8]]);
	end if;
    end for;

    Puts(F, "");
    Flush(F);

end procedure;

function ReadCurves(F, FFx)


    FF := CoefficientRing(FFx);

    str := Gets(F); if IsEof(str) then return []; end if;
    nb := StringToInteger(str);

    J := ReadFFSequence(F, FF, nb);
    str := Gets(F); IG := StringToIntegerSequence(str); IG := <IG[1], IG[2]>;
    str := Gets(F); singular := StringToInteger(str) eq 1 select true else false;
    str := Gets(F); nbH := StringToInteger(str);
    Hs := []; for i := 1 to nbH do
	if Characteristic(FF) ne 2 then
	    H := FFx!ReadFFSequence(F, FF, 9);
	    Append(~Hs, H);
	else
	    f := FFx!ReadFFSequence(F, FF, 9);
	    h := FFx!ReadFFSequence(F, FF, 9);
	    Append(~Hs, [f, h]);
	end if;
    end for;
    str := Gets(F);

    return [* J, IG, singular, Hs *];

end function;

FFEnum  := recformat< FF, p, n, q, t, x>;

function FFEnumInit(FF, t)
    FFCtxt := rec<FFEnum |
                  FF := FF,
		  p := Characteristic(FF),
                  n  := Degree(FF),
		  q := #FF,
		  t := t,
		  x := 0>;
   return FFCtxt;
end function;

procedure FFEnumNext(~V, ~FFCtxt)
    p := FFCtxt`p; q := FFCtxt`q; n := FFCtxt`n;
    x := FFCtxt`x; t := FFCtxt`t;

    X := Intseq(x+q^t, q)[1..t];
    FFCtxt`x +:= 1;
    FFCtxt`x := FFCtxt`x mod q^(t);

    V := [FFCtxt`FF!Intseq(a+p^n, p)[1..n] : a in X];

end procedure;

function EnumInit(FF)

    if Characteristic(FF) eq 2 then
	return [* 0, [], WPSEnumInit(FF, [7, 32, 40]) *]; /* Case (7) */

    elif Characteristic(FF) eq 3 then
	return WPSEnumInit(FF, [2, 4, 5, 7, 9, 12]);

    elif Characteristic(FF) eq 7 then
	return WPSEnumInit(FF, [3, 4, 5, 6, 10, 14]);

    end if;

    return WPSEnumInit(FF, [2, 3, 4, 5, 6, 7]);

end function;

procedure EnumNext(~V, ~Ctxt)

    if Type(Ctxt) eq List then FF := Ctxt[3]`FF; else FF := Ctxt`FF; end if;

    if Characteristic(FF) eq 2 then

	if Ctxt[1] in {2, 3} then
	    FFEnumNext(~V, ~(Ctxt[3]));
	else
	    WPSEnumNext(~V, ~(Ctxt[3]));
	end if;

	if #(Ctxt[2]) eq 0 then
	    Ctxt[2] := V;
	elif Ctxt[2] eq V then

	    if Ctxt[1] eq 0 then
		Ctxt[1] := 1; Ctxt[3] := WPSEnumInit(FF, [1, 3, 4, 5]); /* Case (1,5) */
		WPSEnumNext(~V, ~(Ctxt[3])); Ctxt[2] := V;

	    elif Ctxt[1] eq 1 then
		Ctxt[1] := 2; Ctxt[3] := FFEnumInit(FF, 3);    /* Case (3,3) */
		FFEnumNext(~V, ~(Ctxt[3])); Ctxt[2] := V;
		repeat FFEnumNext(~V, ~(Ctxt[3])); until V[3] ne 0;

	    elif Ctxt[1] eq 2 then
		Ctxt[1] := 3; Ctxt[3] := FFEnumInit(FF, 4); /* Case (1,1,3) */
		FFEnumNext(~V, ~(Ctxt[3])); Ctxt[2] := V;
		repeat FFEnumNext(~V, ~(Ctxt[3])); until V[4] ne 0;

	    elif Ctxt[1] eq 3 then                                      /* Case (1,1,1,1) */
		Ctxt[1] := 4; Ctxt[3] := WPSEnumInit(FF, [2, 3, 5, 6, 8, 9]);
		WPSEnumNext(~V, ~(Ctxt[3])); Ctxt[2] := V;

	    else /* Ctxt[1] eq 4 */
		Ctxt[1] := 0; Ctxt[3] := WPSEnumInit(FF, [7, 32, 40]);
		WPSEnumNext(~V, ~(Ctxt[3])); Ctxt[2] := V;

	    end if;

	end if;

	if Ctxt[1] eq 1 then /* Case (1, 5) */
	    V := [FF | 0 ] cat V;

	elif Ctxt[1] eq 2 then /* Case (3,3) */
	    V := WPSNormalize([2, 2, 2, 2], [FF | 1] cat Reverse(V));

	elif Ctxt[1] eq 3 then /* Case (1,1,3) */
	    while V[2] eq 0 do FFEnumNext(~V, ~(Ctxt[3])); end while;
	    V := WPSNormalize([2, 2, 2, 2, 2], [FF | 1] cat Reverse(V));

	end if;

    else
	WPSEnumNext(~V, ~Ctxt);
    end if;

end procedure;

/* Let's go */
"";
if reconstruct then
    printf "Enumerating curves over GF(%o)\n", p;
    InputFile := false;
    OutputFile := POpen("gzip > CurvesMod_" cat IntegerToString(p) cat ".dat.gz", "w");
elif reload then
    printf "Reading curves over GF(%o)\n", p;
    InputFile := POpen("gzip -d < CurvesMod_" cat IntegerToString(p) cat ".dat.gz", "r");
    OutputFile := false;
else
    printf "Counting curves over GF(%o)\n", p;
    InputFile := false;
    OutputFile := false;
end if;

FF := GF(p); FFx<x> := PolynomialRing(FF);

if not reload then
    WPSCtxt := EnumInit(FF);
    EnumNext(~FJI, ~WPSCtxt);
else
    FJI := 0;
end if;
FJI0 := FJI;

S8 := [0, 0, 0]; G672 := [0, 0, 0]; D12 := [0, 0, 0]; C14 := [0, 0, 0];
C2D8 := [0, 0, 0]; C2 := [0, 0, 0]; U6 := [0, 0, 0];
V8 := [0, 0, 0]; C4 := [0, 0, 0]; D4 := [0, 0, 0]; C2S4 := [0, 0, 0];
C2C4 := [0, 0, 0]; C2p3 := [0, 0, 0];

nbfree := 0; nball := 0; nbtrue := 0; nbcurve := 0; tm := Cputime();

//SetVerbose("Hyperelliptic", 2);
repeat

    nbfree +:= 1;

    if (nbfree mod 1000 eq 0) or
	(reconstruct eq true and nbfree mod 1000 eq 0) then
	PrintStats(tm, nbfree, nball, S8, G672, D12, C14, C2D8, C2, U6, V8, C4, D4, C2S4, C2C4, C2p3);
    end if;


    if reload then
	JIs := [0];
    else
	JIs := ShiodaAlgebraicInvariants(FJI : ratsolve := true);
    end if;
    nball +:= #JIs;

    for _J in JIs do

	if reconstruct then
	    J := _J;
	    singular := DiscriminantFromShiodaInvariants(J) eq 0;


	    if singular or not twists then
                if singular and Characteristic(FF) in {2, 3, 7} then continue; end if;
                H, G := HyperellipticPolynomialsFromShiodaInvariants(J);
	    else
		H, G := TwistedHyperellipticPolynomialsFromShiodaInvariants(J);
	    end if;

	    if Type(H[1]) eq BoolElt then
		printf "Error at J = %o (none curve found)\n", J;
		continue;
	    end if;

	    HJ := ShiodaInvariants(H[1]);
	    if not ShiodaInvariantsEqual(ChangeUniverse(J, Universe(HJ)), HJ) then
		printf "Error at J = %o, HJ = %o  (reconstruction)\n", J, HJ;
		continue;
	    end if;

	    if (Characteristic(FF) ne 2 and &and[ &and[c in FF : c in Eltseq(h)] : h in H] ne true) or
		(Characteristic(FF) eq 2 and &and[ &and[ &and[c in FF : c in Eltseq(q)] : q in fh]: fh in H] ne true)
		then
		printf "Error at J = %o (none rational model)\n", J;
		continue;
	    end if;

            IG := <0,0>;
            if Type(G) eq GrpPerm then IG :=  IdentifyGroup(G); end if;
	    WriteCurves(OutputFile, [* J, IG, singular, H *]);

	elif reload then

	    CC := ReadCurves(InputFile, FFx);
	    if #CC eq 0 then
		FJI := 0; nball -:= 1; nbfree -:= 1; break;
	    else
		FJI := 1;
		J, IG, singular, H := Explode(CC);
	    end if;

	else
	    J := _J; H := [0];
	    singular := DiscriminantFromShiodaInvariants(J) eq 0;

	    if singular and Characteristic(FF) in {2, 3, 7} then continue; end if;
	    G := GeometricAutomorphismGroupFromShiodaInvariants(J);
	    IG := Type(G) eq GrpPerm select IdentifyGroup(G) else <0,0>;
	end if;

	if not singular then idx := 1; else idx := 2; end if;

	case IG:
	when <0, 0>:
	    S8[idx] +:= 1;
	when <672, 1043>:
	    G672[idx] +:= 1;
	when <12, 4>:
	    D12[idx] +:= 1;
	when <14, 2>:
	    C14[idx] +:= 1;
	when <16, 11>:
	    C2D8[idx] +:= 1;
	when <2, 1>:
	    C2[idx] +:= 1;
	when <24, 5>:
	    U6[idx] +:= 1;
	when <32, 9>:
	    V8[idx] +:= 1;
	when <4, 1>:
	    C4[idx] +:= 1;
	when <4, 2>:
	    D4[idx] +:= 1;
	when <48, 48>:
	    C2S4[idx] +:= 1;
	when <8, 2>:
	    C2C4[idx] +:= 1;
	when <8, 5>:
	    C2p3[idx] +:= 1;
	end case;

	case IG:
	when <0, 0>:
	    S8[3] +:= #H-1;
	when <672, 1043>:
	    G672[3] +:= #H-1;
	when <12, 4>:
	    D12[3] +:= #H-1;
	when <14, 2>:
	    C14[3] +:= #H-1;
	when <16, 11>:
	    C2D8[3] +:= #H-1;
	when <2, 1>:
	    C2[3] +:= #H-1;
	when <24, 5>:
	    U6[3] +:= #H-1;
	when <32, 9>:
	    V8[3] +:= #H-1;
	when <4, 1>:
	    C4[3] +:= #H-1;
	when <4, 2>:
	    D4[3] +:= #H-1;
	when <48, 48>:
	    C2S4[3] +:= #H-1;
	when <8, 2>:
	    C2C4[3] +:= #H-1;
	when <8, 5>:
	    C2p3[3] +:= #H-1;
	else
	    "unknown ", G, IG;
	    quit;
	end case;

    end for;

    if not reload then
	EnumNext(~FJI, ~WPSCtxt);
    end if;

until FJI eq FJI0;

if reconstruct then
    delete OutputFile;
elif reload then
    delete InputFile;
end if;

PrintStats(tm, nbfree, nball, S8, G672, D12, C14, C2D8, C2, U6, V8, C4, D4, C2S4, C2C4, C2p3);
