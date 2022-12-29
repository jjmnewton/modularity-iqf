//////// Hyperelliptic case

NormalizedM := function(M)
  N := Nrows(M);
  for j in [1 .. N] do
    for i in [1 .. N] do
      if M[i,j] ne 0 then
        return 1/M[i,j]*M;
      end if;
    end for;
  end for;
  printf("Error, your matrix is zero");
  return 0;
end function;

P<x>:=PolynomialRing(GF(7));
f:=x^8+1;
//f:=x^8+14*x^4+1;
//f:=x^7-1;
//f:=x*(x^6-1);
f:=x^12-1;
//f:=x^5-x;
//f:= x^6 + x^3 + 3;
C:=HyperellipticCurve(f);
g:=Genus(C);
T1:=Twists(C);

#T1;
[[[i,j] : j in [i+1..#T1], i in [1..#T1-1] | IsIsomorphicHyperellipticCurves(T1[i],T1[j])]];

// part to be integrated
_,Aut:=IsGL2EquivalentExtended(f,f,2*g+2 : geometric := true, commonfield := true);
Aut:=[* NormalizedM(M) : M in Aut *];
e:=Lcm([Degree(BaseRing(M)) : M in Aut]);
p:=Characteristic(BaseRing(Aut[1]));
F:=GF(p^e);
for M in Aut do Embed(BaseRing(M),F); end for;
Aut:=[ChangeRing(M,GF(p^e)) : M in Aut];
#Aut;

T1:=Twists(C,Aut) ;
#T1;
[[[i,j] : j in [i+1..#T1], i in [1..#T1-1] | IsIsomorphicHyperellipticCurves(T1[i],T1[j])]];

/* for g<4
T2:=Twists(C);
#T1 eq #T2;
*/


/*
p:=3;
Maxi:=[];
g:=2;
while p le 30 do
        print "p",p;
      F:=GF(p);
      L:=[];
      for JL in CartesianPower(F,3) do
          H:=HyperellipticCurveFromG2Invariants([JL[1],JL[2],JL[3]]);
          HL:=Twists(H);
          f:=HyperellipticPolynomials(H);
          _,Aut:=IsGL2EquivalentExtended(f,f,2*g+2 : geometric := true, commonfield := true);
                Aut:=[* NormalizedM(M) : M in Aut *];
        e:=Lcm([Degree(BaseRing(M)) : M in Aut]);
        p:=Characteristic(BaseRing(Aut[1]));
        F2:=GF(p^e);
        for M in Aut do Embed(BaseRing(M),F2); end for;
        Aut:=[ChangeRing(M,GF(p^e)) : M in Aut];
        T1:=Twists(H,Aut) ;
        if #T1 ne #HL then print H,#T1,#HL,#Aut,
                [[[i,j] : j in [i+1..#T1], i in [1..#T1-1] | IsIsomorphic(T1[i],T1[j])]]; end if;
        end for;
        p:=NextPrime(p);
end while;

p:=13;
reconstruct:=true; twists:=true;
load "hg3enum.m";

p:=13;
g:=3;
FF:=GF(p);
WPSCtxt := EnumInit(FF);
EnumNext(~FJI, ~WPSCtxt);
FJI0 := FJI;

repeat
        EnumNext(~FJI, ~WPSCtxt);
        J := ShiodaAlgebraicInvariants(FJI : ratsolve := true);
        for j in J do
                singular := DiscriminantFromShiodaInvariants(j) eq 0;
                if singular eq false then
                        H:=HyperellipticCurveFromShiodaInvariants(j);
                        HL:=TwistedHyperellipticPolynomialsFromShiodaInvariants(j);
                        f:=HyperellipticPolynomials(H);
                        print f;
                        _,Aut:=IsGL2EquivalentExtended(f,f,2*g+2 : geometric := true, commonfield := true);
                        Aut:=[* NormalizedM(M) : M in Aut *];
                        e:=Lcm([Degree(BaseRing(M)) : M in Aut]);
                        p:=Characteristic(BaseRing(Aut[1]));
                        F2:=GF(p^e);
                        for M in Aut do Embed(BaseRing(M),F2); end for;
                        Aut:=[ChangeRing(M,GF(p^e)) : M in Aut];
                        T1:=Twists(H,Aut) ;
                        if #T1 ne #HL then print H,#T1,#HL,#Aut,
                                [[[i,j] : j in [i+1..#T1], i in [1..#T1-1] | IsIsomorphic(T1[i],T1[j])]]; end if;
                end if;
        end for;
until FJI eq FJI0;

P<u>:=PolynomialRing(GF(p));
f1:=4*u^7 + 8*u^6 + 10*u^5 + 4*u^3 + 5*u^2 + 9*u;
f2:=3*u^8 + 4*u^7 + 10*u^6 + u^5 + u^4 + u^3 + 8*u^2 + 7*u + 3;
*/
