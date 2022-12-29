/***
 *  Fast enumeration of curves with non-trivial automorphism group (through
 *  parametrizations of their loci).
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
 *  Copyright 2011, R. Lercier & C. Ritzenthaler
 */

 /*

  For finite fields of increasing size, we enumerates all the Shioda
  invariants for non-trivial genus 3 hyperelliptic automorphism group thanks
  to the parametrizations given in [LeRi2011] and check that the curves
  obtained all are in disctinct isomorphism classes.


  Bibliography.

  [LeRi2011] "Hyperelliptic curves and their invariants: geometric, arithmetic
  and algorithmic aspects", 2011, preprint.

 */

 AttachSpec("../magma/spec");

 p := 7;
 repeat
     p +:= 1;

     ret, pp := IsPrimePower(p);
     if not ret or pp lt 11 then continue; end if;

     ""; "";
     "*** Working modulo p =", p;

     FF := GF(p); _<x> := PolynomialRing(FF);


     /*
     * C2xD8
     *
     ****************/

     "";
     "C2xD8 enumeration";
     "------------------";
     p-3, "curves to be found";;

     LST := [];
     for t in FF do
         if t in [FF!-1/72, FF!2/3] then continue; end if; /* Disc = 0 */
         if t eq 0 then continue; end if; /* C2xS4 */

         f := x^8 + 7/6*x^4 + 1/2*t + 1/144;
         JI := ShiodaInvariants(f : normalize := true);
         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <16, 11> then
             "ARGHH... at JI =", JI;
         end if;

         Append(~LST, JI);

     end for;

     #LST, "curves found";
     if #Seqset(LST) ne p-3 or #Seqset(LST) ne #LST then
         "ARGHHHHH....";
         break;
     end if;


     /*
     * D12
     *
     ****************/

     "";
     "D12 enumeration";
     "------------------";
     p-3, "curves to be found";;

     LST := [];

     for t in FF do
         if t in [FF!-1/486, FF!-1/192] then continue; end if; /* Disc = 0 */
         if t eq 0 then continue; end if; /* C2xS4 */

         f := x^7 - 7/9*x^4 + (-48*t - 8/81)*x;
         JI := ShiodaInvariants(f : normalize := true);
         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <12, 4> then
             "ARGHH... at JI =", JI;
         end if;

         Append(~LST, JI);

     end for;

     #LST, "curves found";
     if #Seqset(LST) ne p-3 or #Seqset(LST) ne #LST then
         "ARGHHHHH....";
         break;
     end if;


     /*
     * C2xC4
     *
     ****************/

     "";
     "C2xC4 enumeration";
     "------------------";
     p-3, "curves to be found";;

     LST := [];

     for t in FF do
         if t in [FF!21/5, FF!168/5] then continue; end if; /* Disc = 0 */
         if t eq 24/5 then continue; end if; /* C2xS4 */

         f := (x^4+2*x^2+5/147*t-1/7)*(x^4-5/147*t+1/7);
         JI := ShiodaInvariants(f : normalize := true);
         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <8, 2> then
             "ARGHH... at t=", t, "JI =", JI;
         end if;

         Append(~LST, JI);

     end for;

     #LST, "curves found";
     if #Seqset(LST) ne p-3 or #Seqset(LST) ne #LST then
         "ARGHHHHH....";
         break;
     end if;



     /*
     * C4
     *
     ****************/

     "";
     "C4 enumeration";
     "--------------";

     (p-1)^2+1, "curves to be found";;

     LST := [];
     for u in FF do
         for t in FF do

             if t eq 0 then continue; end if;

             JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
                 [t, 0, 1/96*(t+1)*t^2, 0, 3*u^3+(63/80*t-5/16)*u^2+(-1/124416000*(-25+63*t)*(-90720*t+36000)+47/6400*t^2-7/384*t+25/6912-1/64*t^3)*u-1/124416000*(-25+63*t)*(-1269
             *t^2+3150*t-625+2700*t^3), 0, 8/3*u^4+(2/3*t-10/27)*u^3+(139/3600*t^2+25/1296-1/360*t^3-5/72*t)*u^2+(-17/14400*t^4+241/432000*t^3+25/10368*t-125/279936-139/51840*
             t^2)*u-125/4478976*t-9707/145152000*t^5+139/2985984*t^2-299/18662400*t^3+82091/967680000*t^4+625/161243136-1/483840*t^6, 0, -5/3*u^5+(-31/48*t+125/432)*u^4+(-23/
             3360*t^3+155/1728*t-625/31104-3349/40320*t^2)*u^3+(3349/387072*t^2+3125/4478976-775/165888*t-94723/29030400*t^3-1/345600*t^4)*u^2+(-15625/1289945088+86893/
             580608000*t^5-16745/55738368*t^2+61/3870720*t^6+105073/418037760*t^3+3875/35831808*t-735179/13934592000*t^4)*u+15625/185752092672+736579/401316249600*t^4+83725/
             24078974976*t^2-23681183/3344302080000*t^5-108523/24078974976*t^3-19375/20639121408*t+734581/139345920000*t^6+1/44236800*t^7]
             );

             if DiscriminantFromShiodaInvariants(JI) eq 0 then continue;  end if;

             G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
             if IdentifyGroup(G) ne <4, 1> then
                 //	"ARGHH... at u,t=", u, t, "JI =", JI;IdentifyGroup(G);
                 continue;
             end if;

             Append(~LST, JI);

         end for;
     end for;

     /* Case J4 = 1/96 */
     for t in FF do

         if t eq 0 then continue; end if;

         JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
             [
             t,
             0,
             t^2/96,
             0,
             (154993*t^3 + 14448*t^2 + 426*t + 4)/(7776000),
             0,
             (80060695*t^4 + 11513824*t^3 + 613284*t^2 + 13888*t + 112)/(44089920000),
             0,
             (-905961157*t^5 - 150709664*t^4 - 9796132*t^3 - 308716*t^2 - 4718*t - 28)/(3174474240000)
             ]
             );

         if DiscriminantFromShiodaInvariants(JI) eq 0 then
             continue;
         end if;

         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <4, 1> then
             //	"ARGHH... at t=", t, "JI =", JI;IdentifyGroup(G);
             continue;
         end if;

         Append(~LST, JI);

     end for;

     /* Case J2=0, J6=J4 */
     for t in FF do

         JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
             [
             0,
             0,
             4/3969*(t-9)*(11*t+6),
             0,
             4/3969*(t+1)*(11*t+6)^2,
             0,
             32/36756909*(373*t^2+440*t+127)*(11*t+6)^2,
             0,
             -8/992436543*(835*t^2+646*t+51)*(11*t+6)^3
             ]
             );

         if DiscriminantFromShiodaInvariants(JI) eq 0 then
             continue;
         end if;

         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <4, 1> then
             //	"ARGHH... at t=", t, "JI =", JI;IdentifyGroup(G);
             continue;
         end if;

         Append(~LST, JI);

     end for;



     /* Isolated points */
     JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
         [FF!x : x in [1, 0, 1/96, 0, 154993/7776000, 0, 16012139/8817984000, 0,-905961157/3174474240000]]);
     G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
     if IdentifyGroup(G) eq <4, 1> and DiscriminantFromShiodaInvariants(JI) ne 0 then
         Append(~LST, WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10], JI));
     end if;

     if not pp in {11} then

         JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
             [FF!x : x in [0, 0, 4/43659, 0, 4/43659, 0, 11936/4447585989, 0, -6680/120084821703]]);
         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) eq <4, 1> and DiscriminantFromShiodaInvariants(JI) ne 0 then
             Append(~LST, WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10], JI));
         end if;
     end if;


     #LST, "curves found";
     if #Seqset(LST) ne (p-1)^2+1 or #Seqset(LST) ne #LST then
         "ARGHHHHH....";
         break;
     end if;


     /*
     * C2^3
     *
     ****************/

     "";
     "C2^3 enumeration";
     "-----------------";

     (p-1)^2+1, "curves to be found";;

     LST := [];
     TR := [];
     for t in FF do
         for u in FF do

             if t eq 0 then continue; end if;

             JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
                 [
                 t,
                 t,
                 -9800*u^4+85*t*u^2-35/3*t*u+2/147*t^2,
             -137200*u^5+700*t*u^3+350/3*t*u^2-25/28*t^2*u+1/28*t^2,
             -617400*u^6+2030*t*u^4+1470*t*u^3-689/56*t^2*u^2+11/12*t^2*u-1/24*t^2+2/3087*t^3,
             -1920800*u^7-72520/3*t*u^5+43120/3*t*u^4+377/6*t^2*u^3-226/9*t^2*u^2+1/588*t^2*(17*t+686)*u-1/588*t^3,
             -2469600*u^8-125300/3*t*u^6+37240/3*t*u^5-643/14*t^2*u^4+1432/9*t^2*u^3-1/246960*t^2*(4705960+120087*t)*u^2+1411/17640*t^3*u-11/252105*t^4-1/1680*t^3,
             302526000*u^9-12022150/3*t*u^7-325850/3*t*u^6+665105/36*t^2*u^5-9905/18*t^2*u^4-1/2016*t^2*(-397880+56341*t)*u^3+18829/6048*t^3*u^2+1/98784*t^3*(472*t-30527)*u+1/96*t^3-1/4116*t^4,
             1162084000*u^10-11872700*t*u^8-7991900/3*t*u^7+1366535/18*t^2*u^6-51835/9*t^2*u^5-1/2352*t^2*(-13267240+268943*t)*u^4-77657/3024*t^3*u^3+1/1037232*t^3*(67571+105696*t)*u^2-1/148176*t^3*(824*t-1029)*u-11/5294205*t^5+1/6174*t^4
             ]
                 );

             if DiscriminantFromShiodaInvariants(JI) eq 0 then
                 continue;
             end if;

             G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
             if IdentifyGroup(G) ne <8, 5> then
                 //	"ARGHH... at t, u=", t, u, "JI =", JI;IdentifyGroup(G);
                 continue;
             end if;

             Append(~LST, JI);
             Append(~TR, [* JI, [u, t] *]);

         end for;
     end for;

     /* Case J2=0, J4=J3 */
     for t in FF do

         if t eq -105/1260 then continue; end if;

         JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
             [
             0,
             1260*t+105,
             7350*t,
             36750*t+7350,
             -66150*t^2-242550*t-29400,
             -926100*t^2+977550*t+102900,
             -7563150*t^2-1749300*t-102900,
             20837250*t^3-33957000*t^2-8232000*t-1029000,
             -6945750*t^3+557975250*t^2+119364000*t+7203000
             ]
             );

         if DiscriminantFromShiodaInvariants(JI) eq 0 then
             continue;
         end if;

         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <8, 5> then
             //	"ARGHH... at t=", t, "JI =", JI;IdentifyGroup(G);
             continue;
         end if;

         Append(~LST, JI);

     end for;


     /* Case J3=0, J5=J2^2 */
     for t in FF do

         if pp eq 101 then
             JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
                 [32*(t+44)*(t+12),
                 0,
                 57*(t^2+84*t+59)*(t+12)^2,
                 14*(t+12)^3*(t+84)^2,
                 22*(t+62)*(t+12)^3*(t+22)*(t^2+73*t+23)*(t+54)/(2*t^2+45*t+46),
             97/51*(t+12)^4*(t^2+7*t+86)*(t+84),
                 81*(t+12)^4*(t^2+51*t+54)*(t^2+73*t+23)*(t^2+64*t+62)/(2*t^2+45*t+46),
             2/51*(t+12)^5*(t^2+3*t+19)*(t+73)*(t+84),
                 3*(t^2+3*t+75)*(t^2+26*t+79)*(t+12)^5*(t^2+73*t+23)*(t+68)/(2*t^2+45*t+46)]
             );
         else

             JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
                 [
                 1010/3*(52*t+59)*(t+1),
                 0,
                 50/27*(52*t+59)^2*(11272*t^2+23147*t+11767),
                 25/9*(52*t+59)^3*(17*t+29)^2,
                 -25/486*(52*t+59)^3*(27670948*t^3+88650255*t^2+94796346*t+33852031),
                 50/81*(52*t+59)^4*(17*t+29)*(38117*t^2+81691*t+43682),
                 -25/3402*(52*t+59)^4*(6266813468*t^4+26795826605*t^3+42971724291*t^2+30632960351*t+8190389165),
                 -125/2916*(52*t+59)^5*(17*t+29)*(11612756*t^3+34093287*t^2+33246138*t+10800599),
                 125/30618*(52*t+59)^5*(794827443664*t^5+4302413461544*t^4+9310923963145*t^3+10069939679311*t^2+5442845374787*t+1176260576869)
                 ]
                 );
         end if;

         if DiscriminantFromShiodaInvariants(JI) eq 0 then
             continue;
         end if;

         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) ne <8, 5> then
             //	"ARGHH... at t=", t, "JI =", JI;IdentifyGroup(G);
             continue;
         end if;

         Append(~LST, JI);

     end for;

     if pp eq 101 then

         JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
             [FF!x : x in [32, 0, 57, 14, 11, 93, 91, 4, 52]]
             );

         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) eq <8, 5> and DiscriminantFromShiodaInvariants(JI) ne 0 then
             Append(~LST,JI);
         end if;
     end if;

     if not pp in {13, 17, 101} then
         JI := WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10],
             [FF!x : x in [ 1010/39, 0, 563600/4563, 14450/1521, -345886850/533871, 64798900/177957, -78335168350/48582261, -12338553250/20820969, 49676715229000/5684124537 ]]
             );

         G :=  GeometricAutomorphismGroupFromShiodaInvariants(JI);
         if IdentifyGroup(G) eq <8, 5> and DiscriminantFromShiodaInvariants(JI) ne 0 then
             Append(~LST,JI);
         end if;

     end if;

     #LST, "curves found";
     if #Seqset(LST) ne (p-1)^2+1 or #Seqset(LST) ne #LST then
         "ARGHHHHH....";
         break;
     end if;

     "";
     "***";

 until p gt 50;

 quit;
