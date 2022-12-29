Description
--

This repository contains Magma code for reconstruction and isomorphisms of hyperelliptic curves.

This package is now included by default in Magma-v2.26.

Prerequisites
--

You need to have Magma installed on your machine to use this code.

Installation
--

You can enable the functionality of this package in Magma by attaching the `hyperelliptic/magma/spec` file with `AttachSpec`. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc` file, by adding a line like
```
AttachSpec("~/Programs/hyperelliptic/magma/spec");
```

Usage
--

Examples that test the routines in this package can be found in the directory
[`examples`](examples) (a full list of intrinsics is [here](intrinsics.md)).

Verbose comments are enabled by
```
SetVerbose("Hyperelliptic", n);
```
where `n` is either `1` or `2`. A higher value gives more comments.

Basic use of the package is as follows.

* Compute Shioda Invariants [J2, J3, J4, J5, J6, J7, J8, J9, J10] of a genus 3
  hyperelliptic curve

```
_<x> := PolynomialRing(Rationals());
H := HyperellipticCurve(x^8+x^6-x^2+x-1);
JI := ShiodaInvariants(H);
JI;
[ -29/14, 0, 158041/230496, 25/87808, 242163085/1084253184, -97577/14751744, -12622697959/330576748544, -2165139797/1942981705728, -750879849570517/62201321006039040 ];
```

* Conversely, given the first 6 free invariants J2, J3, J4, J5, J6, J7,
  compute all the possible algebraically compatible invariants J8, J9, J10
  (here, there is only one solution, the one we start from);

```
JIs := ShiodaAlgebraicInvariants(JI[1..6]);
```

* Reconstruct from these invariants a model, and the geometric automorphism
  group of the curve.

```
C, aut := HyperellipticCurveFromShiodaInvariants(JIs[1]);
```

* Check that H and C are twists.

```
ShiodaInvariantsEqual(JI, ShiodaInvariants(C));
```

Citing this code
--

Please cite the following preprint if this code has been helpful in your research:

Reynald Lercier, Jeroen Sijsling, Christophe Ritzenthaler,
*Functionalities for genus 2 and 3 curves*,
[arXiv:2102.04372](https://arxiv.org/abs/2102.04372)
