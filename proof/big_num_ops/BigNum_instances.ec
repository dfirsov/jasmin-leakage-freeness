from Jasmin require import JBigNum.

require Array3 Array32 Array64 .

abbrev nlimbs = 32.

clone BigNum as W64xN with
 op nlimbs <- nlimbs,
 theory R.A <= Array32.Array32,
 theory R2.A <= Array64.Array64,
 theory Array3 <= Array3.Array3.
