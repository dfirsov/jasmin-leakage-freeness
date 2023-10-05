require import Core Int IntDiv Ring IntDiv StdOrder List Distr Real DInterval.
import Ring.IntID IntOrder.
import StdBigop Bigint BIA.

require import BitEncoding.
import BS2Int.

require import AuxLemmas.

from Jasmin require import JModel.

require export BigNum_instances.
import W64xN R.
 
op D : int distr = duniform (range 0 W64xN.modulusR).
lemma D_ll : is_lossless D. apply duniform_ll.  
 have q : 0 < W64xN.modulusR. auto. smt(@List). qed.
lemma D_uni : is_uniform D. smt(@Distr). qed.
lemma D_sup x : x \in D <=> 0 <= x < W64xN.modulusR. smt(@Distr). qed.
lemma D_mu x : x \in D => mu1 D x = Real.inv W64xN.modulusR%r. smt(@Distr). qed.
lemma M_pos : 2 < W64xN.modulusR. auto. qed.


abbrev ImplZZ x y = W64xN.valR x = y.
  

op zeroR : W64xN.R.t = W64xN.R.A.of_list W64.zero (List.nseq nlimbs W64.zero).

lemma zeroRE: W64xN.valR zeroR = 0.
rewrite /zeroR.
have nseqS'  : forall  (n : int) (x : W64.t), 0 < n => nseq n x = x :: nseq (n - 1) x. smt(nseqS).
do? (rewrite nseqS'; first by trivial). simplify.
rewrite nseq0.
by rewrite /zeroR W64xN.R.bn2seq /= W64xN.R.A.of_listK 1:/# /bn_seq.
qed.


module ASpecFp = {
  proc subn(a b: int): bool * int = {
    var c, r;
    c <- a < b;
    r <- (a - b) %% W64xN.modulusR;
    return (c, r);
  }
  proc ctseln(cond: bool, c a: int): int = {
    var r;
    r <- (if cond then a else c);
    return r;
  } 
  proc cminus(a p: int): int = {
    var r;
    r <- if a < p then a else a-p;
    return r;
  }
  proc rsample(a : int): int = {
    var r;
    r <$ duniform (range 0 a);
    return r;
  }
}.


module CSpecFp = {
 proc cminus(a p: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.subn(a, p);
  r <@ ASpecFp.ctseln(c, x, a);
  return r;
 }
 proc rsample(a:int) : int * int = {
   var x, b, i,z;
   x <- 0;
   b <- true;
   i <- 0;
   while(b){
     x <$ D;
     (b , z) <@ ASpecFp.subn(x,a);
     b <- !b;
     i <- i + 1;
   }
   return (i,x);
 }
}.



