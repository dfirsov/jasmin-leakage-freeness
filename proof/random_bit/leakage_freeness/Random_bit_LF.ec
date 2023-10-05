require import List Int AllCore Distr.
from Jasmin require import JModel.

require import AuxLemmas.
require import BigNum_LF.


require import W64_RejectionSamplingExtract_ct.
require  W64_RejectionSamplingExtract.
module XtrR = W64_RejectionSamplingExtract_ct.M(W64_RejectionSamplingExtract_ct.Syscall).
module XtrI = W64_RejectionSamplingExtract.M(W64_RejectionSamplingExtract.Syscall).

(* Direct derivation of leakage-freeness (LFdef) for random_bit function  *)
op random_bit_t : leakages_t =  LeakAddr [] ::  LeakAddr [0] :: LeakAddr [] :: LeakAddr [] :: [].

lemma random_bit_leakages start_l : 
  hoare [ M(Syscall).random_bit : M.leakages = start_l ==> M.leakages = random_bit_t ++ start_l].
proc. wp. call (_:true). rnd. skip. progress.
wp. skip. progress. 
qed.

lemma random_bit_ll : islossless M(Syscall).random_bit.
proc. inline*. wp. rnd. wp. skip.
progress. 
apply dmap_ll.
apply dmap_ll.
apply  DList.dlist_ll. smt(@W8).
qed.

lemma random_bit_leakages_ph start_l :
  phoare [ M(Syscall).random_bit : M.leakages = start_l 
            ==> M.leakages = random_bit_t ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq random_bit_ll. hoare. conseq (random_bit_leakages start_l).
qed.

op g l = if l = random_bit_t then 1%r else 0%r.

lemma random_bit_LFdef l a &m s: (glob XtrR){m} = s
 =>  let v = Pr[ XtrR.random_bit() @ &m : res = a  ] in 
     let w = Pr[ XtrR.random_bit() @ &m : XtrR.leakages = l ++ s  /\ res = a  ] in 
  0%r < w => v/w 
  = g l.
move => h1 h2 h3 h4.
have fact1 : Pr[XtrR.random_bit() @ &m : res = a /\ XtrR.leakages <> random_bit_t ++ s ] = 0%r.
 have fact' : Pr[XtrR.random_bit() @ &m : XtrR.leakages <> random_bit_t ++ s  ] = 0%r.
  byphoare (_: XtrR.leakages = s ==> _). hoare. simplify. conseq (random_bit_leakages s). auto. auto.
smt(@Distr).
have fact2 : l = random_bit_t.
 have fact2' : Pr[XtrR.random_bit() @ &m : XtrR.leakages = l ++ s /\ res = a]
  =  Pr[XtrR.random_bit() @ &m : XtrR.leakages = l ++ s /\ res = a /\ l = random_bit_t ].
  rewrite Pr[mu_split l = random_bit_t]. 
  have ->: Pr[XtrR.random_bit() @ &m :
   (XtrR.leakages = l ++ s /\ res = a) /\ l = random_bit_t]
    = Pr[XtrR.random_bit() @ &m :
   XtrR.leakages = l ++ s /\ res = a /\ l = random_bit_t]. rewrite Pr[mu_eq]. auto. auto.
  have ->: Pr[XtrR.random_bit() @ &m :
   (XtrR.leakages = l ++ s /\ res = a) /\ l <> random_bit_t] = Pr[XtrR.random_bit() @ &m :
   XtrR.leakages = l ++ s /\ res = a /\ l <> random_bit_t]. rewrite Pr[mu_eq]. auto. auto. auto.
  have ->: Pr[XtrR.random_bit() @ &m :
   XtrR.leakages = l ++ s /\ res = a /\ l <> random_bit_t] = 0%r. 
    have : Pr[XtrR.random_bit() @ &m :
   XtrR.leakages = l ++ s /\ res = a /\ l <> random_bit_t] <= Pr[XtrR.random_bit() @ &m : res = a /\ XtrR.leakages <> random_bit_t ++ s]. rewrite Pr[mu_sub]. progress. smt(@List). auto.
  smt(@Distr). simplify. auto.
  have : Pr[XtrR.random_bit() @ &m :
           XtrR.leakages = l ++ s /\ res = a /\ l = random_bit_t] 
   = Pr[XtrR.random_bit() @ &m :
           XtrR.leakages = random_bit_t ++ s /\ res = a /\ l = random_bit_t ].
  rewrite Pr[mu_eq]. progress. auto.
  progress.
  case (l = random_bit_t). auto.
   move => q.
  have falsity : Pr[XtrR.random_bit() @ &m : XtrR.leakages = l ++ s /\ res = a] = 0%r.
  rewrite fact2'. rewrite q. simplify. rewrite Pr[mu_false]. auto.
   smt().
  have : Pr[XtrR.random_bit() @ &m : res = a] = Pr[XtrR.random_bit() @ &m : XtrR.leakages = random_bit_t ++ s /\ res = a].
   rewrite Pr[mu_split XtrR.leakages = random_bit_t ++ s]. 
  have ->: Pr[XtrR.random_bit() @ &m : res = a /\ XtrR.leakages <> random_bit_t ++ s] = 0%r.
  byphoare (_: XtrR.leakages = s ==> _). hoare. simplify. conseq (random_bit_leakages s). auto. auto. auto. simplify. rewrite Pr[mu_eq]. auto. auto.
  move => pp.
  have : h2 = h3. 
  rewrite pp.  rewrite /h3. rewrite fact2. auto. smt(@Real).
qed.
          



(* pRHL derivation of LF  *)
require import LeakageFreeness_Analysis.

clone import LF_Meta as Meta
 with type pin_t <- unit, 
      type sin_t <- unit, 
      type out_t <- W8.t.

module JI = {
 proc main(x : unit * unit) : W8.t = {
  var r;
  r <@ XtrI.random_bit();
  return r;
 }
}.

module JR = {
 proc main(x : unit * unit) : W8.t = {
  var r;
  r <@ XtrR.random_bit();
  return r;
 }
 proc mainG() : W8.t * leakages_t = {
  var r;
  r <@ XtrR.random_bit();
  return (r, XtrR.leakages);
 }
}.

lemma random_bit_LF:
 equiv[  RSim(JI, JR).main ~  SimR(JI, JR).main :
  ={pin, sin, glob JR} ==> ={res, glob JR}].
proc. wp. inline*. wp. rnd. wp. rnd. wp. skip. progress.
qed.
