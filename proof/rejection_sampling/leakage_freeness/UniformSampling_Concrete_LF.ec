require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import UniformSampling_Concrete_LeakagesFun.


(* We prove that Jasmin's uniform sampling function bn_rsample is leakage-free (LFdef)  *)

require import W64_RejectionSamplingExtract_ct.
module XtrR = W64_RejectionSamplingExtract_ct.M(W64_RejectionSamplingExtract_ct.Syscall).



lemma rsample_leakages2 a s  &m : (glob XtrR){m} = s =>
  Pr[ XtrR.bn_rsample_i(a) @ &m : XtrR.leakages <> samp_t res.`1 ++ s ] = 0%r.
move => q.
byphoare (_: glob XtrR = s ==> _).
hoare. simplify.
conseq (rsample_leakages s). auto. 
progress. 
qed.

(* samp_t_correct *)
lemma samp_t_correct a l x s &m : (glob XtrR){m} = s =>
  Pr[ XtrR.bn_rsample_i(a) @ &m : XtrR.leakages = l ++ s  /\ res.`2 = x ]
  = Pr[ XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x  ].


move => H.
have ->: Pr[ XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x ]
 = Pr[ XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ XtrR.leakages = samp_t res.`1  ++ s ].
  have -> : Pr[XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x]
   = Pr[XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ XtrR.leakages = samp_t res.`1 ++ s]
   + Pr[XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ XtrR.leakages <> samp_t res.`1 ++ s].
   rewrite Pr[mu_split (XtrR.leakages = samp_t res.`1 ++ s)] -!andbA /#.
  have ->: Pr[XtrR.bn_rsample_i(a) @ &m :
   l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ XtrR.leakages <> samp_t res.`1 ++ s] = 0%r.
    have : Pr[XtrR.bn_rsample_i(a) @ &m :
       l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ XtrR.leakages <> samp_t res.`1 ++ s]
     <= Pr[ XtrR.bn_rsample_i(a) @ &m : XtrR.leakages <> samp_t res.`1 ++ s ]. smt(@Distr).
    rewrite (rsample_leakages2 a s &m). auto. smt(@Distr). 
auto.
have -> : Pr[ XtrR.bn_rsample_i(a) @ &m : l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ XtrR.leakages = samp_t res.`1 ++ s  ]
 = Pr[ XtrR.bn_rsample_i(a) @ &m : res.`2 = x /\  l ++ s = XtrR.leakages /\ XtrR.leakages = samp_t res.`1 ++ s  ].
rewrite Pr[mu_eq]. move => &hr. split.  smt().  smt(). auto.
have -> : Pr[ XtrR.bn_rsample_i(a) @ &m : res.`2 = x /\ l ++ s = XtrR.leakages /\ XtrR.leakages = samp_t res.`1 ++ s  ]
 = Pr[ XtrR.bn_rsample_i(a) @ &m :  l ++ s = XtrR.leakages /\ res.`2 = x ].
  have : Pr[ XtrR.bn_rsample_i(a) @ &m :  l ++ s = XtrR.leakages /\ res.`2 = x ] 
   = Pr[ XtrR.bn_rsample_i(a) @ &m :  l ++ s = XtrR.leakages /\ res.`2 = x /\ XtrR.leakages = samp_t res.`1 ++ s  ]
   + Pr[ XtrR.bn_rsample_i(a) @ &m :  l ++ s = XtrR.leakages /\ res.`2 = x /\ XtrR.leakages <> samp_t res.`1 ++ s  ].
 rewrite Pr[mu_split (XtrR.leakages = samp_t res.`1 ++ s )] -!andbA /#.
   have : Pr[ XtrR.bn_rsample_i(a) @ &m :  l ++ s = XtrR.leakages /\ res.`2 = x /\ XtrR.leakages <> samp_t res.`1 ++ s  ]
    = 0%r.
     have : Pr[ XtrR.bn_rsample_i(a) @ &m :  l ++ s = XtrR.leakages /\ res.`2 = x /\ XtrR.leakages <> samp_t res.`1 ++ s  ] 
         <= Pr[ XtrR.bn_rsample_i(a) @ &m : XtrR.leakages <> samp_t res.`1 ++ s ].
       rewrite Pr[mu_sub]. auto. auto.
    rewrite (rsample_leakages2 a s &m). auto. smt(@Distr).
    move => h. rewrite h. simplify. progress. rewrite H0.
rewrite Pr[mu_eq]. smt(). auto. 
rewrite Pr[mu_eq]. smt(). auto.
qed.


(* rsample_leakf *)
lemma bn_rsample_leakf a s x l &m : (glob XtrR){m} = s
 => Pr[ XtrR.bn_rsample_i(a) @ &m : XtrR.leakages = l ++ s /\ res.`2 = x  ]
  = Pr[ XtrR.bn_rsample_i(a) @ &m :  (inv (-1) samp_t) l = res.`1  /\ res.`2 = x  ].
move => ic (* ic' *). rewrite  (samp_t_correct a l x s &m). auto. auto.
simplify. 
have -> : 
  Pr[XtrR.bn_rsample_i(a) @ &m :
   l ++ s = samp_t res.`1 ++ s /\ res.`2 = x]
  =   Pr[XtrR.bn_rsample_i(a) @ &m :
   l ++ s = samp_t res.`1 ++ s /\ res.`2 = x /\ 0 <= res.`1]. byequiv.
proc. wp. simplify. 
while (0 <= i{1} /\ ={i,byte_p, byte_z}). wp.  simplify.
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
skip. progress. smt(). wp. 
call (_:true). wp. sim. wp.  skip. progress.
auto. auto.
have -> : Pr[XtrR.bn_rsample_i(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x] 
 = Pr[XtrR.bn_rsample_i(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x /\ 0 <= res.`1].
 byequiv.
proc. wp. simplify.
while (0 <= i{1} /\ ={i,byte_p, byte_z}). wp.  simplify.
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
skip. progress. smt(). wp. 
call (_:true). wp. sim. wp.  skip. progress.
auto. auto.
rewrite Pr[mu_eq].
progress.
have -> : l = samp_t res{hr}.`1. smt(@List).
rewrite invP. apply samp_t_inj. auto.
have : exists z, (samp_t z) = l.
apply (choiceEx (-1) samp_t l res{hr}.`1) . apply H. smt().
elim. progress.
rewrite - H.
rewrite invP.
apply samp_t_inj. auto.
auto.
qed.


require import W64_RejectionSamplingExtract.
module M2 = W64_RejectionSamplingExtract.M(W64_RejectionSamplingExtract.Syscall).  

lemma XtrR_M2_rsample :
  equiv  [ XtrR.bn_rsample_i ~ M2.bn_rsample_i
    : ={arg} ==> ={res}  ].
proof. proc.  sim. 
call (_:true). 
wp. while (={a,i}). wp.  skip. progress. wp. skip. progress.
wp.  skip. progress. qed.


require import BigNum_proofs.
require import BigNum_spec.
require import UniformSampling_Abstract.
require import UniformSampling_Concrete.



equiv rsample_cspec_equiv:
 XtrR.bn_rsample_i ~ CSpecFp.rsample:
  W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
transitivity M2.bn_rsample_i
 (={arg} ==> ={res})
 (W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
progress. smt(). progress.
conseq XtrR_M2_rsample. 
conseq rsample_cspec.
qed.


lemma rsample_cspec_pr a i x &m : 
  Pr[ XtrR.bn_rsample_i(a) @ &m : res = (i,x)  ]
   = Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res = (i, W64xN.valR x)  ].
byequiv.
conseq rsample_cspec_equiv. progress. progress. smt().
smt(@W64xN). auto. auto.
qed.

lemma bn_rsample_pr a i x &m : 
  1 <= i => RSP (W64xN.valR a) (W64xN.valR x) =>
  Pr[ XtrR.bn_rsample_i(a) @ &m : res = (i,x) ]
   = mu D (predC (RSP (W64xN.valR a))) ^ (i - 1) * mu1 D (W64xN.valR x).
rewrite rsample_cspec_pr.
apply rsample_pr. 
qed.

lemma rsample_index_pos &m a : Pr[XtrR.bn_rsample_i(a) @ &m : res.`1 <= 0 ] = 0%r.
byphoare (_: arg = a ==> _);auto. hoare.
proc.  simplify.
unroll 19. rcondt 19. wp. wp. 
call (_:true). wp. auto. wp. skip. auto.
while (0 < i). wp. call (_:true). auto. wp.  call (_:true). auto.  wp. 
inline*. wp. rnd. wp. skip. progress. smt().
wp. call (_:true). auto.  wp.  
call (_:true). auto. wp. 
call (_:true). auto. wp. 
call (_:true). auto. wp. skip. smt().
qed.

import W64xN.


op g a l : real 
 = if inv (-1) samp_t l <= 0 then 0%r else 
     mu D (predC (RSP (valR a))) ^ (inv (-1) samp_t l - 1)
       * (1%r / W64xN.modulusR%r).


        
lemma bn_rsample_v &m x a l s: (glob XtrR){m} = s
  => Pr[ XtrR.bn_rsample_i(a) @ &m : XtrR.leakages = l ++ s  /\ res.`2 = x  ] 
       = if (valR a <= valR x) then 0%r else (g a l).
 move => p.
   rewrite  (bn_rsample_leakf a s x l &m);auto.
case (inv (-1) samp_t l <= 0). 
move => q. rewrite /g. rewrite q.  simplify. 
  have : Pr[XtrR.bn_rsample_i(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x] 
    <= Pr[XtrR.bn_rsample_i(a) @ &m : res.`1 <= 0 ]. simplify. rewrite Pr[mu_sub]. smt().
   auto. smt(rsample_index_pos @Distr).
move => q.
have -> : 
 Pr[XtrR.bn_rsample_i(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x]
  = Pr[XtrR.bn_rsample_i(a) @ &m :
   res = (inv (-1) samp_t l , x) ]. rewrite Pr[mu_eq]. smt(). auto.
case (valR x < valR a) => case1.
rewrite rsample_cspec_pr.
rewrite rsample_pr.   smt().
rewrite /RSP. auto.
rewrite /z. 
have ->: mu1 D (W64xN.valR x) = 1%r / W64xN.modulusR%r.
rewrite duniform1E_uniq. smt(@List).
 have f1 : 0 <= W64xN.valR x < W64xN.modulusR. smt(@W64xN).  smt(@Distr @List). 
rewrite /g.   smt().
have : Pr[W64_RejectionSamplingExtract_ct.M(W64_RejectionSamplingExtract_ct.Syscall).bn_rsample_i(a) @ &m :
   res.`2 = x] = 0%r.
  have -> : Pr[W64_RejectionSamplingExtract_ct.M(W64_RejectionSamplingExtract_ct.Syscall).bn_rsample_i(a) @ &m :
     res.`2 =  x] = Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. progress. rewrite H.  auto.  smt(@W64xN). auto. auto.
  apply rsample_pr_out. auto.
smt(@Distr).
qed.

op h a : real = 1%r/(valR a)%r. 

lemma bn_rsample_w &m x a: 
 Pr[ XtrR.bn_rsample_i(a) @ &m : res.`2 = x ] 
  = if (valR a <= valR x) then 0%r else h a.    
proof. 
 have ->: Pr[ XtrR.bn_rsample_i(a) @ &m : res.`2 = x ] =
  Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. 
progress. rewrite - H. auto. smt(@W64xN). auto. auto.
rewrite /h.
case: (valR a <= valR x). move => alx.
rewrite rsample_pr_out. smt(). auto.
move => a_less_x.
rewrite rsample_uni. smt(@W64xN).
smt(@W64xN). smt(). auto.
qed.

op rsample_f a l = h a / g a l.

lemma bn_rsample_leakfree_i pin l a &m s: (glob XtrR){m} = s 
 =>  let v = Pr[ XtrR.bn_rsample_i(pin) @ &m : res.`2 = a  ] in 
     let w = Pr[ XtrR.bn_rsample_i(pin) @ &m : XtrR.leakages = l ++ s  /\ res.`2 = a  ] in 
  0%r < w => v/w 
  = rsample_f pin l.
move => l_empty v w f1.
have : (valR a < valR pin).
 case (valR pin <= valR a) => h.
 have : w <= 0%r.
 rewrite /w.  
 rewrite (bn_rsample_v &m a pin  l _). auto.
 rewrite h. auto.
 smt(). 
 smt().
move => a_less_pin.
rewrite /f.
rewrite  (bn_rsample_v &m a pin l s _). auto.
rewrite  (bn_rsample_w &m a pin ). auto. 
smt().
qed.


lemma bn_rsample_leakfree pin l a &m s: (glob XtrR){m} = s
 =>  let v = Pr[ XtrR.bn_rsample(pin) @ &m : res = a  ] in 
     let w = Pr[ XtrR.bn_rsample(pin) @ &m : XtrR.leakages = l ++ s  /\ res = a  ] in 
  0%r < w => v/w 
  = rsample_f pin l.
proof. 
 have <-: Pr[ XtrR.bn_rsample_i(pin) @ &m : res.`2 = a  ] = Pr[ XtrR.bn_rsample(pin) @ &m : res = a  ].
  byequiv (_: ={arg, glob XtrR} ==> res.`2{1} = res{2}). proc. simplify. sim. auto. auto.
 have <-: Pr[ XtrR.bn_rsample_i(pin) @ &m : XtrR.leakages = l ++ s /\ res.`2 = a  ] = Pr[ XtrR.bn_rsample(pin) @ &m : XtrR.leakages = l ++ s /\ res = a  ].
  byequiv (_: ={arg, glob XtrR} ==> res.`2{1} = res{2} /\ ={XtrR.leakages}). proc. simplify. sim. auto. auto.
move => H.
apply (bn_rsample_leakfree_i pin l a &m s H  ). 
qed.

