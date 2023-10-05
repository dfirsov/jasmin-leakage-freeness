require import AllCore IntDiv CoreMap Distr List RealExp.
import StdBigop Bigint BIA.

from Jasmin require import JModel.

require W64_RejectionSamplingExtract.
require import Array1 Array32 Array256.
require import WArray1 WArray256.

require UniformSampling_LF.


(* Instantiation of the BN Framework for 32 limbs *)
clone import UniformSampling_LF as UniformSampling_Concrete_LF
 with op nlimbs <- 32,
      theory BN_base.BN.A <- Array32,
      theory BN_base.Aw8 <- Array256,
      theory BN_base.Abytes <- WArray256
      proof gt0_nlimbs by done.

import BN_base.BN.

(** Extraction of Jasmin code (without leakage) *)
module M = W64_RejectionSamplingExtract.M(W64_RejectionSamplingExtract.Syscall).

(** Lift of general correctness results *)
equiv bn_set0_eq:
 M.bn_set0 ~ BN_base.XtrI.bn_set0 : ={arg} ==> ={res}
by sim.

phoare bn_set0_ph:
 [ M.bn_set0 : true ==> bn res = 0 ] = 1%r
by conseq bn_set0_eq BN_base.bn_set0_ph => /#.

equiv bn_copy_eq:
 M.bn_copy ~ BN_base.XtrI.bn_copy : ={arg} ==> ={res}
by sim.

phoare bn_copy_ph x:
 [ M.bn_copy : arg=x ==> res = x ] = 1%r
by conseq bn_copy_eq (BN_base.bn_copy_ph x) => /#.

equiv bn_subc_eq:
 M.bn_subc ~ BN_base.XtrI.bn_subc : ={arg} ==> ={res}
by sim.

phoare bn_subc_ph _a _b:
 [ M.bn_subc :
   a=_a /\ b=_b 
   ==> bn_withborrow res = bn _a - bn _b] = 1%r
by conseq bn_subc_eq (BN_base.bn_subc_ph _a _b) => /#.

equiv bn_lt_eq:
 M.bn_lt_cf ~ BN_base.XtrI.bn_lt_cf : ={arg} ==> ={res}
by sim.

phoare bn_lt_ph _a _b:
 [ M.bn_lt_cf :
   a=_a /\ b=_b 
   ==> res = bn _a < bn _b] = 1%r
by conseq bn_lt_eq (BN_base.bn_lt_cf_ph _a _b) => /#.

equiv bn_rnd_eq:
 M.bn_rnd ~ BN_base.XtrI.bn_rnd: ={arg} ==> ={res}
by sim.

phoare bn_rnd_ph _res:
 [ M.bn_rnd :
   true ==> res = _res ] = (mu1 bn_rnd _res)
by conseq bn_rnd_eq (BN_base.bn_rnd_ph _res) => /#.

equiv bn_rsample1_eq:
 M.bn_rsample1 ~ BN_base.XtrI.bn_rsample1: ={arg} ==> ={res}
by sim.

phoare bn_rsample1_ph _bnd _res:
 [ M.bn_rsample1 :
   bnd=_bnd ==> res = _res ] = (mu1 (bn_rnd_bnd bnd) _res)
by conseq bn_rsample1_eq (BN_base.bn_rsample1_ph _bnd _res) => /#.

(** Extraction of Jasmin code (with leakage) *)
require W64_RejectionSamplingExtract_ct.
module Mct = W64_RejectionSamplingExtract_ct.M(W64_RejectionSamplingExtract_ct.Syscall).

(** correspondence to generic (parametric) code *)
equiv bn_set0_cteq:
 Mct.bn_set0 ~ BN_base.XtrR.bn_set0 : ={arg} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
 ==> ={res} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
by sim.

equiv bn_subc_cteq:
 Mct.bn_subc ~ BN_base.XtrR.bn_subc : ={arg} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
 ==> ={res} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
by sim.

equiv bn_lt_cteq:
 Mct.bn_lt_cf ~ BN_base.XtrR.bn_lt_cf : ={arg}  /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
 ==> ={res} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
by sim.

equiv bn_rnd_cteq:
 Mct.bn_rnd ~ BN_base.XtrR.bn_rnd : Mct.leakages{1}=BN_base.XtrR.leakages{2}
 ==> ={res} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
by proc; inline*; sim.

equiv bn_rsample1_cteq:
 Mct.bn_rsample1 ~ BN_base.XtrR.bn_rsample1
 : ={bnd} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}
 ==> ={res} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}.
proc.
while(={a,cf,bnd} /\ Mct.leakages{1}=BN_base.XtrR.leakages{2}).
 wp; call bn_lt_cteq.
 wp; call bn_rnd_cteq.
 by auto => />.
wp; call bn_lt_cteq.
wp; call bn_rnd_cteq.
by auto => />.
qed.

(* *
   *  Leakage-Freeness for 32-limb 'rsample1'
   *                                                     *)


(** The right-hand side of the LF equivalence            *)
module SimR = {
 proc main(a a' bnd: W64.t Array32.t): W64.t Array32.t = {
  var r;
  r <@ Mct.bn_rsample1(a',bnd);
  r <@ M.bn_rsample1(a,bnd);
  return r;
 }
}.

(** MAIN RESULT: *)
equiv bn_rsample1_LF:
 Mct.bn_rsample1 ~ SimR.main: ={a, bnd, glob Mct} ==> ={res, glob Mct}.
proof.
transitivity LF_bn_rsample.JR.main
 ( (a,bnd){1}=(sin,pin){2} /\ (glob Mct){1}=(glob LF_bn_rsample.JR){2} ==> ={res} /\ (glob Mct){1}=(glob LF_bn_rsample.JR){2} )
 ( (a,bnd){2}=(sin,pin){1} /\ (glob Mct){2}=(glob LF_bn_rsample.JR){1} ==> ={res} /\ (glob Mct){2}=(glob LF_bn_rsample.JR){1} ) => //.
+ by move=> /> &1 &2 -> ->; exists Mct.leakages{2} (bnd,a){2} .
+ proc*; inline main.
  by wp; call bn_rsample1_cteq; auto => />.
transitivity LF_bn_rsample.Meta.SimR(LF_bn_rsample.JI, LF_bn_rsample.JR).main
 ( ={pin, sin, BN_base.XtrR.leakages} ==> ={res, BN_base.XtrR.leakages} )
 ( (a,bnd){2}=(sin,pin){1} /\ (glob Mct){2}=(glob LF_bn_rsample.JR){1} ==> ={res} /\ (glob Mct){2}=(glob LF_bn_rsample.JR){1} ) => //.
+ move => /> &1 &2 -> ->.
  by exists BN_base.XtrR.leakages{1} (pin{1},sin{1},witness).
+ by apply UniformSampling_Concrete_LF.bn_rsample_LF.
symmetry; proc*; inline main.
wp; call bn_rsample1_eq.
wp; call bn_rsample1_cteq.
by auto => />.
qed.



