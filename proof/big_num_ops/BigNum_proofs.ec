require import AllCore IntDiv CoreMap List RealExp.
import StdBigop Bigint BIA.

from Jasmin require import JModel.

require import W64_RejectionSamplingExtract.

require import BigNum_spec AuxLemmas.
import W64xN R.

require import BitEncoding.
import BS2Int.

module M = M(Syscall).

lemma bn_copy_correct x :
  phoare[ M.bn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])%A
  ) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@A). smt(). wp.  skip. progress. smt(). smt().
apply A.ext_eq. progress. smt(). 
qed.


equiv subc_spec:
 M.bn_subc ~ ASpecFp.subn:
  W64xN.valR a{1} = a{2} /\ W64xN.valR b{1} = b{2} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
  ==> res{1}.`1=res{2}.`1 /\ W64xN.valR res{1}.`2 = res{2}.`2.
proof.
transitivity 
 W64xN.R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 (W64xN.valR  a{1} = a{2} /\ W64xN.valR b{1} = b{2} /\ !c{1} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
   ==> res{1}.`1 = res{2}.`1 /\ W64xN.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2 ; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= 64 /\ 
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%A /\
         (forall k, i{2} <= k < 64 => a{1}.[k] = aa.[k])%A).
   wp; skip => /> &1 &2 Hi1 _ Hh1 Hh2 Hi2.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (subc _ _ _)%W64.
    pose Y := (subc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?. smt(@A). smt(@A).
    (*  by rewrite !A.set_eqiE /#. *)
    (* by rewrite !set_neqiE /#. *)
   move=> k Hk1 Hk2.
   (* by rewrite set_neqiE /#. *) smt(@A).
  wp; skip => />.
  split => *.
   split => k *.
    (* by rewrite (_:k=0) 1:/# !set_eqiE /#. *) smt(@A).
   (* by rewrite set_neqiE /#. *) smt(@A).
  by apply A.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ W64xN.R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64xN.valR a{1} = a{2} /\ W64xN.valR b{1} = b{2} /\ !c{1}  (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *) ==> ={c} 
   /\ W64xN.valR r{1} = r{2} ).
  + by move=> /> &2 H  ; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (W64xN.R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> .
progress. 
    by rewrite W64xN.R.bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.


lemma bn_set0_correct :
  phoare[ M.bn_set0 : true  ==> W64xN.valR res = 0 ] = 1%r.
proc.
while (i <= nlimbs
  /\ (forall j, 0 <= j < i => a.[j]%A = W64.zero)) (nlimbs - i). progress.
wp.  skip.  progress. smt().  smt(@A). smt(). wp.  skip. progress. smt(). smt().
rewrite - zeroRE. congr.
apply A.ext_eq. progress.  
rewrite /zeroR. smt(@A @List). 
qed.



