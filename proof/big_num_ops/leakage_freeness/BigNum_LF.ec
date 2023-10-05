require import List Int AllCore Distr.
from Jasmin require import JModel.

require import AuxLemmas.
require import W64_RejectionSamplingExtract_ct.


(* SUBTRACTION LEAKAGES  *)
op sub_prefix : leakages_t = 
  [LeakFor (1, 32); LeakAddr []; LeakAddr [0]; LeakAddr []; 
    LeakAddr []; LeakAddr [0]; LeakAddr [0]].

op sub_step (i : int) : leakages_t = 
  [LeakAddr [i] ; LeakAddr [] ; LeakAddr [] ; LeakAddr [i] ; 
    LeakAddr [i] ].


op sub_g (x : int) : leakages_t = iteri (x - 1) (fun i r => sub_step (i + 1) ++ r) [].
lemma sub_g_comp_1 x : x <= 1 => sub_g x = []. by smt(@Int). qed.

lemma sub_g_comp_2 x : 1 <  x => sub_g x = sub_step (x-1) ++ sub_g (x - 1). progress. rewrite /sub_g. smt(@Int). qed.

op sub_f (x : int) : leakages_t = sub_g x ++ sub_prefix.


lemma bn_subc_leakages start_l :
  hoare [ M(Syscall).bn_subc : M.leakages = start_l 
            ==> M.leakages = sub_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = sub_prefix ++ start_l /\ i = 1 ==> _).
progress.
while (0 < i /\ i <= 32 /\ M.leakages = sub_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /sub_f. rewrite (sub_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /sub_step. simplify. auto.
skip. progress. rewrite /sub_f.  rewrite sub_g_comp_1. auto. auto.
smt().
qed.

lemma bn_subc_ll : islossless M(Syscall).bn_subc.
proc. wp. while(0 < i /\ i <= 32) (32 - i + 1). progress.
wp. skip. smt(). wp. skip. smt().
qed.

lemma bn_subc_leakages_ph start_l :
  phoare [ M(Syscall).bn_subc : M.leakages = start_l 
            ==> M.leakages = sub_f 32 ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq bn_subc_ll. hoare. conseq (bn_subc_leakages start_l).
qed.



(* COPY LEAKAGES  *)
op copy_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] ::[].
op copy_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: LeakAddr [i] :: [].

op copy_g (x : int) : leakages_t = iteri x (fun i r => copy_step i ++ r) [].

lemma copy_g_comp_1 x : x <= 0 => copy_g x = [].
progress. rewrite /copy_g. smt(@Int). qed.

lemma copy_g_comp_2 x : 0 <  x => copy_g x = copy_step (x-1) ++ copy_g (x - 1).
progress. rewrite /copy_g. smt(@Int). qed.

op [opaque] copy_f (x : int) : leakages_t = copy_g x ++ copy_prefix.

lemma bn_copy_leakages start_l :
   hoare [ M(Syscall).bn_copy : M.leakages = start_l 
     ==> M.leakages = copy_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = copy_prefix ++ start_l /\ i = 0 ==> _).
progress.
while (0 <= i /\ i <= 32 /\ M.leakages = copy_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /copy_f. rewrite (copy_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /copy_step. simplify. auto.
skip. progress. rewrite /copy_f.  rewrite copy_g_comp_1. auto. auto. 
smt().
qed.


lemma bn_copy_ll : islossless M(Syscall).bn_copy.
proc. wp. while(0 <= i /\ i <= 32) (32 - i + 1). progress.
wp. skip. smt(). wp. skip. smt().
qed.


lemma bn_copy_leakages_ph start_l :
   phoare [ M(Syscall).bn_copy : M.leakages = start_l 
     ==> M.leakages = copy_f 32 ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq bn_copy_ll. hoare. conseq (bn_copy_leakages start_l).
qed.




(* set0 LEAKAGES  *)
op set0_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: [].
op set0_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: [].

op set0_g (x : int) : leakages_t = iteri x (fun i r => set0_step i ++ r) [].
lemma set0_g_comp_1 x : x <= 0 => set0_g x = []. by smt(@Int). qed.
lemma set0_g_comp_2 x : 0 <  x => set0_g x = set0_step (x-1) ++ set0_g (x - 1). by smt(@Int). qed.

op [opaque] set0_f (x : int) : leakages_t = set0_g x ++ set0_prefix.

lemma bn_set0_leakages start_l :
   hoare [ M(Syscall).bn_set0 : M.leakages = start_l 
                ==> M.leakages = set0_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = set0_prefix ++ start_l /\ i = 0 ==> _).
progress. rewrite /set0_prefix.
while (0 <= i /\ i <= 32 /\ M.leakages = set0_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /set0_f. rewrite (set0_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /set0_step. simplify. auto.
skip. progress. rewrite /set0_f.  rewrite set0_g_comp_1. auto. auto. 
smt().
qed.

lemma bn_set0_ll : islossless M(Syscall).bn_set0.
proc. wp. while(0 <= i /\ i <= 32) (32 - i + 1). progress.
wp. skip. smt(). wp. skip. smt().
qed.

lemma bn_set0_leakages_ph start_l :
   phoare [ M(Syscall).bn_set0 : M.leakages = start_l 
                ==> M.leakages = set0_f 32 ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq bn_set0_ll. hoare. conseq (bn_set0_leakages start_l).
qed.

