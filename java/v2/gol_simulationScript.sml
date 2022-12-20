(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open preamble gol_rulesTheory gol_simTheory;

val _ = new_theory "gol_simulation";

(* important definitions *)

Definition to_state_def:
  to_state xs = { p | MEM (p,T) xs } : gol_rules$state
End

Definition gol_simulation_def:
  (gol_simulation [] ⇔ T) ∧
  (gol_simulation [x] ⇔ T) ∧
  (gol_simulation (x::y::ys) ⇔
     step (to_state x) = to_state y ∧
     gol_simulation (y::ys))
End

(* minor definitions *)

Definition ii_lt_def:
  ii_lt (i:int,j:int) (i',j') ⇔ i < i' ∨ (i = i' ∧ j < j')
End

Theorem ii_lt_trans:
  ii_lt x y ∧ ii_lt y z ⇒ ii_lt x z
Proof
  PairCases_on ‘x’
  \\ PairCases_on ‘y’
  \\ PairCases_on ‘z’
  \\ fs [ii_lt_def]
  \\ intLib.COOPER_TAC
QED

Theorem SORTED_ii_lt_IMP:
  SORTED ii_lt xs ⇒ ALL_DISTINCT xs
Proof
  Induct_on ‘xs’ \\ fs []
  \\ Cases_on ‘xs’ \\ fs []
  \\ PairCases_on ‘h’ \\ PairCases \\ fs []
  \\ strip_tac \\ gvs []
  \\ conj_tac
  >-
   (rw [] \\ fs []
    \\ fs [ii_lt_def]
    \\ intLib.COOPER_TAC)
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘h0’
  \\ qid_spec_tac ‘h1’
  \\ qid_spec_tac ‘t’
  \\ Induct \\ fs [FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac \\ strip_tac
  \\ fs []
  \\ imp_res_tac ii_lt_trans
  \\ res_tac \\ fs []
  \\ rw [] \\ fs []
  \\ fs [ii_lt_def]
  \\ intLib.COOPER_TAC
QED

Definition state_lookup_def:
  state_lookup p xs =
    case ALOOKUP xs p of
    | SOME b => b
    | NONE => F
End

Definition check_pos_def:
  check_pos xs ys (i:int,j:int) ⇔
    state_lookup (i,j) ys =
    gol (state_lookup (i-1,j-1) xs) (state_lookup (i,j-1) xs) (state_lookup (i+1,j-1) xs)
        (state_lookup (i-1,j  ) xs) (state_lookup (i,j  ) xs) (state_lookup (i+1,j  ) xs)
        (state_lookup (i-1,j+1) xs) (state_lookup (i,j+1) xs) (state_lookup (i+1,j+1) xs)
End

Triviality imp_set_eq:
  s ⊆ p ∧ t ⊆ p ∧ (∀x. x ∈ p ⇒ (x ∈ s ⇔ x ∈ t)) ⇒ s = t
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality state_lookup_to_state:
  ALL_DISTINCT (MAP FST xs) ⇒ state_lookup p xs = to_state xs p
Proof
  PairCases_on ‘p’
  \\ fs [state_lookup_def,to_state_def]
  \\ Cases_on ‘ALOOKUP xs (p0,p1)’ \\ gvs []
  \\ imp_res_tac ALOOKUP_NONE \\ fs [MEM_MAP]
  \\ imp_res_tac ALOOKUP_MEM \\ rw []
  \\ eq_tac \\ rw [] \\ fs []
  \\ imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM
  \\ fs []
QED

Definition check_infl_def:
  check_infl [] ps = T ∧
  check_infl ((x:int,y:int)::xs) ps =
    (MEM (x-1,y-1) ps ∧ MEM (x,y-1) ps ∧ MEM (x+1,y-1) ps ∧
     MEM (x-1,y  ) ps ∧ MEM (x,y  ) ps ∧ MEM (x+1,y  ) ps ∧
     MEM (x-1,y+1) ps ∧ MEM (x,y+1) ps ∧ MEM (x+1,y+1) ps ∧
     check_infl xs ps)
End

Theorem check_infl:
  check_infl xs ps ⇒ infl (set xs) SUBSET set ps
Proof
  Induct_on ‘xs’ \\ fs [check_infl_def]
  >-
   (fs [SUBSET_DEF,IN_DEF,infl_def,FORALL_PROD]
    \\ fs [live_adj_def])
  \\ fs [SUBSET_DEF,IN_DEF,infl_thm,FORALL_PROD,check_infl_def]
  \\ rw [] \\ fs []
  \\ gvs [int_arithTheory.elim_minus_ones]
QED

Theorem IMP_step_to_state:
  ∀xs ys ps.
    (let xs' = MAP FST xs in
     let ys' = MAP FST ys in
       ALL_DISTINCT xs' ∧
       ALL_DISTINCT ys' ∧
       EVERY (λy. MEM y ps) ys' ∧
       check_infl xs' ps ∧
       EVERY (check_pos xs ys) ps)
    ⇒
    step (to_state xs) = to_state ys
Proof
  rw [] \\ fs [step_def]
  \\ irule imp_set_eq
  \\ qexists_tac ‘set ps’
  \\ ‘step (to_state xs) ⊆ set ps’ by
   (irule SUBSET_TRANS
    \\ irule_at Any check_infl
    \\ first_x_assum $ irule_at Any
    \\ irule SUBSET_TRANS
    \\ irule_at Any step_SUBSET_infl
    \\ irule infl_mono
    \\ fs [to_state_def,SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD]
    \\ rw [] \\ pop_assum $ irule_at Any)
  \\ ‘to_state ys ⊆ set ps’ by
   (fs [SUBSET_DEF] \\ rw [] \\ PairCases_on ‘x’
    \\ fs [to_state_def,EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ res_tac \\ fs [])
  \\ fs [] \\ PairCases \\ rw []
  \\ simp [IN_step] \\ fs [EVERY_MEM]
  \\ first_x_assum drule
  \\ fs [check_pos_def,gol_def,live_adj_def,IN_DEF,state_lookup_to_state]
QED

val _ = export_theory();
