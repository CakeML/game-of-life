(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open preamble;

val _ = new_theory "gol_rules";

(* There is an unbounded 2D plane of cells *)
Type state[pp] = “:(int # int) set”;

Definition b2n_def[simp]:
  b2n T = 1n ∧ b2n F = 0
End

(* Number of live neighbours to a cell at i, j *)
Definition live_adj_def:
  live_adj (s:state) i j =
    b2n (s (i-1, j-1)) + b2n (s (i, j-1)) + b2n (s (i+1, j-1)) +
    b2n (s (i-1, j+0)) +                    b2n (s (i+1, j+0)) +
    b2n (s (i-1, j+1)) + b2n (s (i, j+1)) + b2n (s (i+1, j+1))
End

(* For each tick, the game takes a simultaneous step forward in time *)
Definition step_def:
  step (s:state) (i,j) ⇔
    if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                 else live_adj s i j = 3
End

(* consequences *)

Theorem IN_step:
  (i,j) ∈ step s ⇔ if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                                else live_adj s i j = 3
Proof
  fs [IN_DEF,step_def]
QED

Theorem b2n_eq[simp]:
  (b2n b = 0 ⇔ ~b) ∧
  (b2n b = 1 ⇔ b)
Proof
  Cases_on ‘b’ \\ fs []
QED

(* area of influence *)

Definition infl_def: (* influence *)
  infl s (i,j) ⇔ live_adj s i j ≠ 0 ∨ (i,j) ∈ s
End

Theorem infl_compose:
  infl s ∩ infl t = ∅ ⇒
  step (s ∪ t) = step s ∪ step t
Proof
  fs [EXTENSION,FORALL_PROD]
  \\ rw [IN_DEF,infl_def,step_def]
  \\ first_x_assum (qspecl_then [‘p_1’,‘p_2’] mp_tac)
  \\ Cases_on ‘s (p_1,p_2)’ \\ fs [] \\ rw []
  \\ fs [live_adj_def,IN_DEF]
QED

Theorem infl_thm:
  (i,j) ∈ infl s ⇔
    (i-1, j-1) ∈ s ∨ (i, j-1) ∈ s ∨ (i+1, j-1) ∈ s ∨
    (i-1, j  ) ∈ s ∨ (i, j  ) ∈ s ∨ (i+1, j  ) ∈ s ∨
    (i-1, j+1) ∈ s ∨ (i, j+1) ∈ s ∨ (i+1, j+1) ∈ s
Proof
  fs [IN_DEF,infl_def]
  \\ Cases_on ‘s (i,j)’ \\ fs [live_adj_def]
  \\ fs [AC DISJ_COMM DISJ_ASSOC]
QED

Theorem infl_mono:
  x ⊆ y ⇒ infl x ⊆ infl y
Proof
  fs [infl_thm,SUBSET_DEF,FORALL_PROD]
  \\ rw [] \\ fs []
QED

Theorem step_SUBSET_infl:
  step s ⊆ infl s
Proof
  fs [step_def,SUBSET_DEF] \\ PairCases \\ fs [IN_step,infl_thm]
  \\ strip_tac
  \\ ‘live_adj s x0 x1 ≠ 0’ by (pop_assum mp_tac \\ IF_CASES_TAC \\ fs [])
  \\ last_x_assum kall_tac
  \\ fs [live_adj_def,IN_DEF]
QED

Theorem infl_union:
  DISJOINT (infl s) (infl s') ⇒ infl (s ∪ s') = infl s ∪ infl s'
Proof
  fs [EXTENSION,IN_DISJOINT,FORALL_PROD] \\ rw []
  \\ eq_tac \\ fs [infl_thm]
  THEN1 (rw [] \\ fs [])
  \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs []
QED

(* list to set *)

Definition to_state_def:
  to_state xs = { p | MEM (p,T) xs } : state
End

val _ = export_theory();
