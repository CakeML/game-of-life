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

(* Number of Live neighbours to a cell at i, j *)
Definition live_adj_def:
  live_adj (s:state) i j =
    b2n (s (i-1, j-1)) + b2n (s (i, j-1)) + b2n (s (i+1, j-1)) +
    b2n (s (i-1, j+0)) +                    b2n (s (i+1, j+0)) +
    b2n (s (i-1, j+1)) + b2n (s (i, j+1)) + b2n (s (i+1,j+1))
End

(* For each tick, the game takes a simultaneous step forward in time *)
Definition step_def:
  step (s:state) (i,j) ⇔
    if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                 else live_adj s i j = 3
End

Theorem IN_step:
  (i,j) ∈ step s ⇔ if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                                else live_adj s i j = 3
Proof
  fs [IN_DEF,step_def]
QED


(* composition *)

Definition infl_def: (* influence *)
  infl s (i,j) ⇔ live_adj s i j ≠ 0 ∨ (i,j) ∈ s
End

Theorem b2n_eq[simp]:
  (b2n b = 0 ⇔ ~b) ∧ (b2n b = 1 ⇔ b)
Proof
  Cases_on ‘b’ \\ fs []
QED

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

(* take 60 steps within inlfuence sets *)

Inductive steps:
  (∀i s. infl s ⊆ i ⇒ steps 0 i s s) ∧
  (∀i s t.
    infl s ⊆ i ∧ steps n i (step s) t ⇒
    steps (SUC n) i s t)
End

Definition next60_def:
  next60 (inp,i0) (c,c0,c1) (out,o1) ⇔
    i0 ⊆ inp ∧ o1 ⊆ out ∧
    DISJOINT inp c ∧ DISJOINT out c ∧
    ∃m. steps 30 (c ∪ inp) (i0 ∪ c0) m ∧
        steps 30 (c ∪ out) m (c1 ∪ o1)
End

Definition all_disjoint_def:
  all_disjoint [] = T ∧
  all_disjoint (x::xs) = (EVERY (DISJOINT x) xs ∧ all_disjoint xs)
End

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

Theorem steps30_compose:
  ∀n s s' m m'.
    all_disjoint [inp;inp';c;c'] ∧
    steps n (c ∪ inp) s m ∧
    steps n (c' ∪ inp') s' m' ⇒
    steps n (c ∪ c' ∪ (inp ∪ inp')) (s ∪ s') (m ∪ m')
Proof
  Induct
  \\ once_rewrite_tac [steps_cases] \\ fs []
  \\ rpt strip_tac
  \\ ‘infl (s ∪ s') ⊆ c ∪ c' ∪ (inp ∪ inp')’ by
   (qsuff_tac ‘infl (s ∪ s') = infl s ∪ infl s'’
    THEN1 (fs [SUBSET_DEF] \\ rw [] \\ res_tac \\ fs [])
    \\ match_mp_tac infl_union
    \\ fs [IN_DISJOINT,SUBSET_DEF,all_disjoint_def]
    \\ metis_tac [])
  \\ qsuff_tac ‘step (s ∪ s') = step s ∪ step s'’ THEN1 fs []
  \\ match_mp_tac infl_compose
  \\ fs [IN_DISJOINT,SUBSET_DEF,all_disjoint_def,EXTENSION]
  \\ metis_tac []
QED

Theorem next60_compose:
  next60 (inp,i0) (c,c0,c1) (out,o1) ∧
  next60 (inp',i0') (c',c0',c1') (out',o1') ∧
  all_disjoint [inp;inp';c;c'] ∧
  all_disjoint [out;out';c;c'] ⇒
  next60 (inp ∪ inp', i0 ∪ i0') (c ∪ c',c0 ∪ c0',c1 ∪ c1') (out ∪ out',o1 ∪ o1')
Proof
  fs [next60_def]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ strip_tac \\ conj_tac
  THEN1 (fs [SUBSET_DEF,IN_DISJOINT,all_disjoint_def]
         \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
  \\ qexists_tac ‘m ∪ m'’
  \\ drule_all steps30_compose
  \\ pop_assum kall_tac
  \\ drule_all steps30_compose
  \\ fs [AC UNION_COMM UNION_ASSOC]
QED

Theorem next60_internalise:
  next60 (f ∪ inp,x ∪ i0) (c,c0,c1) (f ∪ out,y ∪ o1) ∧
  i0 ⊆ inp ∧ o1 ⊆ out ∧
  DISJOINT (infl x) (infl i0) ∧
  DISJOINT (infl y) (infl o1) ∧
  DISJOINT f inp ∧ DISJOINT f out ⇒
  next60 (inp,i0) (f ∪ c,x ∪ c0,y ∪ c1) (out,o1)
Proof
  fs [next60_def]
  \\ strip_tac
  \\ conj_tac THEN1 (fs [IN_DISJOINT] \\ metis_tac [])
  \\ conj_tac THEN1 (fs [IN_DISJOINT] \\ metis_tac [])
  \\ qexists_tac ‘m’
  \\ fs [AC UNION_COMM UNION_ASSOC]
QED

(* infl props *)

Theorem infl_mono:
  x ⊆ y ⇒ infl x ⊆ infl y
Proof
  fs [infl_thm,SUBSET_DEF,FORALL_PROD]
  \\ rw [] \\ fs []
QED

(* from string *)

Definition fromString_def:
  fromStrings i j [] = ([]:(int # int) list) ∧
  fromStrings i j (str :: strs) =
    FLAT (MAPi (λn c. if MEM c "  ." then [] else [(& n + i,j)]) str) ++
    fromStrings i (j+1) strs
End

Definition build_def:
  build i j strs =
    QSORT (λ(i1,j1) (i2,j2). if i1 = i2 then j1 ≤ j2 else i1 ≤ i2)
      (fromStrings i j strs)
End

val _ = export_theory();
