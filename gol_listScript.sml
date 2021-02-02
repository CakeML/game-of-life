(*
  A representation of GOL as coordinate lists. This representation can
  only represent GOL states with finitely many Live cells.
*)
open preamble gol_rulesTheory;

val _ = new_theory "gol_list";

(* The precence of (i,j) in a list means that location (i,j) is Live. *)
Definition fromList_def:
  fromList l i j = if MEM (i,j) l then Live else Dead
End

Definition min_max_def:
  min_max min max [] = (min,max) ∧
  min_max min max ((i:int)::is) =
    min_max (if i < min then i else min) (if max < i then i else max) is
End

Definition min_max_coordinates_def:
  min_max_coordinates [] = NONE ∧
  min_max_coordinates ((i,j)::alive) =
    SOME (min_max i i (MAP FST alive),
          min_max j j (MAP SND alive))
End

Definition int_range_def:
  int_range i j =
    if j < i then [] else
      GENLIST (λn. & n + i) (Num (j - i + 1))
End

Definition cross_def:
  cross [] js = [] ∧
  cross (i::is) js = MAP (λj. (i,j)) js ++ cross is js
End

Definition active_area_def:
  active_area l =
    case min_max_coordinates l of
    | NONE => []
    | SOME ((i1,i2),(j1,j2)) =>
        let is = int_range (i1 - 1) (i2 + 1) in
        let js = int_range (j1 - 1) (j2 + 1) in
          cross is js
End

(* This computes the next state after a step-transition in GOL *)
Definition next_def:
  next l =
    FILTER (λ(i,j). step (fromList l) i j = Live) (active_area l)
End

Theorem min_max_thm:
  ∀xs m n l h.
    min_max m n xs = (l,h) ⇒
      l ≤ m ∧ n ≤ h ∧
      ∀x. MEM x xs ⇒ l ≤ x ∧ x ≤ h
Proof
  Induct \\ fs [min_max_def]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum drule
  \\ pop_assum kall_tac
  \\ rw [] \\ res_tac
  \\ intLib.COOPER_TAC
QED

Theorem min_max_coordinates_imp:
  l ≠ [] ⇒
  ∃i1 i2 j1 j2.
    min_max_coordinates l = SOME ((i1,i2),(j1,j2)) ∧
    ∀i j. MEM (i,j) l ⇒ i1 ≤ i ∧ i ≤ i2 ∧ j1 ≤ j ∧ j ≤ j2
Proof
  Cases_on ‘l’ \\ fs [] \\ PairCases_on ‘h’
  \\ fs [min_max_coordinates_def] \\ rw []
  \\ Cases_on ‘min_max h0 h0 (MAP FST t)’ \\ fs []
  \\ Cases_on ‘min_max h1 h1 (MAP SND t)’ \\ fs []
  \\ imp_res_tac min_max_thm
  \\ fs [FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem MEM_cross:
  ∀is js i j. MEM (i,j) (cross is js) ⇔ MEM i is ∧ MEM j js
Proof
  Induct \\ fs [cross_def] \\ fs [MEM_MAP] \\ metis_tac []
QED

Theorem MEM_int_range:
  ∀i j n. MEM n (int_range i j) ⇔ i ≤ n ∧ n ≤ j
Proof
  rw [int_range_def]
  THEN1 intLib.COOPER_TAC
  \\ fs [MEM_GENLIST]
  \\ eq_tac \\ rw []
  THEN1 intLib.COOPER_TAC
  THEN1 intLib.COOPER_TAC
  \\ qexists_tac ‘Num (n - i)’
  \\ intLib.COOPER_TAC
QED

Theorem c2n_eq_0:
  c2n c = 0 ⇔ c = Dead
Proof
  Cases_on ‘c’ \\ fs [c2n_def]
QED

(* correctness of next *)
Theorem fromList_next:
  fromList (next l) = step (fromList l)
Proof
  fs [FUN_EQ_THM] \\ rw [] \\ rename [‘step _ i j’]
  \\ fs [fromList_def,next_def,active_area_def]
  \\ Cases_on ‘l = []’ \\ fs [min_max_coordinates_def]
  THEN1 EVAL_TAC
  \\ drule min_max_coordinates_imp \\ strip_tac \\ fs []
  \\ fs [MEM_FILTER,MEM_cross,MEM_int_range]
  \\ Cases_on ‘step (fromList l) i j’ \\ fs []
  \\ fs [AllCaseEqs()]
  \\ CCONTR_TAC
  \\ qsuff_tac ‘live_adj (fromList l) i j = 0’
  THEN1 (strip_tac \\ fs [step_def,AllCaseEqs()])
  \\ simp [live_adj_def]
  \\ fs [c2n_eq_0]
  \\ fs [fromList_def,AllCaseEqs()]
  \\ CCONTR_TAC \\ fs []
  \\ res_tac \\ intLib.COOPER_TAC
QED

val _ = export_theory();
