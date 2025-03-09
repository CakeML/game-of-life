(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open HolKernel bossLib boolLib Parse;
open pred_setTheory pairTheory dep_rewrite arithmeticTheory listTheory
     alistTheory rich_listTheory combinTheory gol_rulesTheory
     integerTheory intLib

val _ = new_theory "gol_circuit";

Overload LLOOKUP = “λl n. oEL n l”;
Overload "U" = “BIGUNION”;

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

Theorem IMP_infl_subset:
  s ⊆ COMPL (infl (COMPL t)) ⇒ infl s ⊆ t
Proof
  gvs [SUBSET_DEF] \\ gvs [IN_DEF, infl_def, FORALL_PROD]
  \\ gvs [live_adj_def,IN_DEF] \\ rw []
  \\ Cases_on ‘s (p_1,p_2)’ \\ gvs []
  \\ last_x_assum drule \\ gvs [integerTheory.INT_SUB_ADD]
  \\ gvs [intLib.COOPER_PROVE “m + k - k:int = m”]
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
  infl (s ∪ s') = infl s ∪ infl s'
Proof
  fs [EXTENSION,IN_DISJOINT,FORALL_PROD] \\ rw []
  \\ eq_tac \\ fs [infl_thm]
  \\ rw [] \\ fs []
QED

(* runs *)

Datatype:
  modifier =
    <| area           : (int # int) set ;
       deletions      : (int # int) set ;
       insertions     : (int # int) set ;
       assert_area    : (int # int) set ;
       assert_content : (int # int) set |>
End

Definition mod_step_def:
  mod_step c s1 s3 ⇔
    ∃s2.
      infl s1 ⊆ c.area ∧
      step s1 = s2 ∧
      s2 ∩ c.assert_area = c.assert_content ∧
      s3 = c.insertions ∪ (s2 DIFF c.deletions)
End

Theorem mod_step_univ:
  c.area = UNIV ∧ c.insertions = EMPTY ∧ c.deletions = EMPTY
  ⇒
  (mod_step c s1 s2
   ⇔
   step s1 = s2 ∧
   s2 ∩ c.assert_area = c.assert_content)
Proof
  gvs [mod_step_def] \\ metis_tac []
QED

Definition mod_steps_def:
  mod_steps 0 c n s1 s2 = (s1 = s2) ∧
  mod_steps (SUC k) c n s1 s3 =
     ∃s2. mod_step (c n) s1 s2 ∧ mod_steps k c (n+1:num) s2 s3
End

Definition run_to_def:
  run_to k c s t ⇔ mod_steps k c 0 s t
End

Definition run_def:
  run c s = ∀k. ∃t. run_to k c s t
End

Definition disjoint_mod_def:
  disjoint_mod m1 m2 ⇔ DISJOINT m1.area m2.area
End

Definition disjoint_mods_def:
  disjoint_mods c1 c2 ⇔ ∀n. disjoint_mod (c1 n) (c2 n)
End

Definition mod_wf_def:
  mod_wf m ⇔
    m.deletions ⊆ m.area ∧
    m.assert_area ⊆ m.area ∧
    m.assert_content ⊆ m.assert_area
End

Definition mods_wf_def:
  mods_wf c = ∀n. mod_wf (c (n:num))
End

Definition join_def:
  join c1 c2 =
    λn. <| area           := (c1 n).area ∪ (c2 n).area ;
           deletions      := (c1 n).deletions ∪ (c2 n).deletions ;
           insertions     := (c1 n).insertions ∪ (c2 n).insertions ;
           assert_area    := (c1 n).assert_area ∪ (c2 n).assert_area ;
           assert_content := (c1 n).assert_content ∪ (c2 n).assert_content |>
End

Theorem mod_steps_compose:
  ∀c1 c2 k n s1 s2 t1 t2.
    disjoint_mods c1 c2 ∧
    mods_wf c1 ∧
    mods_wf c2 ∧
    mod_steps k c1 n s1 t1 ∧
    mod_steps k c2 n s2 t2 ⇒
    mod_steps k (join c1 c2) n (s1 ∪ s2) (t1 ∪ t2)
Proof
  gen_tac \\ gen_tac \\ Induct \\ gvs [mod_steps_def]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum drule_all
  \\ rename [‘_ (u1 ∪ u2) (_ ∪ _)’]
  \\ disch_then $ irule_at Any
  \\ gvs [mod_step_def,join_def]
  \\ gvs [infl_union,mods_wf_def,disjoint_mods_def,disjoint_mod_def]
  \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [mod_wf_def]
  \\ DEP_REWRITE_TAC [infl_compose]
  \\ qabbrev_tac ‘u1 = step s1’
  \\ qabbrev_tac ‘u2 = step s2’
  \\ ‘u1 ⊆ infl s1’ by gvs [step_SUBSET_infl,Abbr‘u1’]
  \\ ‘u2 ⊆ infl s2’ by gvs [step_SUBSET_infl,Abbr‘u2’]
  \\ gvs [IN_DISJOINT,EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Definition join_all_def:
  join_all (dom, cs) = λn.
    <|area           := U { (cs i n).area           | i ∈ dom } ;
      deletions      := U { (cs i n).deletions      | i ∈ dom } ;
      insertions     := U { (cs i n).insertions     | i ∈ dom } ;
      assert_area    := U { (cs i n).assert_area    | i ∈ dom } ;
      assert_content := U { (cs i n).assert_content | i ∈ dom } |>
End

Theorem infl_bigunion:
  infl (U ss) = U { infl s | s ∈ ss }
Proof
  rw [Once SET_EQ_SUBSET, BIGUNION_SUBSET]
  >-
   (fs [SUBSET_DEF, FORALL_PROD, infl_thm]
    \\ simp [GSYM EXISTS_OR_THM, GSYM RIGHT_AND_OVER_OR, GSYM infl_thm]
    \\ metis_tac [])
  \\ metis_tac [SUBSET_BIGUNION_I, infl_mono]
QED

Theorem IN_infl_bounds:
  (x,y) ∈ infl s ⇔ ∃x1 y1. (x1,y1) ∈ s ∧ ABS (x - x1) ≤ 1 ∧ ABS (y - y1) ≤ 1
Proof
  gvs [infl_thm] \\ rw [] \\ reverse eq_tac \\ rw []
  >-
   (CCONTR_TAC \\ gvs []
    \\ imp_res_tac (METIS_PROVE [] “(x,y) ∈ s ∧ (a,b) ∉ s ⇒  a = x ⇒ y ≠ b”)
    \\ intLib.COOPER_TAC)
  \\ rpt $ pop_assum $ irule_at Any
  \\ intLib.COOPER_TAC
QED

Theorem DISJOINT_infl:
  DISJOINT (infl s) (infl t) ⇒
  ∀x1 y1 x2 y2.
    (x1,y1) ∈ s ∧
    (x2,y2) ∈ t ⇒
    2 < ABS (x1 - x2) ∨ 2 < ABS (y1 - y2)
Proof
  CCONTR_TAC \\ gvs []
  \\ last_x_assum mp_tac
  \\ gvs [DISJOINT_DEF]
  \\ gvs [DISJOINT_DEF,EXTENSION,FORALL_PROD]
  \\ gvs [IN_infl_bounds,PULL_EXISTS]
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ intLib.COOPER_TAC
QED

Theorem live_adj_eq_0:
  live_adj s x y = 0 ⇔
  (x-1,y-1) ∉ s ∧
  (x,y-1) ∉ s ∧
  (x+1,y-1) ∉ s ∧
  (x-1,y) ∉ s ∧
  (x+1,y) ∉ s ∧
  (x-1,y+1) ∉ s ∧
  (x,y+1) ∉ s ∧
  (x+1,y+1) ∉ s
Proof
  gvs [live_adj_def,IN_DEF, AC CONJ_COMM CONJ_ASSOC]
QED

Theorem disjoint_live_adj:
  DISJOINT (infl y) (infl s) ∧ (x0,x1) ∈ s ⇒
  live_adj y x0 x1 = 0
Proof
  simp [live_adj_eq_0]
  \\ CCONTR_TAC \\ gvs []
  \\ drule_all DISJOINT_infl
  \\ intLib.COOPER_TAC
QED

Definition adj_def:
  adj x y = { (x1,y1) | ABS (x - x1) ≤ 1 ∧ ABS (y - y1) ≤ 1 } DIFF {(x,y)}
End

Theorem adj_set:
  adj x y = set [(x-1,y-1);(x,y-1);(x+1,y-1);(x-1,y);(x+1,y);(x-1,y+1);(x,y+1);(x+1,y+1)]
Proof
  gvs [EXTENSION]
  \\ gvs [adj_def,FORALL_PROD] \\ rw []
  \\ intLib.COOPER_TAC
QED

Theorem finite_adj:
  FINITE (adj x y)
Proof
  rewrite_tac [adj_set] \\ simp []
QED

Theorem live_adj_eq:
  live_adj s x y = CARD (s ∩ adj x y)
Proof
  rewrite_tac [adj_set]
  \\ ‘∀xs. s ∩ set xs = set (FILTER s xs)’
        by gvs [EXTENSION,MEM_FILTER,IN_DEF]
  \\ asm_rewrite_tac []
  \\ DEP_REWRITE_TAC [ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ conj_tac
  >-
   (irule FILTER_ALL_DISTINCT
    \\ gvs [] \\ intLib.COOPER_TAC)
  \\ gvs [live_adj_def]
  \\ rw [] \\ gvs []
QED

Triviality int_lemma:
  ABS (x − a) ≤ 1 ∧ ABS (x − b) ≤ 1 ⇒  ~(2 < ABS (a − b))
Proof
  intLib.COOPER_TAC
QED

Theorem live_adj_U:
  ∀k x0 x1.
    (∀x y. x ∈ ss ∧ y ∈ ss ∧ x ≠ y ⇒ DISJOINT (infl x) (infl y)) ∧
    k ≠ 0 ⇒
    (live_adj (U ss) x0 x1 = k ⇔
     ∃x. x ∈ ss ∧ live_adj x x0 x1 = k)
Proof
  gvs [live_adj_eq]
  \\ rw [] \\ eq_tac \\ rw []
  \\ gvs [finite_adj,FINITE_INTER,pred_setTheory.CARD_EQ_0]
  \\ gvs [EXTENSION]
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ AP_TERM_TAC
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []
  \\ rpt $ first_assum $ irule_at $ Pos last
  \\ qpat_x_assum ‘_ ∈ ss’ mp_tac
  \\ qpat_x_assum ‘_ ∈ ss’ mp_tac
  \\ rename [‘s1 ∈ ss ⇒ s2 ∈ ss ⇒ _’]
  \\ Cases_on ‘s1 = s2’ \\ gvs []
  \\ rpt strip_tac
  \\ last_x_assum $ qspecl_then [‘s1’,‘s2’] mp_tac
  \\ (impl_tac >- (gvs [EXTENSION] \\ metis_tac []))
  \\ strip_tac
  \\ qpat_x_assum ‘_ ∈ adj _ _’ mp_tac
  \\ qpat_x_assum ‘_ ∈ adj _ _’ mp_tac
  \\ rename [‘x ∈ _ ⇒ y ∈ _ ⇒ _’]
  \\ rpt strip_tac
  \\ PairCases_on ‘x’
  \\ PairCases_on ‘y’
  \\ imp_res_tac DISJOINT_infl
  \\ gvs [adj_def]
  \\ imp_res_tac int_lemma
QED

Theorem infl_compose_bigunion:
  (∀x y. x ∈ ss ∧ y ∈ ss ∧ x ≠ y ⇒ DISJOINT (infl x) (infl y))
  ⇒
  step (U ss) = U { step s | s ∈ ss }
Proof
  strip_tac
  \\ simp [Once EXTENSION]
  \\ PairCases
  \\ gvs [PULL_EXISTS]
  \\ reverse $ rw [IN_DEF,infl_def,step_def]
  >-
   (gvs [METIS_PROVE [] “b ∨ ~c ⇔ (c ⇒ b)”, SF CONJ_ss]
    \\ drule live_adj_U
    \\ disch_then $ qspec_then ‘3’ mp_tac
    \\ simp_tac std_ss []
    \\ disch_then $ rewrite_tac o single
    \\ rewrite_tac [IN_DEF] \\ simp_tac std_ss []
    \\ eq_tac \\ rpt strip_tac
    \\ rpt $ first_assum $ irule_at Any)
  \\ eq_tac \\ rpt strip_tac
  \\ rpt $ first_assum $ irule_at $ Pos last \\ simp []
  >-
   (drule live_adj_U
    \\ disch_then $ qspec_then ‘2’ mp_tac \\ simp_tac std_ss []
    \\ strip_tac \\ gvs []
    \\ rename [‘y ∈ ss’]
    \\ Cases_on ‘y = s’ \\ gvs []
    \\ gvs [IN_DEF]
    \\ ‘DISJOINT (infl y) (infl s)’ by res_tac
    \\ drule disjoint_live_adj \\ simp [IN_DEF]
    \\ disch_then imp_res_tac \\ gvs [])
  >-
   (drule live_adj_U
    \\ disch_then $ qspec_then ‘3’ mp_tac \\ simp_tac std_ss []
    \\ strip_tac \\ gvs []
    \\ rename [‘y ∈ ss’]
    \\ Cases_on ‘y = s’ \\ gvs []
    \\ gvs [IN_DEF]
    \\ ‘DISJOINT (infl y) (infl s)’ by res_tac
    \\ drule disjoint_live_adj \\ simp [IN_DEF]
    \\ disch_then imp_res_tac \\ gvs [])
  \\ drule live_adj_U \\ gvs [] \\ gvs [IN_DEF]
  \\ metis_tac []
QED

Theorem mod_step_compose_bigunion:
  ∀n cs s t.
    (∀x y. x ∈ dom ∧ y ∈ dom ∧ x ≠ y ⇒ disjoint_mods (cs x) (cs y)) ∧
    (∀i. i ∈ dom ⇒ mods_wf (cs i) ∧ mod_step (cs i n) (s i) (t i))
    ⇒
    mod_step (join_all (dom, cs) n) (U { s i | i ∈ dom }) (U { t i | i ∈ dom })
Proof
  rw [mod_step_def, join_all_def, infl_bigunion]
  >- (rw [BIGUNION_SUBSET] \\ irule SUBSET_BIGUNION_SUBSET_I
    \\ simp [PULL_EXISTS] \\ metis_tac [])
  \\ dep_rewrite.DEP_REWRITE_TAC [infl_compose_bigunion]
  \\ (rw []
    >- (`i ≠ i'` by metis_tac [] \\ `disjoint_mods (cs i) (cs i')` by rw []
      \\ fs [disjoint_mods_def, disjoint_mod_def]
      \\ metis_tac [IN_DISJOINT, SUBSET_DEF]))
  >- (rw [Once EXTENSION, PULL_EXISTS] \\ eq_tac \\ rw []
    >- (Cases_on `i = i'`
      >- (gvs [mods_wf_def, mod_wf_def, SUBSET_DEF, EXTENSION] \\ metis_tac [])
      \\ `disjoint_mods (cs i) (cs i')` by rw []
      \\ fs [disjoint_mods_def, disjoint_mod_def, mods_wf_def, mod_wf_def]
      \\ metis_tac [step_SUBSET_infl, IN_DISJOINT, SUBSET_DEF])
    \\ rpt $ first_assum $ irule_at Any \\ fs [EXTENSION])
  \\ rw [Once EXTENSION, PULL_EXISTS]
  \\ fs [Once EXTENSION, Once EXTENSION, mods_wf_def, mod_wf_def, SUBSET_DEF]
  \\ eq_tac \\ rw []
  >- (first_assum $ drule_then (gvs o single)
    >- metis_tac []
    \\ `∀i. i ∈ dom ⇒ x ∉ (cs i n).deletions` suffices_by metis_tac []
    \\ rw [] \\ Cases_on `i = i'`
    >- (gvs [mods_wf_def, mod_wf_def, SUBSET_DEF, EXTENSION] \\ metis_tac [])
    \\ `disjoint_mods (cs i) (cs i')` by rw []
    \\ fs [disjoint_mods_def, disjoint_mod_def, mods_wf_def, mod_wf_def]
    \\ metis_tac [step_SUBSET_infl, IN_DISJOINT, SUBSET_DEF])
  \\ metis_tac []
QED

Theorem mod_steps_compose_bigunion:
  ∀k cs n s t.
    (∀x y. x ∈ dom ∧ y ∈ dom ∧ x ≠ y ⇒ disjoint_mods (cs x) (cs y)) ∧
    (∀i. i ∈ dom ⇒ mods_wf (cs i) ∧ mod_steps k (cs i) n (s i) (t i))
    ⇒
    mod_steps k (join_all (dom, cs)) n (U { s i | i ∈ dom }) (U { t i | i ∈ dom })
Proof
  Induct \\ gvs [mod_steps_def]
  >- (simp [Once EXTENSION, Once EXTENSION] \\ metis_tac [])
  \\ metis_tac [mod_step_compose_bigunion]
QED

Theorem run_compose_bigunion:
  ∀dom cs s.
    (∀x y. x ∈ dom ∧ y ∈ dom ∧ x ≠ y ⇒ disjoint_mods (cs x) (cs y)) ∧
    (∀i. i ∈ dom ⇒ mods_wf (cs i) ∧ run (cs i) (s i))
    ⇒
    run (join_all (dom, cs)) (U { s i | i ∈ dom })
Proof
  rw [run_def, run_to_def]
  \\ `∀i. i ∈ dom ⇒ ∃t. mod_steps k (cs i) 0 (s i) t` by metis_tac []
  \\ metis_tac [mod_steps_compose_bigunion]
QED

Definition empty_mod_def:
  empty_mod = λn:num.
    <|area           := ∅ ;
      deletions      := ∅ ;
      insertions     := ∅ ;
      assert_area    := ∅ ;
      assert_content := ∅ |>
End

Theorem run_empty_mod:
  run empty_mod ∅
Proof
  `join_all (∅,(λ_. empty_mod)) = empty_mod` by
    simp [FUN_EQ_THM, empty_mod_def, join_all_def]
  \\ mp_tac $ Q.SPECL [`∅`,`λ_.empty_mod`,`λ_.∅`] run_compose_bigunion
  \\ simp []
QED

(*
  deletions and insertions --> assertions
*)

Definition can_assert_def:
  can_assert p c ⇔
    ∀n:num.
      p ∩ (c n).deletions ≠ EMPTY ⇒
      p ⊆ (c n).deletions ∧
      p ⊆ (c n).assert_area ∧
      (c n).insertions ∩ p = (c n).assert_content ∩ p
End

Definition assert_mod_def:
  assert_mod p m =
    if p ∩ m.deletions = EMPTY then m else
      m with <| insertions := m.insertions DIFF p ;
                deletions := m.deletions DIFF p |>
End

Definition assert_def:
  assert p c = λn. assert_mod p (c n)
End

Theorem to_assert:
  ∀k n s t.
    mod_steps k c n s t ∧
    can_assert p c
    ⇒
    mod_steps k (assert p c) n s t
Proof
  Induct
  \\ gvs [mod_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [mod_step_def,assert_def,assert_mod_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem to_assert_run:
  ∀c s.
    run c s ∧
    can_assert p c
    ⇒
    run (assert p c) s
Proof
  rw [run_def,run_to_def]
  \\ last_x_assum $ qspec_then ‘k’ strip_assume_tac
  \\ drule_all to_assert
  \\ disch_then $ irule_at Any
QED

(*
  deletions and insertions --> nop
*)

Definition del_io_mod_def:
  del_io_mod p m =
    if p ∩ m.deletions = EMPTY then m else
      m with <| assert_area := m.assert_area DIFF p ;
                assert_content := m.assert_content DIFF p ;
                insertions := m.insertions DIFF p ;
                deletions := m.deletions DIFF p |>
End

Definition del_io_def:
  del_io p c = λn. del_io_mod p (c n)
End

Theorem to_del_io:
  ∀k n s t.
    mod_steps k c n s t ∧
    can_assert p c
    ⇒
    mod_steps k (del_io p c) n s t
Proof
  Induct
  \\ gvs [mod_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [mod_step_def,del_io_def,del_io_mod_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem to_del_io_run:
  ∀c s.
    run c s ∧
    can_assert p c
    ⇒
    run (del_io p c) s
Proof
  rw [run_def,run_to_def]
  \\ last_x_assum $ qspec_then ‘k’ strip_assume_tac
  \\ drule_all to_del_io
  \\ disch_then $ irule_at Any
QED

(* turn all ins and outs to asserts *)

Definition clear_mod_def:
  clear_mod m =
    m with <| area := UNIV ; insertions := {} ; deletions := {} |>
End

Definition clear_mods_def:
  clear_mods m n = clear_mod (m n)
End

Definition can_clear_def:
  can_clear c =
    ∀n. (c n).deletions = (c n).assert_area ∧
        (c n).assert_content = (c n).insertions
End

Theorem mod_steps_clear_mods:
  ∀k c n s t.
    mod_steps k c n s t ∧
    can_clear c
    ⇒
    mod_steps k (clear_mods c) n s t
Proof
  Induct
  \\ gvs [mod_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ gvs [mod_step_def,can_clear_def,clear_mods_def,clear_mod_def]
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem run_clear_mods:
  ∀c s.
    run c s ∧
    can_clear c
    ⇒
    run (clear_mods c) s
Proof
  rw [run_def,run_to_def]
  \\ last_x_assum $ qspec_then ‘k’ strip_assume_tac
  \\ drule_all mod_steps_clear_mods
  \\ disch_then $ irule_at Any
QED

(*
  TODO: translate by dx dy
*)

(*
  circuit conventions (set and list versions)
   - uses 75x75 coordinates
*)

Definition box_def:
  box (x:int,y:int) (w:num,h:num) = { (x + &i, y + &j) | i < w ∧ j < h }
End

Definition base_area_def:
  base_area area =
    U { box (75 * x - 75, 75 * y - 75) (150,150) | (x,y) ∈ area }
End

Definition io_box_def:
  io_box (x:int, y:int) =
    box (75 * x - 6, 75 * y - 6) (12, 12)
End

Datatype:
  dir = N | S | W | E
End

Definition is_ns_def:
  is_ns ((x,y),d,r) = (d = N ∨ d = S)
End

Definition is_ew_def:
  is_ew ((x,y),d,r) = (d = E ∨ d = W)
End

Definition add_pt_def[simp]:
  add_pt (a:int,b:int) (c,d) = (a+c,b+d)
End

Definition sub_pt_def[simp]:
  sub_pt (a:int,b:int) (c,d) = (a-c,b-d)
End

Definition neg_pt_def[simp]:
  neg_pt (a:int,b:int) = (-a,-b)
End

Theorem add_pt_0[simp]:
  add_pt x (0,0) = x
Proof
  Cases_on `x` \\ simp []
QED

Theorem add_pt_assoc:
  add_pt a (add_pt b c) = add_pt (add_pt a b) c
Proof
  MAP_EVERY Cases_on [`a`,`b`,`c`] \\ simp [INT_ADD_ASSOC]
QED

Definition dir_to_xy_def[simp]:
  dir_to_xy N = (0,-1) ∧
  dir_to_xy S = (0,1) ∧
  dir_to_xy E = (1,0) ∧
  dir_to_xy W = (-1,0)
End

Definition circ_mod_wf_def:
  circ_mod_wf area ins outs as ⇔
    (∀x y. (x,y) ∈ area ⇒ x % 2 = 0 ∧ y % 2 = 0) ∧
    (∀p r1 r2. (p,r1) ∈ ins ∧ (p,r2) ∈ ins ⇒ r1 = r2) ∧
    (∀p r1 r2. (p,r1) ∈ outs ∪ as ∧ (p,r2) ∈ outs ∪ as ⇒ r1 = r2) ∧
    (∀p d r. (p,d,r) ∈ ins ∪ as ⇒ add_pt p (dir_to_xy d) ∈ area) ∧
    (∀p d r. (p,d,r) ∈ outs ∪ as ⇒ sub_pt p (dir_to_xy d) ∈ area) ∧
    (∀p d r. (p,d,r) ∈ ins ∧ sub_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ outs) ∧
    (∀p d r. (p,d,r) ∈ outs ∧ add_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ ins) ∧
    (∀p r. (p,r) ∈ as ⇒ ∀q. (p,q) ∉ ins ∧ (p,q) ∉ outs)
End

Theorem circ_mod_wf_def_old:
  circ_mod_wf area ins outs as ⇔
    (∀x y. (x,y) ∈ area ⇒ x % 2 = 0 ∧ y % 2 = 0) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ ins ∧ ((x,y),r2) ∈ ins ⇒ r1 = r2) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ outs ∪ as ∧ ((x,y),r2) ∈ outs ∪ as ⇒ r1 = r2) ∧
    (∀x y r. ((x,y),N,r) ∈ ins ∪ as ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ ins ∪ as ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ ins ∪ as ⇒ (x+1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ ins ∪ as ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),N,r) ∈ outs ∪ as ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ outs ∪ as ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ outs ∪ as ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ outs ∪ as ⇒ (x+1,y) ∈ area) ∧
    (∀p d r. (p,d,r) ∈ ins ∧ sub_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ outs) ∧
    (∀p d r. (p,d,r) ∈ outs ∧ add_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ ins) ∧
    (∀x y r. ((x,y),r) ∈ as ⇒ ∀q. ((x,y),q) ∉ ins ∧ ((x,y),q) ∉outs)
Proof
  simp [circ_mod_wf_def] \\ rpt AP_TERM_TAC
  \\ `∀P. (∀d. P d) ⇔ P N ∧ P S ∧ P E ∧ P W` by
    (strip_tac \\ eq_tac \\ strip_tac \\ TRY Cases \\ metis_tac [])
  \\ pop_assum (rw o single) \\ rw [FORALL_PROD, GSYM int_sub]
  \\ metis_tac []
QED

Definition circ_area_def:
  circ_area area ins outs n =
    if n MOD 60 < 30 then
      base_area area DIFF
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {N;S} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {E;W} }) ∪
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {E;W} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {N;S} })
    else
      base_area area DIFF
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {E;W} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {N;S} }) ∪
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {N;S} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {E;W} })
End

Definition circ_io_area_def:
  circ_io_area outs =
    U { io_box (x,y) | ∃r. ((x,y),r) ∈ outs }
End

Definition circ_output_area_def:
  circ_output_area outs n =
    circ_io_area (if n MOD 60 = 29 then outs ∩ is_ns else
                  if n MOD 60 = 59 then outs ∩ is_ew else {})
End

Definition io_gate_def:
  io_gate E =
   [[F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;T;F;F;T;F];
    [F;F;F;F;F;F;F;F;F;T];
    [F;F;F;F;F;T;F;F;F;T];
    [F;F;F;F;F;F;T;T;T;T];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F]] ∧
  io_gate W =
   [[F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [T;T;T;T;F;F;F;F;F;F];
    [T;F;F;F;T;F;F;F;F;F];
    [T;F;F;F;F;F;F;F;F;F];
    [F;T;F;F;T;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F]] ∧
  io_gate N =
   [[F;F;T;T;T;F;F;F;F;F];
    [F;T;F;F;T;F;F;F;F;F];
    [F;F;F;F;T;F;F;F;F;F];
    [F;F;F;F;T;F;F;F;F;F];
    [F;T;F;T;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F]] ∧
  io_gate S =
   [[F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;T;F;T;F];
    [F;F;F;F;F;T;F;F;F;F];
    [F;F;F;F;F;T;F;F;F;F];
    [F;F;F;F;F;T;F;F;T;F];
    [F;F;F;F;F;T;T;T;F;F]]
End

Definition from_row_def:
  from_row (x,y) [] = {} ∧
  from_row (x,y) (F::xs) = from_row (x+1:int,y:int) xs ∧
  from_row (x,y) (T::xs) = {(x,y)} ∪ from_row (x+1,y) xs
End

Definition from_rows_def:
  from_rows (x,y) [] = {} ∧
  from_rows (x,y) (row :: rows) = from_row (x,y) row ∪ from_rows (x,y+1) rows
End

Theorem from_rows_EMPTY:
  ∀x y.
    EVERY (EVERY (λx. x = F)) bools ⇒
    from_rows (x,y) bools = ∅
Proof
  Induct_on ‘bools’ \\ gvs [from_rows_def,SF SFY_ss]
  \\ Induct \\ gvs [from_row_def]
QED

Definition lwss_as_set_def:
  lwss_as_set (x,y) d = from_rows (x,y) (io_gate d)
End

Definition lwss_at_def:
  lwss_at n ((x,y),d,r) =
    if r (n DIV 60) then
      lwss_as_set (75 * x - 5, 75 * y - 5) d
    else
      {}
End

Definition circ_io_lwss_def:
  circ_io_lwss ins n =
    if n MOD 60 = 29 then
      U (IMAGE (lwss_at n) (ins ∩ is_ns) )
    else if n MOD 60 = 59 then
      U (IMAGE (lwss_at n) (ins ∩ is_ew) )
    else
      {}
End

Definition circ_mod_def:
  circ_mod area ins outs as n =
    <| area           := circ_area area ins outs n ;
       deletions      := circ_output_area outs n ;
       insertions     := circ_io_lwss ins n ;
       assert_area    := circ_output_area (outs ∪ as) n ;
       assert_content := circ_io_lwss (outs ∪ as) n |>
End

Theorem circ_mod_empty[simp]:
  circ_mod ∅ ∅ ∅ ∅ = empty_mod
Proof
  rw [empty_mod_def, Once FUN_EQ_THM, circ_mod_def]
  \\ simp [EXTENSION, circ_mod_def, circ_area_def, base_area_def,
    circ_output_area_def, circ_io_area_def, circ_io_lwss_def]
QED

Theorem IN_from_row:
  ∀row i j x y.
    (x,y) ∈ from_row (i,j) row ⇔
    y = j ∧ ∃n. oEL n row = SOME T ∧ x = i + &n
Proof
  Induct \\ gvs [from_row_def,oEL_def]
  \\ rw [] \\ gvs [from_row_def,oEL_def]
  \\ Cases_on ‘h’ \\ gvs [from_row_def,oEL_def]
  \\ Cases_on ‘y = j’ \\ gvs []
  \\ eq_tac \\ rw []
  >- (qexists_tac ‘0’ \\ gvs [])
  >- (qexists_tac ‘n+1’ \\ gvs [] \\ intLib.COOPER_TAC)
  \\ gvs [AllCaseEqs()]
  >- (qexists_tac ‘n-1’ \\ gvs [] \\ intLib.COOPER_TAC)
  >- (qexists_tac ‘n+1’ \\ gvs [] \\ intLib.COOPER_TAC)
  >- (qexists_tac ‘n-1’ \\ gvs [] \\ intLib.COOPER_TAC)
QED

Theorem IN_from_rows:
  ∀rows i j x y.
    (x,y) ∈ from_rows (i,j) rows ⇔
      ∃dx dy row.
        x = i + & dx ∧ y = j + & dy ∧
        oEL dy rows = SOME row ∧
        oEL dx row = SOME T
Proof
  Induct \\ gvs [from_rows_def] \\ gvs [oEL_def,IN_from_row]
  \\ rpt gen_tac \\ eq_tac \\ strip_tac
  >- (pop_assum $ irule_at Any \\ qrefinel [‘_’,‘0’] \\ gvs [])
  >- (qrefinel [‘dx’,‘1+dy’] \\ gvs [] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘dy’ \\ gvs []
  \\ rpt $ pop_assum $ irule_at Any
  \\ intLib.COOPER_TAC
QED

Theorem from_rows_translate:
  ∀a b. (x+a,y+b) ∈ from_rows (i+a,j+b) rows ⇔ (x,y) ∈ from_rows (i,j) rows
Proof
  rw [IN_from_rows] \\ ntac 3 (AP_TERM_TAC \\ ABS_TAC)
  \\ eq_tac \\ rw [] \\ ARITH_TAC
QED

Theorem io_gate_lenth:
  LENGTH (io_gate d) = 10 ∧
  ∀row. MEM row (io_gate d) ⇒ LENGTH row = 10
Proof
  Cases_on ‘d’ \\ gvs [io_gate_def, SF DNF_ss]
QED

Theorem lwss_at_imp_io_box:
  (x,y) ∈ lwss_at n ((i,j),r) ⇒ (x,y) ∈ io_box (i,j)
Proof
  PairCases_on ‘r’ \\ rw [lwss_at_def,io_box_def, lwss_as_set_def]
  \\ gvs [box_def,IN_from_rows]
  \\ qexists_tac ‘dx + 1’
  \\ qexists_tac ‘dy + 1’
  \\ qsuff_tac ‘dx < 10 ∧ dy < 10’ >- intLib.COOPER_TAC
  \\ gvs [oEL_THM]
  \\ rename [‘io_gate d’]
  \\ strip_assume_tac io_gate_lenth
  \\ gvs [MEM_EL,PULL_EXISTS]
QED

Theorem IN_io_box_io_box:
  (a0,a1) ∈ io_box (x,y) ⇒ ((a0,a1) ∈ io_box (x1,y1) ⇔ x = x1 ∧ y = y1)
Proof
  gvs [io_box_def,box_def] \\ intLib.COOPER_TAC
QED

Theorem mods_wf_circ_mod:
  circ_mod_wf area ins outs as ⇒
  mods_wf (circ_mod area ins outs as)
Proof
  rw [circ_mod_wf_def_old]
  \\ gvs [mods_wf_def,mod_wf_def,circ_mod_def] \\ rw []
  >-
   (gvs [circ_output_area_def,circ_area_def] \\ rw []
    \\ gvs [circ_io_area_def,SUBSET_DEF,PULL_EXISTS]
    \\ gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD]
    \\ metis_tac [])
  >-
   (gvs [circ_output_area_def,circ_area_def] \\ rw []
    \\ gvs [circ_io_area_def,SUBSET_DEF,PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ PairCases_on ‘r’ \\ gvs []
    >- (gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD] \\ metis_tac [])
    >-
     (disj1_tac
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ rename [‘a ∈ io_box (x,y)’] \\ PairCases_on ‘a’
      \\ ‘(x,y − 1) ∈ area ∧ (x,y + 1) ∈ area’ by
        (gvs [IN_DEF,is_ns_def,SF DNF_ss] \\ res_tac \\ gvs [])
      \\ drule IN_io_box_io_box
      \\ disch_then (fn th => rewrite_tac [th])
      \\ reverse conj_tac >- metis_tac []
      \\ gvs [base_area_def,PULL_EXISTS,box_def,io_box_def]
      \\ Cases_on ‘j < 6’
      >-
       (qexists_tac ‘x’ \\ qexists_tac ‘y-1’ \\ gvs []
        \\ qexists_tac ‘75 - 6 + i’
        \\ qexists_tac ‘150 - 6 + j’
        \\ intLib.COOPER_TAC)
      >-
       (qexists_tac ‘x’ \\ qexists_tac ‘y+1’ \\ gvs []
        \\ qexists_tac ‘75 - 6 + i’
        \\ qexists_tac ‘j - 6’
        \\ intLib.COOPER_TAC))
    >- (gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD] \\ metis_tac [])
    >-
     (disj1_tac
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ rename [‘a ∈ io_box (x,y)’] \\ PairCases_on ‘a’
      \\ ‘(x − 1,y) ∈ area ∧ (x + 1,y) ∈ area’ by
        (gvs [IN_DEF,is_ew_def,SF DNF_ss] \\ res_tac \\ gvs [])
      \\ drule IN_io_box_io_box
      \\ disch_then (fn th => rewrite_tac [th])
      \\ reverse conj_tac >- metis_tac []
      \\ gvs [base_area_def,PULL_EXISTS,box_def,io_box_def]
      \\ Cases_on ‘i < 6’
      >-
       (qexists_tac ‘x-1’ \\ qexists_tac ‘y’ \\ gvs []
        \\ qexists_tac ‘150 - 6 + i’
        \\ qexists_tac ‘75 - 6 + j’
        \\ intLib.COOPER_TAC)
      >-
       (qexists_tac ‘x+1’ \\ qexists_tac ‘y’ \\ gvs []
        \\ qexists_tac ‘i - 6’
        \\ qexists_tac ‘75 - 6 + j’
        \\ intLib.COOPER_TAC)))
  \\ rw [circ_io_lwss_def]
  \\ simp [circ_io_area_def,circ_output_area_def,
           SUBSET_DEF,FORALL_PROD,PULL_EXISTS,EXISTS_PROD]
  \\ rewrite_tac [GSYM AND_IMP_INTRO]
  \\ rpt gen_tac
  \\ rpt $ disch_then assume_tac
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ imp_res_tac lwss_at_imp_io_box \\ gvs []
QED

Definition circuit_run_def:
  circuit_run area ins outs as init ⇔
    run (circ_mod area ins outs as) init ∧
    circ_mod_wf area ins outs as
End

Theorem circuit_run_empty:
  circuit_run ∅ ∅ ∅ ∅ ∅
Proof
  simp [circuit_run_def, run_empty_mod, circ_mod_wf_def]
QED

Definition circuit_def:
  circuit area ins outs as init ⇔
    circuit_run (set area) (set ins) (set outs) (set as) init ∧
    ALL_DISTINCT area ∧
    ALL_DISTINCT (MAP FST ins) ∧
    ALL_DISTINCT (MAP FST outs) ∧
    ALL_DISTINCT (MAP FST as)
End

Theorem mod_steps_add:
  ∀k c n s1 s2.
    mod_steps (l + k) c n s1 s2 ⇔
    ∃s3. mod_steps k c n s1 s3 ∧ mod_steps l c (n + k) s3 s2
Proof
  Induct_on ‘k’ \\ gvs []
  \\ once_rewrite_tac [mod_steps_def] \\ gvs [ADD_CLAUSES]
  \\ gvs [mod_steps_def] \\ gvs [PULL_EXISTS,ADD1]
  \\ metis_tac []
QED

Theorem run_to_le:
  ∀k k0 c s t. run_to k c s t ∧ k0 ≤ k ⇒ ∃u. run_to k0 c s u
Proof
  rw [] \\ gvs [LESS_EQ_EXISTS,run_to_def]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [mod_steps_add] \\ rw []
  \\ first_x_assum $ irule_at Any
QED

Theorem run_to_imp_run:
  ∀k c s.
    (∀n. ∃t. run_to (k * n) c s t) ∧ k ≠ 0 ⇒
    run c s
Proof
  rw [run_def] \\ rename [‘run_to k1’]
  \\ last_x_assum $ qspec_then ‘k1’ strip_assume_tac
  \\ irule run_to_le
  \\ pop_assum $ irule_at Any \\ gvs []
QED

Definition list_disjoint_def:
  list_disjoint xs ys ⇔ EVERY (λx. ~ MEM x ys) xs
End

Definition io_compatible_def:
  io_compatible area ins [] = T ∧
  io_compatible area ins (((x,y),d,_)::rest) =
    (io_compatible area ins rest ∧
     if x % 2 = 0 then
       MEM (x,y-1) area ∧ MEM (x,y+1) area ⇒
       case ALOOKUP ins (x,y) of
       | NONE => F
       | SOME (d1,_) => d = d1
     else
       MEM (x-1,y) area ∧ MEM (x+1,y) area ⇒
       case ALOOKUP ins (x,y) of
       | NONE => F
       | SOME (d1,_) => d = d1)
End

Definition no_overlap_def:
  no_overlap area1 ins1 outs1 as1
             area2 ins2 outs2 as2 ⇔
    list_disjoint area1 area2 ∧
    list_disjoint (MAP FST ins1) (MAP FST ins2) ∧
    list_disjoint (MAP FST outs1) (MAP FST outs2) ∧
    list_disjoint (MAP FST as1) (MAP FST as2) ∧
    let area = area1 ++ area2 in
    let ins  = ins1  ++ ins2  in
    let outs = outs1 ++ outs2 in
      io_compatible area ins outs ∧
      io_compatible area outs ins
End

(*
Theorem circuit_compose:
  circuit area1 ins1 outs1 as1 init1 ∧
  circuit area2 ins2 outs2 as2 init2
  ⇒
  no_overlap area1 ins1 outs1 as1
             area2 ins2 outs2 as2
  ⇒
  circuit (area1 ++ area2)
          (ins1  ++  ins2)
          (outs1 ++ outs2)
          (as1   ++   as2)
          (init1 ∪  init2)
Proof
  cheat
QED

Theorem circuit_internalise:
  ∀ins1 ins2 x outs1 outs2.
    circuit area (ins1 ++ x ++ ins2) (outs1 ++ x ++ outs2) as init ⇒
    circuit area (ins1 ++      ins2) (outs1 ++      outs2) as init
Proof
  cheat
QED
*)



Theorem circ_area_diff:
  circ_mod_wf area ins outs as ∧
  m ⊆ ins ∧
  m ⊆ outs ⇒
  circ_area area ins outs x =
  circ_area area (ins DIFF m) (outs DIFF m) x
Proof
  cheat
QED

Triviality circuit_run_internalise_lemma:
  ∀m area ins outs as init.
    circuit_run area ins outs as init ∧ m ⊆ ins ∧ m ⊆ outs ∧
    (¬ (m ⊆ is_ns) ⇒ m ⊆ is_ew) ⇒
    circuit_run area (ins DIFF m) (outs DIFF m) as init
Proof
  gvs [circuit_run_def] \\ rpt gen_tac \\ strip_tac
  \\ dxrule to_del_io_run
  \\ disch_then $ qspec_then ‘circ_io_area m’ mp_tac
  \\ impl_tac
  >- cheat
  \\ qsuff_tac
     ‘del_io (circ_io_area m) (circ_mod area ins outs as) =
      circ_mod area (ins DIFF m) (outs DIFF m) as’
  >- (gvs [] \\ rw [] \\ gvs [circ_mod_wf_def, SF SFY_ss, SF DNF_ss])
  \\ gvs [FUN_EQ_THM] \\ gvs [del_io_def,del_io_mod_def,circ_mod_def]
  \\ gen_tac \\ IF_CASES_TAC
  \\ gvs [fetch "-" "modifier_component_equality"]
  \\ irule_at Any circ_area_diff
  \\ first_assum $ irule_at $ Pos hd \\ simp []
  >-
   (pop_assum mp_tac
    \\ simp [Once circ_output_area_def]
    \\ reverse $ rpt (IF_CASES_TAC \\ gvs [])
    \\ simp [circ_output_area_def]
    \\ simp [circ_io_lwss_def]
    \\ cheat)
  \\ cheat
QED

Theorem is_ns_not_is_ew:
  is_ns x ⇔ ~ is_ew x
Proof
  PairCases_on ‘x’ \\ gvs [] \\ Cases_on ‘x2’ \\ gvs [is_ns_def,is_ew_def]
QED

Theorem circuit_run_internalise:
  ∀m area ins outs as init.
    circuit_run area ins outs as init ∧ m ⊆ ins ∧ m ⊆ outs ⇒
    circuit_run area (ins DIFF m) (outs DIFF m) as init
Proof
  rpt strip_tac
  \\ ‘∃m1 m2. m = m1 ∪ m2 ∧ DISJOINT m1 m2 ∧ m1 ⊆ is_ns ∧ m2 ⊆ is_ew’ by
    (qexists_tac ‘m ∩ is_ns’
     \\ qexists_tac ‘m ∩ is_ew’
     \\ gvs [SUBSET_DEF]
     \\ gvs [IN_DISJOINT,EXTENSION]
     \\ gvs [IN_DEF,is_ns_not_is_ew]
     \\ metis_tac [])
  \\ gvs [DIFF_UNION]
  \\ irule circuit_run_internalise_lemma
  \\ irule_at Any circuit_run_internalise_lemma \\ simp []
  \\ gvs [IN_DISJOINT,SUBSET_DEF]
  \\ metis_tac []
QED

Definition next_to_def:
  next_to (x1,y1) (x2,y2) ⇔
    x1 = x2 ∧ ABS (y1 - y2) = 2 ∨
    y1 = y2 ∧ ABS (x1 - x2) = 2
End

Definition mid_point_def:
  midpoint (x1,y1) (x2,y2) = ((x1+x2) / 2:int, (y1+y2) / 2:int)
End

Definition ports_of_def:
  ports_of s = IMAGE (λ(xy,rest). (xy:int # int)) s
End

Definition iunion_def:
  iunion f = U {f z | z | T}
End

Theorem mem_iunion[simp]:
  x ∈ iunion f ⇔ ∃a. x ∈ f a
Proof
  simp [iunion_def, PULL_EXISTS]
QED

Theorem iunion_empty[simp]:
  iunion (λ_. ∅) = ∅
Proof
  simp [EXTENSION]
QED

Theorem circuit_run_compose_bigunion:
  (* each element in the family must be a circuit_run *)
  (∀x. circuit_run (area x) (ins x) (outs x) (as x) (init x)) ∧
  (∀x1 x2. x1 ≠ x2 ⇒
    (* all areas must be disjoint *)
    DISJOINT (area x1) (area x2) ∧
    (* on a border between two areas, in/out ports must be matching, if they exist *)
    ∀p d r.
      ((p,d,r) ∈ ins x1 ∧ sub_pt p (dir_to_xy d) ∈ area x2 ⇒ (p,d,r) ∈ outs x2) ∧
      ((p,d,r) ∈ outs x1 ∧ add_pt p (dir_to_xy d) ∈ area x2 ⇒ (p,d,r) ∈ ins x2))
  ⇒
  circuit_run (iunion area) (iunion ins) (iunion outs) (iunion as) (iunion init)
Proof
  cheat
QED

Definition translate_set_def:
  translate_set x s a ⇔ sub_pt a x ∈ s
End

Theorem translate_set_empty[simp]:
  translate_set p ∅ = ∅
Proof
  simp [EXTENSION, pairTheory.FORALL_PROD, translate_set_def, IN_DEF]
QED

Theorem mem_translate_set[simp]:
  a ∈ translate_set x s ⇔ sub_pt a x ∈ s
Proof
  simp [IN_DEF, translate_set_def]
QED

Definition translate_mod_def:
  translate_mod p mod =
    <|area           := translate_set p mod.area;
      deletions      := translate_set p mod.deletions;
      insertions     := translate_set p mod.insertions;
      assert_area    := translate_set p mod.assert_area;
      assert_content := translate_set p mod.assert_content|>
End

Definition translate_mods_def:
  translate_mods p mod n = translate_mod p (mod n)
End

Theorem translate_mods_empty[simp]:
  translate_mods p empty_mod = empty_mod
Proof
  rw [Once FUN_EQ_THM, translate_mods_def, empty_mod_def, translate_mod_def]
QED

(*
Definition circuit_spec_def:
  circuit_spec area ins outs init ⇔
    ∀s1.
      (∀xy d p. (xy,d,p) ∈ ins ⇒ p (s1 xy)) ⇒
      ∃s2.
        (∀xy d p. (xy,d,p) ∈ ins ⇒ s1 xy = s2 xy) ∧
        (∀xy. xy ∉ IMAGE FST outs ⇒ s1 xy = s2 xy) ∧
        (∀xy d p. (xy,d,p) ∈ outs ⇒ p (s2 xy)) ∧
        circuit_run area
          { (xy,d,s2 xy) | ∃p. (xy,d,p) ∈ ins }
          { (xy,d,s2 xy) | ∃p. (xy,d,p) ∈ outs } {}
          init
End

Theorem circuit_spec_compose:
  circuit_spec area1 ins1 (outs1 ∪ m) init1 ∧
  circuit_spec area2 (ins2 ∪ m) outs2 init2 ∧
  DISJOINT area1 area2 ∧
  DISJOINT (IMAGE FST ins1) (IMAGE FST m) ∧
  DISJOINT (IMAGE FST ins2) (IMAGE FST m) ∧
  DISJOINT (IMAGE FST ins1) (IMAGE FST ins2) ∧
  DISJOINT (IMAGE FST outs1) (IMAGE FST outs2) ∧
  (∀xy r1 r2. (xy,r1) ∈ ins2 ∧ (xy,r2) ∈ outs1 ⇒ r1 = r2)
  ⇒
  circuit_spec (area1 ∪ area2) (ins1 ∪ ins2) (outs1 ∪ outs2) (init1 ∪ init2)
Proof
  gvs [circuit_spec_def]
  \\ rpt strip_tac
  \\ gvs [SF DNF_ss, GSYM CONJ_ASSOC]
  \\ last_x_assum drule
  \\ strip_tac
  \\ qabbrev_tac ‘s12 = λxy. if xy ∈ IMAGE FST ins2 then s1 xy else s2 xy’
  \\ last_x_assum $ qspec_then ‘s12’ mp_tac
  \\ impl_tac >-
   (gvs [Abbr‘s12’,EXISTS_PROD,FORALL_PROD, SF SFY_ss]
    \\ rw [] \\ gvs [] \\ res_tac \\ gvs []
    \\ gvs [IN_DISJOINT,FORALL_PROD] \\ metis_tac [])
  \\ strip_tac
  \\ rename [‘∀xy d p. (xy,d,p) ∈ outs2 ⇒ p (sN xy)’]
  \\ qexists_tac ‘sN’
  \\ gvs [SF SFY_ss]
  \\ conj_tac
  >- (rpt strip_tac \\ cheat)
  \\ conj_tac
  >- (rpt strip_tac
      \\ first_x_assum drule \\ gvs [Abbr‘s12’]
      \\ rw [] \\ gvs [EXISTS_PROD] \\ gvs [])
  \\ conj_tac
  >- (rpt strip_tac \\ cheat)
  \\ conj_tac
  >- (rpt strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ ‘s12 xy = sN xy’ by cheat
      \\ pop_assum $ rewrite_tac o single o GSYM
      \\ rw [Abbr‘s12’]
      \\ Cases_on ‘x’ \\ gvs []
      \\ ‘r = (d,p)’ by metis_tac [] \\ gvs [SF SFY_ss])
  \\ cheat
QED
*)

(* --- compose all experiment --- *)

(*
   The idea here is that we go about building and verifying a circuit
   in a different way:

    1. We create a set consisting of all of the gates. For each gate,
       we need to have a blist_simulation_ok theorem.

    2. We then prove that the set of gates is well connected (every
       out port has a corresponding in with the same direction) and
       has no overlapping gates (all gate areas are disjoint). Let's
       call this property ‘conected’.

    3. The connected property from point 2 implies that there is bool
       sequence that describes the signal passing through each in/out
       port in the set of gets. In other words, we know:

         ∀gates.
           conected gates ⇒
           ∃s. circuit_run UNIV {} {}
                 { (xy, d, s xy) | (xy,d) ∈ ports_of gates }
                 (make_init_of gates)

       Note that ins and outs are empty and all the information is
       only asserts, i.e., it is a complete circuit that runs directly
       in the GOL semantics without insertions/deletions.

    4. The remaining task is to prove theorems that derive facts
       about what is passing through these io/out ports. For example,
       for an and-gate we might like to prove

         circuit_run UNIV {} {}
           { (xy, d, s xy) | (xy,d) ∈ ports_of gates }
           (make_init_of gates)
         ⇒
         ∀n. s (12,11) (n+5) = s (12,13) n ∧ s (11,12) n

       which can be read as saying that the output at (12,11) at clock
       n+5 is the bool-and of s (12,11) and s (11,12) at clock n. It's
       important that these descriptions (on the left-hand side of ⇒):

        - are really simple direct statements in the logic

        - don't need to distinguish in from out

        - can easily be about certain ranges of ‘n’ rather than
          entire sequences.

       For each individual gate, we get an automatic theorem that
       gives the information is present in current circuit theorems
       coming out of the simulation.

       Note that all properties we prove about the gate from here
       onwards have exactly the same shape on the left-hand side of
       the implication, i.e.,

         circuit_run UNIV {} {}
           { (xy, d, s xy) | (xy,d) ∈ ports_of gates }
           (make_init_of gates)
         ⇒
         ...

       which means that we can compose them easily. In practice, we
       can define a constant such that our theorems are of the form:

         gol_in_gol_ports gates s
         ⇒
         ...

    5. A major objective is now to prove a theorem of the form:

         gol_in_gol_ports (all_gol_in_gol_gates init) s
         ⇒
         ∀x y n.
           (x,y) ∈ steps n init
           ⇔
           s (x * 21 * 150 + 123, y * 21 * 150 + 45) (n * 60 * period)

       (I made up some of the magic numbers 123 and 45 above.)

*)

val _ = export_theory();
