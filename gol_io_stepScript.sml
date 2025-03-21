(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open HolKernel bossLib boolLib Parse;
open pred_setTheory pairTheory dep_rewrite arithmeticTheory listTheory
     alistTheory rich_listTheory combinTheory gol_rulesTheory
     integerTheory intLib gol_simTheory gol_lemmasTheory;

val _ = new_theory "gol_io_step";

Overload LLOOKUP = “λl n. oEL n l”;
Overload "U" = “BIGUNION”;

fun cong_tac n = ntac n $ FIRST [AP_THM_TAC, AP_TERM_TAC, ABS_TAC, BINOP_TAC, MK_COMB_TAC]

(* runs *)

Datatype:
  modifier =
    <| area           : (int # int) set ;
       deletions      : (int # int) set ;
       insertions     : (int # int) set ;
       assert_area    : (int # int) set ;
       assert_content : (int # int) set |>
End

Definition io_step_def:
  io_step c s1 s3 ⇔
    ∃s2.
      infl s1 ⊆ c.area ∧
      step s1 = s2 ∧
      s2 ∩ c.assert_area = c.assert_content ∧
      s3 = c.insertions ∪ (s2 DIFF c.deletions)
End

Theorem io_step_univ:
  c.area = UNIV ∧ c.insertions = EMPTY ∧ c.deletions = EMPTY
  ⇒
  (io_step c s1 s2
   ⇔
   step s1 = s2 ∧
   s2 ∩ c.assert_area = c.assert_content)
Proof
  gvs [io_step_def] \\ metis_tac []
QED

Definition io_steps_def:
  io_steps 0 c n s1 s2 = (s1 = s2) ∧
  io_steps (SUC k) c n s1 s3 =
     ∃s2. io_step (c n) s1 s2 ∧ io_steps k c (n+1:num) s2 s3
End

Definition run_to_def:
  run_to k c s t ⇔ io_steps k c 0 s t
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

Theorem io_steps_compose:
  ∀c1 c2 k n s1 s2 t1 t2.
    disjoint_mods c1 c2 ∧
    mods_wf c1 ∧
    mods_wf c2 ∧
    io_steps k c1 n s1 t1 ∧
    io_steps k c2 n s2 t2 ⇒
    io_steps k (join c1 c2) n (s1 ∪ s2) (t1 ∪ t2)
Proof
  gen_tac \\ gen_tac \\ Induct \\ gvs [io_steps_def]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum drule_all
  \\ rename [‘_ (u1 ∪ u2) (_ ∪ _)’]
  \\ disch_then $ irule_at Any
  \\ gvs [io_step_def,join_def]
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

Theorem io_step_compose_bigunion:
  ∀n cs s t.
    (∀x y. x ∈ dom ∧ y ∈ dom ∧ x ≠ y ⇒ disjoint_mods (cs x) (cs y)) ∧
    (∀i. i ∈ dom ⇒ mods_wf (cs i) ∧ io_step (cs i n) (s i) (t i))
    ⇒
    io_step (join_all (dom, cs) n) (U { s i | i ∈ dom }) (U { t i | i ∈ dom })
Proof
  rw [io_step_def, join_all_def, infl_bigunion]
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

Theorem io_steps_compose_bigunion:
  ∀k cs n s t.
    (∀x y. x ∈ dom ∧ y ∈ dom ∧ x ≠ y ⇒ disjoint_mods (cs x) (cs y)) ∧
    (∀i. i ∈ dom ⇒ mods_wf (cs i) ∧ io_steps k (cs i) n (s i) (t i))
    ⇒
    io_steps k (join_all (dom, cs)) n (U { s i | i ∈ dom }) (U { t i | i ∈ dom })
Proof
  Induct \\ gvs [io_steps_def]
  >- (simp [Once EXTENSION, Once EXTENSION] \\ metis_tac [])
  \\ metis_tac [io_step_compose_bigunion]
QED

Theorem run_compose_bigunion:
  ∀dom cs s.
    (∀x y. x ∈ dom ∧ y ∈ dom ∧ x ≠ y ⇒ disjoint_mods (cs x) (cs y)) ∧
    (∀i. i ∈ dom ⇒ mods_wf (cs i) ∧ run (cs i) (s i))
    ⇒
    run (join_all (dom, cs)) (U { s i | i ∈ dom })
Proof
  rw [run_def, run_to_def]
  \\ `∀i. i ∈ dom ⇒ ∃t. io_steps k (cs i) 0 (s i) t` by metis_tac []
  \\ metis_tac [io_steps_compose_bigunion]
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
    io_steps k c n s t ∧
    can_assert p c
    ⇒
    io_steps k (assert p c) n s t
Proof
  Induct
  \\ gvs [io_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [io_step_def,assert_def,assert_mod_def]
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
    io_steps k c n s t ∧
    can_assert p c
    ⇒
    io_steps k (del_io p c) n s t
Proof
  Induct
  \\ gvs [io_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [io_step_def,del_io_def,del_io_mod_def]
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

Theorem io_steps_clear_mods:
  ∀k c n s t.
    io_steps k c n s t ∧
    can_clear c
    ⇒
    io_steps k (clear_mods c) n s t
Proof
  Induct
  \\ gvs [io_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ gvs [io_step_def,can_clear_def,clear_mods_def,clear_mod_def]
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
  \\ drule_all io_steps_clear_mods
  \\ disch_then $ irule_at Any
QED

val _ = export_theory();
