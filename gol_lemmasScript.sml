(*
  Lemmas about GOL semantics and definition of area of influence (infl)
*)
open HolKernel bossLib boolLib Parse;
open pred_setTheory pairTheory dep_rewrite arithmeticTheory listTheory
     alistTheory rich_listTheory combinTheory gol_rulesTheory
     integerTheory intLib;

val _ = new_theory "gol_lemmas";

Overload LLOOKUP = “λl n. oEL n l”;
Overload "U" = “BIGUNION”;

fun cong_tac n = ntac n $ FIRST [AP_THM_TAC, AP_TERM_TAC, ABS_TAC, BINOP_TAC, MK_COMB_TAC]

(* properties about adj *)

Theorem adj_eq:
  adj x y = { (x1,y1) | ABS (x - x1) ≤ 1 ∧ ABS (y - y1) ≤ 1 } DIFF {(x,y)}
Proof
  gvs [EXTENSION]
  \\ gvs [adj_def,FORALL_PROD] \\ rw []
  \\ intLib.COOPER_TAC
QED

Theorem adj_set:
  adj x y = set [(x-1,y-1);(x,y-1);(x+1,y-1);(x-1,y);(x+1,y);(x-1,y+1);(x,y+1);(x+1,y+1)]
Proof
  gvs [EXTENSION,adj_def] \\ rw [] \\ eq_tac \\ rw []
  \\ intLib.COOPER_TAC
QED

Theorem finite_adj:
  FINITE (adj x y)
Proof
  rewrite_tac [adj_set] \\ simp []
QED

(* properties of live_adj *)

Definition b2n_def[simp]:
  b2n T = 1n ∧ b2n F = 0
End

Theorem b2n_eq[simp]:
  (b2n b = 0 ⇔ ~b) ∧
  (b2n b = 1 ⇔ b)
Proof
  Cases_on ‘b’ \\ fs []
QED

Theorem live_adj_eq:
  live_adj (s:state) i j =
    b2n (s (i-1, j-1)) + b2n (s (i, j-1)) + b2n (s (i+1, j-1)) +
    b2n (s (i-1, j+0)) +                    b2n (s (i+1, j+0)) +
    b2n (s (i-1, j+1)) + b2n (s (i, j+1)) + b2n (s (i+1, j+1))
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [live_adj_def]
  \\ rewrite_tac [adj_set]
  \\ ‘∀xs. s ∩ set xs = set (FILTER s xs)’
        by gvs [EXTENSION,MEM_FILTER,IN_DEF]
  \\ asm_rewrite_tac []
  \\ DEP_REWRITE_TAC [ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ conj_tac
  >-
   (irule FILTER_ALL_DISTINCT
    \\ gvs [] \\ intLib.COOPER_TAC)
  \\ rw [] \\ gvs []
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
  gvs [live_adj_eq,IN_DEF, AC CONJ_COMM CONJ_ASSOC]
QED

(* area of influence *)

Definition infl_def: (* influence *)
  infl s (i,j) ⇔ live_adj s i j ≠ 0 ∨ (i,j) ∈ s
End

Theorem infl_thm:
  (i,j) ∈ infl s ⇔
    (i-1, j-1) ∈ s ∨ (i, j-1) ∈ s ∨ (i+1, j-1) ∈ s ∨
    (i-1, j  ) ∈ s ∨ (i, j  ) ∈ s ∨ (i+1, j  ) ∈ s ∨
    (i-1, j+1) ∈ s ∨ (i, j+1) ∈ s ∨ (i+1, j+1) ∈ s
Proof
  fs [IN_DEF,infl_def]
  \\ Cases_on ‘s (i,j)’ \\ fs [live_adj_eq]
  \\ fs [AC DISJ_COMM DISJ_ASSOC]
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

Theorem IN_COMPL_infl_COMPL:
  (x,y) ∈ COMPL (infl (COMPL s)) ⇔
  { (x-1,y-1); (x,y-1); (x+1,y-1);
    (x-1,y  ); (x,y  ); (x+1,y  );
    (x-1,y+1); (x,y+1); (x+1,y+1) } ⊆ s
Proof
  gvs [] \\ simp [IN_DEF,infl_def]
  \\ gvs [live_adj_eq,IN_DEF]
  \\ eq_tac \\ rw []
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

Theorem disjoint_live_adj:
  DISJOINT (infl y) (infl s) ∧ (x0,x1) ∈ s ⇒
  live_adj y x0 x1 = 0
Proof
  simp [live_adj_eq_0]
  \\ CCONTR_TAC \\ gvs []
  \\ drule_all DISJOINT_infl
  \\ intLib.COOPER_TAC
QED

Theorem IMP_infl_subset:
  s ⊆ COMPL (infl (COMPL t)) ⇒ infl s ⊆ t
Proof
  gvs [SUBSET_DEF] \\ gvs [IN_DEF, infl_def, FORALL_PROD]
  \\ gvs [live_adj_eq,IN_DEF] \\ rw []
  \\ Cases_on ‘s (p_1,p_2)’ \\ gvs []
  \\ last_x_assum drule \\ gvs [integerTheory.INT_SUB_ADD]
  \\ gvs [intLib.COOPER_PROVE “m + k - k:int = m”]
QED

Theorem infl_compose:
  infl s ∩ infl t = ∅ ⇒
  step (s ∪ t) = step s ∪ step t
Proof
  fs [EXTENSION,FORALL_PROD,IN_step]
  \\ rw [IN_DEF,infl_def]
  \\ first_x_assum (qspecl_then [‘p_1’,‘p_2’] mp_tac)
  \\ Cases_on ‘s (p_1,p_2)’ \\ fs [] \\ rw []
  \\ fs [live_adj_eq,IN_DEF]
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
  \\ fs [live_adj_eq,IN_DEF]
QED

Theorem infl_union:
  infl (s ∪ s') = infl s ∪ infl s'
Proof
  fs [EXTENSION,IN_DISJOINT,FORALL_PROD] \\ rw []
  \\ eq_tac \\ fs [infl_thm]
  \\ rw [] \\ fs []
QED

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
  gvs [live_adj_def]
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
  \\ gvs [adj_eq]
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
  \\ gvs [PULL_EXISTS,IN_step]
  \\ reverse $ rw [IN_DEF,infl_def]
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

val _ = export_theory();
