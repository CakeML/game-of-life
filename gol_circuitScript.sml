(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open HolKernel bossLib boolLib Parse;
open pred_setTheory pairTheory dep_rewrite arithmeticTheory listTheory
     alistTheory rich_listTheory combinTheory gol_rulesTheory
     integerTheory intLib gol_simTheory gol_lemmasTheory
     gol_io_stepTheory;

val _ = new_theory "gol_circuit";

Overload LLOOKUP = “λl n. oEL n l”;
Overload "U" = “BIGUNION”;

fun cong_tac n = ntac n $ FIRST [AP_THM_TAC, AP_TERM_TAC, ABS_TAC, BINOP_TAC, MK_COMB_TAC]

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

Theorem is_ns_not_is_ew:
  is_ns x ⇔ ~ is_ew x
Proof
  PairCases_on ‘x’ \\ gvs [is_ns_def, is_ew_def] \\ Cases_on ‘x1’ \\ simp []
QED

Theorem add_pt_0[simp]:
  add_pt x (0,0) = x
Proof
  Cases_on `x` \\ simp []
QED

Theorem add_pt_simps[simp]:
  ∀a b.
    neg_pt (neg_pt a) = a ∧
    add_pt a (neg_pt b) = sub_pt a b ∧
    sub_pt a (neg_pt b) = add_pt a b ∧
    add_pt (sub_pt a b) b = a ∧
    sub_pt (add_pt a b) b = a ∧
    add_pt b (sub_pt a b) = a ∧
    sub_pt (add_pt b a) b = a ∧
    add_pt (neg_pt a) (add_pt a b) = b ∧
    add_pt a (add_pt (neg_pt a) b) = b
Proof
  simp [FORALL_PROD, int_sub] \\ ARITH_TAC
QED

Theorem add_pt_comm:
  add_pt a b = add_pt b a
Proof
  MAP_EVERY Cases_on [`a`,`b`] \\ simp [INT_ADD_SYM]
QED

Theorem add_pt_assoc:
  add_pt a (add_pt b c) = add_pt (add_pt a b) c
Proof
  MAP_EVERY Cases_on [`a`,`b`,`c`] \\ simp [INT_ADD_ASSOC]
QED

Definition circ_mod_wf_def:
  circ_mod_wf area ins outs ⇔
    (∀x y. (x,y) ∈ area ⇒ x % 2 = 0 ∧ y % 2 = 0) ∧
    (∀p r1 r2. (p,r1) ∈ ins ∧ (p,r2) ∈ ins ⇒ r1 = r2) ∧
    (∀p r1 r2. (p,r1) ∈ outs ∧ (p,r2) ∈ outs ⇒ r1 = r2) ∧
    (∀p d1 r1 d2 r2. (p,d1,r1) ∈ ins ∧ (p,d2,r2) ∈ outs ⇒ d1 = d2) ∧
    (∀p d r. (p,d,r) ∈ ins ⇒ add_pt p (dir_to_xy d) ∈ area) ∧
    (∀p d r. (p,d,r) ∈ outs ⇒ sub_pt p (dir_to_xy d) ∈ area) ∧
    (∀p d r. (p,d,r) ∈ ins ∧ sub_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ outs) ∧
    (∀p d r. (p,d,r) ∈ outs ∧ add_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ ins)
End

Theorem circ_mod_wf_def_old:
  circ_mod_wf area ins outs ⇔
    (∀x y. (x,y) ∈ area ⇒ x % 2 = 0 ∧ y % 2 = 0) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ ins ∧ ((x,y),r2) ∈ ins ⇒ r1 = r2) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ outs ∧ ((x,y),r2) ∈ outs ⇒ r1 = r2) ∧
    (∀p d1 r1 d2 r2. (p,d1,r1) ∈ ins ∧ (p,d2,r2) ∈ outs ⇒ d1 = d2) ∧
    (∀x y r. ((x,y),N,r) ∈ ins ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ ins ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ ins ⇒ (x+1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ ins ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),N,r) ∈ outs ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ outs ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ outs ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ outs ⇒ (x+1,y) ∈ area) ∧
    (∀p d r. (p,d,r) ∈ ins ∧ sub_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ outs) ∧
    (∀p d r. (p,d,r) ∈ outs ∧ add_pt p (dir_to_xy d) ∈ area ⇒ (p,d,r) ∈ ins)
Proof
  simp [circ_mod_wf_def] \\ rpt AP_TERM_TAC
  \\ qabbrev_tac ‘b = ∀p d1 r1 d2 r2. (p,d1,r1) ∈ ins ∧ (p,d2,r2) ∈ outs ⇒ d1 = d2’
  \\ pop_assum kall_tac
  \\ `∀P. (∀d. P d) ⇔ P N ∧ P S ∧ P E ∧ P W` by
    (strip_tac \\ eq_tac \\ strip_tac \\ TRY Cases \\ metis_tac [])
  \\ pop_assum (rw o single) \\ rw [FORALL_PROD, GSYM int_sub]
  \\ metis_tac []
QED

Definition circ_area_def:
  circ_area area ins outs n =
    if n MOD 60 < 30 then
      base_area area DIFF
      (U { io_box (x,y) | ∃d r:α. ((x,y),d,r) ∈ ins ∧ d ∈ {N;S} } ∪
       U { io_box (x,y) | ∃d r:α. ((x,y),d,r) ∈ outs ∧ d ∈ {E;W} }) ∪
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

Definition dir_test_def:
  dir_test use_ns = if use_ns then is_ns else is_ew
End

Definition io_cutout_def:
  io_cutout ins outs early_phase =
    circ_io_area (ins ∩ dir_test early_phase
                  ∪ outs ∩ dir_test (¬early_phase))
End

Theorem io_cutout_eq:
  io_cutout ins outs early_phase =
    circ_io_area (ins ∩ dir_test early_phase) ∪
    circ_io_area (outs ∩ dir_test (¬early_phase))
Proof
  gvs [io_cutout_def,EXTENSION,circ_io_area_def]
  \\ metis_tac []
QED

Theorem circ_area_eq:
  circ_area area ins outs n =
    base_area area
    DIFF (io_cutout ins outs (n MOD 60 < 30))
    ∪ (io_cutout ins outs (¬ (n MOD 60 < 30)))
Proof
  Cases_on ‘n MOD 60 < 30’ \\ gvs []
  \\ gvs [circ_area_def]
  \\ gvs [circ_io_area_def,EXISTS_PROD,io_cutout_eq,dir_test_def]
  \\ simp [IN_DEF,is_ns_def,is_ew_def]
QED

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
  circ_mod area ins outs n =
    <| area           := circ_area area ins outs n ;
       deletions      := circ_output_area outs n ;
       insertions     := circ_io_lwss ins n ;
       assert_area    := circ_output_area outs n ;
       assert_content := circ_io_lwss outs n |>
End

Theorem circ_mod_empty[simp]:
  circ_mod ∅ ∅ ∅ = empty_mod
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

Theorem IN_io_box_io_box:
  (a0,a1) ∈ io_box (x,y) ⇒ ((a0,a1) ∈ io_box (x1,y1) ⇔ x = x1 ∧ y = y1)
Proof
  gvs [io_box_def,box_def] \\ intLib.COOPER_TAC
QED

Theorem in_dir_test_not:
  x ∈ dir_test (~b) ⇔ x ∉ dir_test b
Proof
  PairCases_on ‘x’ \\ gvs [dir_test_def] \\ rw []
  \\ Cases_on ‘x1’ \\ gvs [is_ns_def,is_ew_def,IN_DEF]
QED

Theorem io_box_11:
  a ∈ io_box x ∧ a ∈ io_box y ⇒ x = y
Proof
  PairCases_on ‘x’
  \\ PairCases_on ‘y’
  \\ gvs [io_box_def,box_def]
  \\ strip_tac \\ gvs []
  \\ COOPER_TAC
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

Theorem mods_wf_circ_mod:
  circ_mod_wf area ins outs ⇒
  mods_wf (circ_mod area ins outs)
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
    \\ gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD] \\ metis_tac [])
  \\ rw [circ_io_lwss_def]
  \\ simp [circ_io_area_def,circ_output_area_def,
           SUBSET_DEF,FORALL_PROD,PULL_EXISTS,EXISTS_PROD]
  \\ rewrite_tac [GSYM AND_IMP_INTRO]
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ imp_res_tac lwss_at_imp_io_box \\ gvs []
QED

Definition circuit_run_def:
  circuit_run area ins outs init ⇔
    run (circ_mod area ins outs) init ∧
    circ_mod_wf area ins outs
End

Theorem circuit_run_empty:
  circuit_run ∅ ∅ ∅ ∅
Proof
  simp [circuit_run_def, run_empty_mod, circ_mod_wf_def]
QED

Definition circuit_def:
  circuit area ins outs init ⇔
    circuit_run (set area) (set ins) (set outs) init ∧
    ALL_DISTINCT area ∧
    ALL_DISTINCT (MAP FST ins) ∧
    ALL_DISTINCT (MAP FST outs)
End

Theorem io_steps_add:
  ∀k c n s1 s2.
    io_steps (l + k) c n s1 s2 ⇔
    ∃s3. io_steps k c n s1 s3 ∧ io_steps l c (n + k) s3 s2
Proof
  Induct_on ‘k’ \\ gvs []
  \\ once_rewrite_tac [io_steps_def] \\ gvs [ADD_CLAUSES]
  \\ gvs [io_steps_def] \\ gvs [PULL_EXISTS,ADD1]
  \\ metis_tac []
QED

Theorem run_to_le:
  ∀k k0 c s t. run_to k c s t ∧ k0 ≤ k ⇒ ∃u. run_to k0 c s u
Proof
  rw [] \\ gvs [LESS_EQ_EXISTS,run_to_def]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [io_steps_add] \\ rw []
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

Triviality diff_inter:
  (s DIFF t) ∩ y = (s ∩ y) DIFF (t ∩ y)
Proof
  gvs [EXTENSION] \\ metis_tac []
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

Theorem both_ins_outs_IMP_base_area:
  circ_mod_wf area ins outs ∧
  m ⊆ ins ∧
  m ⊆ outs ∧
  (p0,p1) ∈ circ_io_area m ⇒
  (p0,p1) ∈ base_area area
Proof
  gvs [circ_io_area_def] \\ rw []
  \\ PairCases_on ‘r’
  \\ gvs [SUBSET_DEF]
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ ‘add_pt (x,y) (dir_to_xy r0) ∈ area ∧
      sub_pt (x,y) (dir_to_xy r0) ∈ area’ by
    (gvs [circ_mod_wf_def] \\ res_tac \\ gvs [])
  \\ Cases_on ‘r0’ \\ gvs [dir_to_xy_def]
  \\ gvs [base_area_def,PULL_EXISTS]
  \\ gvs [box_def,PULL_EXISTS,io_box_def, GSYM int_sub]
  >- (Cases_on ‘j < 6’
      >- (qexists_tac ‘x’ \\ qexists_tac ‘y - 1’ \\ gvs [] \\ COOPER_TAC)
      >- (qexists_tac ‘x’ \\ qexists_tac ‘y + 1’ \\ gvs [] \\ COOPER_TAC))
  >- (Cases_on ‘j < 6’
      >- (qexists_tac ‘x’ \\ qexists_tac ‘y - 1’ \\ gvs [] \\ COOPER_TAC)
      >- (qexists_tac ‘x’ \\ qexists_tac ‘y + 1’ \\ gvs [] \\ COOPER_TAC))
  >- (Cases_on ‘i < 6’
      >- (qexists_tac ‘x - 1’ \\ qexists_tac ‘y’ \\ gvs [] \\ COOPER_TAC)
      >- (qexists_tac ‘x + 1’ \\ qexists_tac ‘y’ \\ gvs [] \\ COOPER_TAC))
  >- (Cases_on ‘i < 6’
      >- (qexists_tac ‘x - 1’ \\ qexists_tac ‘y’ \\ gvs [] \\ COOPER_TAC)
      >- (qexists_tac ‘x + 1’ \\ qexists_tac ‘y’ \\ gvs [] \\ COOPER_TAC))
QED

Theorem circ_area_diff:
  circ_mod_wf area ins outs ∧
  m ⊆ ins ∧
  m ⊆ outs ⇒
  circ_area area ins outs x =
  circ_area area (ins DIFF m) (outs DIFF m) x
Proof
  gvs [circ_area_eq] \\ rw []
  \\ simp [Once EXTENSION]
  \\ rw [] \\ eq_tac
  \\ strip_tac \\ gvs []
  \\ gvs [io_cutout_def]
  \\ qabbrev_tac ‘b = (x MOD 60 < 30)’
  >- (disj1_tac \\ gvs [circ_io_area_def] \\ metis_tac [])
  >-
   (match_mp_tac (METIS_PROVE [] “(~c ⇒ b) ⇒ (b ∨ c)”)
    \\ strip_tac
    \\ rename [‘p ∈ base_area area’] \\ PairCases_on ‘p’
    \\ ‘(p0,p1) ∈ circ_io_area m’ by (gvs [circ_io_area_def] \\ metis_tac [])
    \\ reverse conj_tac
    >-
     (gvs [diff_inter]
      \\ ‘(ins ∩ dir_test b DIFF m ∩ dir_test b ∪
               (outs ∩ dir_test (¬b) DIFF m ∩ dir_test (¬b))) =
          (ins ∩ dir_test b ∪ outs ∩ dir_test (¬b)) DIFF m’ by
        (gvs [EXTENSION,in_dir_test_not] \\ metis_tac [])
      \\ gvs [] \\ qabbrev_tac ‘s = ins ∩ dir_test b ∪ outs ∩ dir_test (¬b)’
      \\ qpat_x_assum ‘(p0,p1) ∈ circ_io_area m’ mp_tac
      \\ simp [circ_io_area_def]
      \\ gvs [METIS_PROVE [] “~b ∨ c ⇔ b ⇒ c”,PULL_FORALL,PULL_EXISTS]
      \\ rpt strip_tac
      \\ dxrule_then dxrule io_box_11
      \\ strip_tac \\ gvs []
      \\ rename [‘((x,y),r) ∈ m’]
      \\ qsuff_tac ‘r = r'’ >- gvs []
      \\ unabbrev_all_tac \\ gvs []
      \\ gvs [circ_mod_wf_def]
      \\ metis_tac [SUBSET_DEF])
    \\ drule_all both_ins_outs_IMP_base_area \\ gvs [])
  >- (CCONTR_TAC \\ gvs []
      \\ gvs [circ_io_area_def]
      \\ gvs [METIS_PROVE [] “~b ∨ c ⇔ b ⇒ c”,PULL_FORALL]
      \\ ntac 2 $ first_x_assum drule \\ rpt strip_tac
      \\ rename [‘((x,y),r) ∈ dir_test _’]
      \\ ‘((x,y),r) ∈ m’ by metis_tac []
      \\ metis_tac [SUBSET_DEF])
  >- (disj2_tac \\ gvs [circ_io_area_def] \\ metis_tac [])
QED

Theorem circ_io_area_empty:
  circ_io_area {} = {}
Proof
  gvs [circ_io_area_def]
QED

Theorem circ_io_area_inter:
  a ⊆ b ⇒
  circ_io_area a ∩ circ_io_area b = circ_io_area a
Proof
  simp [EXTENSION] \\ rw [] \\ reverse eq_tac \\ rw []
  \\ gvs [circ_io_area_def,PULL_EXISTS,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem circ_io_area_SUBSET:
  m1 ⊆ m2 ⇒ circ_io_area m1 ⊆ circ_io_area m2
Proof
  gvs [circ_io_area_def,SUBSET_DEF,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem lwss_at_io_box:
  x ∈ lwss_at n (p,r) ∧ x ∈ io_box q ⇒ p = q
Proof
  PairCases_on ‘x’
  \\ PairCases_on ‘p’ \\ rw []
  \\ imp_res_tac lwss_at_imp_io_box
  \\ imp_res_tac io_box_11 \\ gvs []
QED

Theorem lwss_at_circ_io_area:
  m ⊆ s1 ∧ m ⊆ s2 ∧
  (∀p r1 r2. (p,r1) ∈ s1 ∧ (p,r2) ∈ s1 ⇒ r1 = r2) ∧
  (∀p r1 r2. (p,r1) ∈ s2 ∧ (p,r2) ∈ s2 ⇒ r1 = r2) ⇒
  U (IMAGE (lwss_at n) s1) ∩ circ_io_area m =
  U (IMAGE (lwss_at n) s2) ∩ circ_io_area m
Proof
  simp [Once EXTENSION]
  \\ gvs [PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  \\ gvs [circ_io_area_def]
  \\ rename [‘x ∈ lwss_at n z’] \\ PairCases_on ‘z’ \\ gvs []
  \\ gvs [PULL_EXISTS]
  \\ drule_all lwss_at_io_box
  \\ strip_tac \\ gvs []
  \\ metis_tac [SUBSET_DEF]
QED

Theorem circ_io_area_disjoint:
  m ⊆ outs ∧ DISJOINT m p ∧ circ_mod_wf area ins outs ⇒
  circ_io_area m ∩ circ_io_area (outs ∩ p) = ∅
Proof
  gvs [circ_io_area_def]
  \\ simp [Once EXTENSION]
  \\ strip_tac
  \\ CCONTR_TAC \\ gvs []
  \\ dxrule_then dxrule io_box_11 \\ strip_tac \\ gvs []
  \\ gvs [SUBSET_DEF]
  \\ gvs [EXTENSION]
  \\ gvs [circ_mod_wf_def]
  \\ gvs [IN_DISJOINT]
  \\ metis_tac []
QED

Theorem to_dir_test:
  is_ns = dir_test T ∧
  is_ew = dir_test F
Proof
  gvs [dir_test_def]
QED

Theorem circ_io_area_eq_empty_lemma:
  circ_io_area m ∩ circ_io_area (outs ∩ dir_test b) = ∅ ∧
  m ≠ {} ∧ m ⊆ dir_test c ∧ m ⊆ outs ⇒
  c ≠ b
Proof
  CCONTR_TAC \\ gvs []
  \\ last_x_assum mp_tac
  \\ gvs [] \\ gvs [EXTENSION]
  \\ gvs [circ_io_area_def,PULL_EXISTS]
  \\ gvs [SUBSET_DEF] \\ res_tac
  \\ PairCases_on ‘x’
  \\ rpt $ last_assum $ irule_at Any
  \\ gvs [io_box_def]
  \\ qexists_tac ‘(75 * x0 − 6,75 * x1 − 6)’
  \\ gvs [box_def]
  \\ qexists_tac ‘0’
  \\ qexists_tac ‘0’
  \\ gvs []
QED

Theorem circ_io_area_neq_empty_lemma:
  circ_io_area m ∩ circ_io_area (outs ∩ dir_test b) ≠ ∅ ∧
  circ_mod_wf area ins outs ∧
  m ⊆ dir_test c ∧ m ⊆ outs ⇒
  c = b
Proof
  gvs [EXTENSION]
  \\ gvs [circ_io_area_def]
  \\ strip_tac \\ gvs []
  \\ imp_res_tac io_box_11
  \\ fs [] \\ gvs []
  \\ gvs [SUBSET_DEF]
  \\ res_tac
  \\ ‘r = r'’ by (gvs [circ_mod_wf_def] \\ res_tac)
  \\ gvs []
  \\ CCONTR_TAC \\ gvs []
  \\ ‘b = ~c’ by metis_tac [] \\ gvs []
  \\ gvs [in_dir_test_not]
QED

Theorem subset_dir_test_imp:
  m ⊆ dir_test b ⇒
  (m ∩ dir_test (~b) = {}) ∧
  (m ∩ dir_test b = m)
Proof
  gvs [SUBSET_DEF,EXTENSION,in_dir_test_not] \\ metis_tac []
QED

Theorem lwss_at_diff_lemma:
  m ⊆ s ∧ (∀p r1 r2. (p,r1) ∈ s ∧ (p,r2) ∈ s ⇒ r1 = r2)
  ⇒
  U (IMAGE (lwss_at x) s) DIFF circ_io_area m =
  U (IMAGE (lwss_at x) (s DIFF m))
Proof
  rw [] \\ simp [Once EXTENSION,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ gvs [METIS_PROVE [] “~b ∨ c ⇔ b ⇒ c”,PULL_FORALL]
  \\ CCONTR_TAC \\ gvs []
  \\ gvs [circ_io_area_def]
  \\ rename [‘a ∈ lwss_at x b’]
  \\ PairCases_on ‘a’
  \\ PairCases_on ‘b’
  \\ drule lwss_at_imp_io_box \\ strip_tac
  >- (gvs [METIS_PROVE [] “~b ∨ c ⇔ b ⇒ c”,PULL_FORALL])
  \\ dxrule_then dxrule io_box_11
  \\ strip_tac
  \\ gvs [SUBSET_DEF]
  \\ metis_tac []
QED

Theorem circ_area_diff_distrib:
  m ⊆ s ∧ (∀p r1 r2. (p,r1) ∈ s ∧ (p,r2) ∈ s ⇒ r1 = r2)
  ⇒
  circ_io_area s DIFF circ_io_area m =
  circ_io_area (s DIFF m)
Proof
  rw [EXTENSION] \\ eq_tac \\ rw []
  \\ gvs [circ_io_area_def,PULL_EXISTS]
  \\ gvs [METIS_PROVE [] “~b ∨ c ⇔ b ⇒ c”,PULL_FORALL]
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ rw []
  \\ dxrule_then dxrule io_box_11
  \\ strip_tac \\ gvs []
  \\ CCONTR_TAC
  \\ gvs [SUBSET_DEF]
  \\ res_tac
  \\ metis_tac []
QED

Triviality circuit_run_internalise_lemma:
  ∀m area ins outs init.
    circuit_run area ins outs init ∧ m ⊆ ins ∧ m ⊆ outs ∧
    (¬ (m ⊆ is_ns) ⇒ m ⊆ is_ew) ⇒
    circuit_run area (ins DIFF m) (outs DIFF m) init
Proof
  gvs [circuit_run_def] \\ rpt gen_tac \\ strip_tac
  \\ dxrule to_del_io_run
  \\ disch_then $ qspec_then ‘circ_io_area m’ mp_tac
  \\ impl_tac
  >-
   (gvs [can_assert_def,circ_mod_def]
    \\ gen_tac \\ gvs [circ_output_area_def]
    \\ IF_CASES_TAC \\ gvs [] \\ strip_tac
    >-
     (‘m ⊆ is_ns’ by
        (CCONTR_TAC \\ gvs []
         \\ qpat_x_assum ‘_ ≠ EMPTY’ mp_tac \\ gvs []
         \\ irule circ_io_area_disjoint
         \\ last_x_assum $ irule_at Any \\ gvs []
         \\ gvs [IN_DISJOINT,SUBSET_DEF]
         \\ CCONTR_TAC \\ gvs [] \\ res_tac
         \\ gvs [IN_DEF] \\ gvs [is_ns_not_is_ew])
      \\ gvs [circ_io_lwss_def]
      \\ rpt $ irule_at Any circ_io_area_SUBSET
      \\ irule_at Any lwss_at_circ_io_area
      \\ gvs [SUBSET_DEF, SF SFY_ss]
      \\ gvs [circ_mod_wf_def,SF SFY_ss])
    \\ IF_CASES_TAC \\ gvs []
    >-
     (‘m ⊆ is_ew’ by
        (CCONTR_TAC \\ gvs []
         \\ qpat_x_assum ‘_ ≠ EMPTY’ mp_tac \\ gvs []
         \\ irule circ_io_area_disjoint
         \\ last_x_assum $ irule_at Any \\ gvs []
         \\ gvs [IN_DISJOINT,SUBSET_DEF]
         \\ CCONTR_TAC \\ gvs [] \\ res_tac
         \\ gvs [IN_DEF] \\ gvs [is_ns_not_is_ew])
      \\ gvs [circ_io_lwss_def]
      \\ rpt $ irule_at Any circ_io_area_SUBSET
      \\ irule_at Any lwss_at_circ_io_area
      \\ gvs [SUBSET_DEF, SF SFY_ss]
      \\ gvs [circ_mod_wf_def,SF SFY_ss])
    \\ gvs [circ_io_area_empty])
  \\ qsuff_tac
     ‘del_io (circ_io_area m) (circ_mod area ins outs) =
      circ_mod area (ins DIFF m) (outs DIFF m)’
  >- (gvs [] \\ rw [] \\ gvs [circ_mod_wf_def, SF SFY_ss, SF DNF_ss])
  \\ gvs [FUN_EQ_THM] \\ gvs [del_io_def,del_io_mod_def,circ_mod_def]
  \\ gen_tac \\ IF_CASES_TAC
  \\ gvs [modifier_component_equality]
  \\ irule_at Any circ_area_diff
  \\ first_assum $ irule_at $ Pos hd \\ simp []
  \\ ‘∃c. m ⊆ dir_test c’ by metis_tac [to_dir_test]
  >-
   (qpat_x_assum ‘_ = {}’ mp_tac
    \\ Cases_on ‘m = {}’ >- gvs []
    \\ simp [Once circ_output_area_def]
    \\ reverse $ rpt (IF_CASES_TAC \\ gvs [circ_io_area_empty])
    >- simp [circ_io_lwss_def,circ_output_area_def]
    \\ simp [circ_output_area_def]
    \\ simp [circ_io_lwss_def]
    \\ gvs [to_dir_test]
    \\ strip_tac
    \\ drule_all circ_io_area_eq_empty_lemma
    \\ strip_tac \\ gvs []
    \\ gvs [diff_inter]
    \\ drule subset_dir_test_imp \\ gvs [])
  \\ qpat_x_assum ‘_ ≠ {}’ mp_tac
  \\ simp [Once circ_output_area_def]
  \\ reverse $ rpt (IF_CASES_TAC \\ gvs [circ_io_area_empty])
  \\ simp [circ_io_lwss_def,circ_output_area_def]
  \\ strip_tac
  \\ gvs [to_dir_test]
  \\ drule_all circ_io_area_neq_empty_lemma \\ strip_tac \\ gvs []
  \\ gvs [diff_inter]
  \\ imp_res_tac subset_dir_test_imp
  \\ simp [] \\ pop_assum kall_tac
  \\ DEP_REWRITE_TAC [lwss_at_diff_lemma,circ_area_diff_distrib]
  \\ gvs [SUBSET_DEF]
  \\ gvs [circ_mod_wf_def,SF SFY_ss]
QED

Theorem circuit_run_internalise:
  ∀m area ins outs init.
    circuit_run area ins outs init ∧ m ⊆ ins ∧ m ⊆ outs ⇒
    circuit_run area (ins DIFF m) (outs DIFF m) init
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

Theorem iunion_if:
  iunion (λb. if b then x else y) = (x ∪ y)
Proof
  simp [EXTENSION] \\ metis_tac []
QED

Theorem base_area_disjoint:
  (z0,z1) ∈ base_area (area x) ∧
  (z0,z1) ∈ base_area (area y) ∧
  DISJOINT (area x) (area y) ∧
  (∀x y a. (x,y) ∈ area a ⇒ x % 2 = 0 ∧ y % 2 = 0) ⇒
  F
Proof
  strip_tac
  \\ gvs [base_area_def,PULL_EXISTS,PULL_FORALL,METIS_PROVE [] “~b ∨ c ⇔ b ⇒ c”,IN_DISJOINT]
  \\ res_tac \\ gvs []
  \\ rpt $ qpat_x_assum ‘_ ∈ area _’ mp_tac
  \\ rename [‘(x1,y1) ∈ area x ⇒ (x2,y2) ∈ area y ⇒ _’]
  \\ rpt strip_tac
  \\ ‘x1 = x2 ⇒ y1 ≠ y2’ by metis_tac []
  \\ gvs [box_def]
  \\ intLib.COOPER_TAC
QED

Theorem IN_circ_io_areas:
  (z0,z1) ∈ circ_io_area s ∧ (z0,z1) ∈ circ_io_area t ⇒
  ∃xy r1 r2. (xy,r1) ∈ s ∧ (xy,r2) ∈ t
Proof
  rw [circ_io_area_def,PULL_EXISTS]
  \\ CCONTR_TAC \\ gvs []
  \\ rename [‘((x1,y1),r1) ∈ t’]
  \\ first_x_assum $ qspecl_then [‘(x,y)’,‘r’] assume_tac \\ gvs []
  \\ ‘x = x1 ⇒  y ≠ y1’ by metis_tac []
  \\ gvs [io_box_def,box_def]
  \\ intLib.COOPER_TAC
QED

Theorem circ_mod_wf_imp_even:
  circ_mod_wf a ins outs ∧ (x,y) ∈ a ⇒ ∃i j. x = 2 * i ∧ y = 2 * j
Proof
  rw [circ_mod_wf_def, SF SFY_ss]
  \\ res_tac \\ COOPER_TAC
QED

Theorem in_io_box_base_area_y:
  (z0,z1) ∈ base_area a1 ∧
  circ_mod_wf a1 ins1 outs ∧
  (z0,z1) ∈ io_box (2 * i,2 * m + 1) ⇒
  (2 * i, 2 * m) ∈ a1 ∨
  (2 * i, 2 * m + 2) ∈ a1
Proof
  gvs [io_box_def,box_def,INT_MUL_ASSOC]
  \\ rw [] \\ gvs [base_area_def,box_def]
  \\ drule_all circ_mod_wf_imp_even
  \\ strip_tac \\ gvs []
  \\ CCONTR_TAC \\ gvs []
  \\ imp_res_tac (METIS_PROVE [] “(x,y) ∈ s ∧ (a,b) ∉ s ⇒  a = x ⇒ y ≠ b”)
  \\ COOPER_TAC
QED

Theorem in_io_box_base_area_x:
  (z0,z1) ∈ base_area a1 ∧
  circ_mod_wf a1 ins1 outs ∧
  (z0,z1) ∈ io_box (2 * i + 1,2 * m) ⇒
  (2 * i, 2 * m) ∈ a1 ∨
  (2 * i + 2, 2 * m) ∈ a1
Proof
  gvs [io_box_def,box_def,INT_MUL_ASSOC]
  \\ rw [] \\ gvs [base_area_def,box_def]
  \\ drule_all circ_mod_wf_imp_even
  \\ strip_tac \\ gvs []
  \\ CCONTR_TAC \\ gvs []
  \\ imp_res_tac (METIS_PROVE [] “(x,y) ∈ s ∧ (a,b) ∉ s ⇒  a = x ⇒ y ≠ b”)
  \\ COOPER_TAC
QED

Theorem sub_pt_in_area:
  (z0,z1) ∈ base_area a1 ∧
  (z0,z1) ∈ io_box (x1,y1) ∧
  DISJOINT a1 a2 ∧
  (d = N ∨ d = S ⇒ ∃n m. x1 = 2 * n ∧ y1 = 2 * m + 1) ∧
  (d = E ∨ d = W ⇒ ∃n m. x1 = 2 * n + 1 ∧ y1 = 2 * m) ∧
  circ_mod_wf a1 ins1 (outs1:(int # int) # dir # β -> bool) ∧
  circ_mod_wf a2 ins2 (outs2:(int # int) # dir # β -> bool) ∧
  add_pt (x1,y1) (dir_to_xy d) ∈ a2 ⇒
  sub_pt (x1,y1) (dir_to_xy d) ∈ a1
Proof
  strip_tac
  \\ Cases_on ‘d’ \\ gvs [sub_pt_def,add_pt_def]
  \\ gvs [GSYM int_sub,int_arithTheory.elim_minus_ones]
  \\ gvs [GSYM INT_ADD_ASSOC]
  \\ rpt $ dxrule_all in_io_box_base_area_x
  \\ rpt $ dxrule_all in_io_box_base_area_y
  \\ strip_tac \\ gvs []
  \\ metis_tac [IN_DISJOINT]
QED

Definition opposite_def[simp]:
  opposite N = S ∧
  opposite S = N ∧
  opposite E = W ∧
  opposite w = E
End

Theorem dir_to_xy_opposite:
  add_pt (x,y) (dir_to_xy d) = sub_pt (x,y) (dir_to_xy (opposite d)) ∧
  sub_pt (x,y) (dir_to_xy d) = add_pt (x,y) (dir_to_xy (opposite d))
Proof
  Cases_on ‘d’ \\ gvs [add_pt_def,sub_pt_def,int_sub]
QED

Theorem circ_mod_wf_imp:
  circ_mod_wf a ins outs ⇒
  (∀p d r. (p,d,r) ∈ ins ⇒ add_pt p (dir_to_xy d) ∈ a) ∧
  (∀p d r. (p,d,r) ∈ outs ⇒ sub_pt p (dir_to_xy d) ∈ a)
Proof
  gvs [circ_mod_wf_def, SF SFY_ss]
QED

Theorem port_locations:
  circ_mod_wf area ins outs ⇒
  ((x1,y1),d,rest) ∈ ins ∪ outs ⇒
  (d = E ∨ d = W ⇒ ∃n m. x1 = 2 * n + 1 ∧ y1 = 2 * m) ∧
  (d = N ∨ d = S ⇒ ∃n m. x1 = 2 * n ∧ y1 = 2 * m + 1)
Proof
  simp [] \\ ntac 2 strip_tac
  \\ drule circ_mod_wf_imp
  \\ strip_tac
  \\ first_x_assum drule
  \\ rpt strip_tac \\ gvs []
  \\ dxrule_all circ_mod_wf_imp_even
  \\ rpt strip_tac \\ gvs []
  \\ COOPER_TAC
QED

Theorem in_io_cutout_lemma:
  DISJOINT (area x) (area y) ∧
  circ_mod_wf (area x) (ins x) (outs x) ∧
  circ_mod_wf (area y) (ins y) (outs y) ∧
  (∀p d r. (p,d,r) ∈ ins x ∧ sub_pt p (dir_to_xy d) ∈ area y ⇒ (p,d,r) ∈ outs y) ∧
  (∀p d r. (p,d,r) ∈ outs x ∧ add_pt p (dir_to_xy d) ∈ area y ⇒ (p,d,r) ∈ ins y) ∧
  (∀p d r. (p,d,r) ∈ ins y ∧ sub_pt p (dir_to_xy d) ∈ area x ⇒ (p,d,r) ∈ outs x) ∧
  (∀p d r. (p,d,r) ∈ outs y ∧ add_pt p (dir_to_xy d) ∈ area x ⇒ (p,d,r) ∈ ins x) ∧
  (z0,z1) ∈ base_area (area x) ∧
  (z0,z1) ∈ io_cutout (ins y) (outs y) b ⇒
  (z0,z1) ∈ io_cutout (ins x) (outs x) (~b)
Proof
  gvs [io_cutout_def,circ_io_area_def,PULL_EXISTS] \\ rw []
  \\ first_assum $ irule_at $ Pos hd
  \\ PairCases_on ‘r’
  \\ first_x_assum drule
  >-
   (reverse impl_tac
    >- (rw [] \\ gvs [SF DNF_ss]
        \\ disj2_tac \\ pop_assum $ irule_at Any \\ gvs [])
    \\ rename [‘((x1,y1),d,rest) ∈ dir_test _’]
    \\ ‘add_pt (x1,y1) (dir_to_xy d) ∈ area y’ by
      (gvs [] \\ gvs [circ_mod_wf_def]
       \\ res_tac \\ fs [] \\ gvs [])
    \\ drule_then drule sub_pt_in_area
    \\ disch_then irule
    \\ pop_assum $ irule_at Any
    \\ rpt $ first_assum $ irule_at Any
    \\ drule port_locations
    \\ disch_then match_mp_tac
    \\ gvs [] \\ metis_tac [])
  >-
   (reverse impl_tac
    >- (rw [] \\ gvs [SF DNF_ss]
        \\ disj1_tac \\ pop_assum $ irule_at Any \\ gvs [])
    \\ rename [‘((x1,y1),d,rest) ∈ dir_test _’]
    \\ ‘sub_pt (x1,y1) (dir_to_xy d) ∈ area y’ by
      (gvs [] \\ gvs [circ_mod_wf_def]
       \\ res_tac \\ fs [] \\ gvs [])
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [dir_to_xy_opposite]
    \\ strip_tac
    \\ drule_then drule sub_pt_in_area
    \\ disch_then irule
    \\ pop_assum $ irule_at Any
    \\ rpt $ first_assum $ irule_at Any
    \\ drule port_locations
    \\ ‘opposite d = E ∨ opposite d = W ⇔ d = E ∨ d = W’ by (Cases_on ‘d’ \\ gvs [])
    \\ ‘opposite d = N ∨ opposite d = S ⇔ d = N ∨ d = S’ by (Cases_on ‘d’ \\ gvs [])
    \\ simp [] \\ disch_then match_mp_tac
    \\ simp [] \\ gvs [] \\ metis_tac [])
QED

Theorem circ_mod_wf_imp_dir_test:
  circ_mod_wf a ins outs ⇒
  (∀p d r. (p,d,r) ∈ ins ⇒ (p,d,r) ∈ dir_test (FST p % 2 = 0)) ∧
  (∀p d r. (p,d,r) ∈ outs ⇒ (p,d,r) ∈ dir_test (FST p % 2 = 0))
Proof
  rw [circ_mod_wf_def, SF DNF_ss]
  \\ PairCases_on ‘p’ \\ gvs []
  \\ rpt $ first_x_assum $ drule
  \\ Cases_on ‘d’ \\ simp [dir_to_xy_def]
  \\ rpt strip_tac
  \\ last_x_assum drule
  \\ simp [dir_test_def,IN_DEF,is_ns_def,is_ew_def]
  \\ rw [] \\ gvs [is_ns_def,is_ew_def]
  \\ intLib.COOPER_TAC
QED

Theorem IN_dir_test:
  (xy,d,r) ∈ dir_test b1 ∧ (xy,d,r) ∈ dir_test b2 ⇒ b1 = b2
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ Cases_on ‘d’
  \\ gvs [IN_DEF,is_ns_def,is_ew_def,dir_test_def]
QED

Theorem iunion_inter:
  iunion f ∩ s = iunion (λz. f z ∩ s)
Proof
  gvs [EXTENSION] \\ metis_tac []
QED

Theorem circ_io_area_iunion:
  circ_io_area (iunion f) = iunion (circ_io_area o f)
Proof
  gvs [EXTENSION,FORALL_PROD,circ_io_area_def]
  \\ metis_tac []
QED

Theorem io_cutout_iunion:
  io_cutout (iunion ins) (iunion outs) b =
  iunion (λz. io_cutout (ins z) (outs z) b)
Proof
  gvs [EXTENSION,io_cutout_eq,FORALL_PROD,
       iunion_inter,circ_io_area_iunion]
  \\ metis_tac []
QED

Theorem dir_test_opposite:
  d1 ≠ d2 ∧ (p,d1,r1) ∈ dir_test b ∧ (p,d2,r2) ∈ dir_test b ⇒
  d1 = opposite d2
Proof
  Cases_on ‘b’ \\ gvs [dir_test_def,IN_DEF]
  \\ Cases_on ‘d1’ \\ Cases_on ‘d2’ \\ gvs [is_ns_def,is_ew_def]
QED

Theorem opposite_opposite:
  ∀d. opposite (opposite d) = d
Proof
  Cases \\ EVAL_TAC
QED

Theorem circuit_run_compose_bigunion:
  ∀area ins outs init.
  (* each element in the family must be a circuit_run *)
  (∀x. circuit_run (area x) (ins x) (outs x) (init x)) ∧
  (∀x1 x2. x1 ≠ x2 ⇒
    (* all areas must be disjoint *)
    DISJOINT (area x1) (area x2) ∧
    (* on a border between two areas, in/out ports must be matching, if they exist *)
    ∀p d r.
      ((p,d,r) ∈ ins x1 ∧ sub_pt p (dir_to_xy d) ∈ area x2 ⇒ (p,d,r) ∈ outs x2) ∧
      ((p,d,r) ∈ outs x1 ∧ add_pt p (dir_to_xy d) ∈ area x2 ⇒ (p,d,r) ∈ ins x2))
  ⇒
  circuit_run (iunion area) (iunion ins) (iunion outs) (iunion init)
Proof
  rw [] \\ gvs [circuit_run_def]
  \\ reverse conj_asm2_tac
  >-
   (simp [circ_mod_wf_def,PULL_EXISTS,SF DNF_ss]
    \\ ‘(∀x p d r. (p,d,r) ∈ ins x ⇒ (p,d,r) ∈ dir_test (FST p % 2 = 0)) ∧
        (∀x p d r. (p,d,r) ∈ outs x ⇒ (p,d,r) ∈ dir_test (FST p % 2 = 0))’
         by metis_tac [circ_mod_wf_imp_dir_test]
    \\ last_x_assum mp_tac
    \\ CONV_TAC (RATOR_CONV (SCONV [circ_mod_wf_def,PULL_EXISTS,SF DNF_ss]))
    \\ strip_tac
    \\ rpt strip_tac
    \\ simp [SF SFY_ss]
    >- (Cases_on ‘a = a'’ >- metis_tac []
        \\ last_assum drule \\ strip_tac
        \\ ‘a' ≠ a’ by gvs []
        \\ last_x_assum drule \\ strip_tac
        \\ gvs [SF DNF_ss]
        \\ PairCases_on ‘r1’
        \\ PairCases_on ‘r2’
        \\ ‘add_pt p (dir_to_xy r20) ∈ area a' ∧
            add_pt p (dir_to_xy r10) ∈ area a’ by metis_tac []
        \\ Cases_on ‘r20 = r10’ >- metis_tac [IN_DISJOINT]
        \\ ‘r20 = opposite r10’ by metis_tac [dir_test_opposite]
        \\ PairCases_on ‘p’
        \\ gvs [GSYM dir_to_xy_opposite]
        \\ metis_tac [])
    >- (Cases_on ‘a = a'’ >- metis_tac []
        \\ last_assum drule \\ strip_tac
        \\ ‘a' ≠ a’ by gvs []
        \\ last_x_assum drule \\ strip_tac
        \\ gvs [SF DNF_ss]
        \\ PairCases_on ‘r1’
        \\ PairCases_on ‘r2’
        \\ ‘sub_pt p (dir_to_xy r20) ∈ area a' ∧
            sub_pt p (dir_to_xy r10) ∈ area a’ by metis_tac []
        \\ Cases_on ‘r20 = r10’ >- metis_tac [IN_DISJOINT]
        \\ ‘r20 = opposite r10’ by metis_tac [dir_test_opposite]
        \\ PairCases_on ‘p’
        \\ gvs [GSYM dir_to_xy_opposite]
        \\ metis_tac [])
    >- (Cases_on ‘a = a'’ >- metis_tac []
        \\ CCONTR_TAC \\ gvs []
        \\ ‘d1 = opposite d2’ by metis_tac [dir_test_opposite,opposite_opposite]
        \\ ‘add_pt p (dir_to_xy d1) ∈ area a’ by metis_tac []
        \\ PairCases_on ‘p’
        \\ gvs [GSYM dir_to_xy_opposite]
        \\ metis_tac [IN_DISJOINT])
    \\ metis_tac [])
  \\ qspecl_then [‘UNIV’,‘λx. circ_mod (area x) (ins x) (outs x)’,
                  ‘init’] mp_tac run_compose_bigunion
  \\ simp []
  \\ reverse $ impl_tac
  >-
   (match_mp_tac (METIS_PROVE [] “(x = x1 ∧ y = y1) ⇒ (f x y ⇒ f x1 y1)”)
    \\ reverse conj_tac >- simp [iunion_def]
    \\ gvs [join_all_def,circ_mod_def]
    \\ simp [Once FUN_EQ_THM] \\ rw []
    \\ gvs [circ_mod_def]
    \\ simp [GSYM iunion_def]
    \\ reverse conj_tac >-
     (simp [EXTENSION]
      \\ gvs [circ_io_area_def,circ_output_area_def,PULL_EXISTS,circ_io_lwss_def]
      \\ rpt (IF_CASES_TAC \\ gvs [])
      \\ metis_tac [])
    \\ simp [circ_area_eq,EXTENSION] \\ PairCases
    \\ qabbrev_tac ‘b = (n MOD 60 < 30)’
    \\ reverse eq_tac
    >-
     (gvs [io_cutout_eq,circ_io_area_def]
      \\ gvs [base_area_def,PULL_EXISTS,PULL_FORALL,IN_DISJOINT]
      \\ rw [] \\ metis_tac [])
    \\ reverse strip_tac
    >-
     (disj2_tac \\ gvs [io_cutout_eq,circ_io_area_def]
      \\ gvs [base_area_def,PULL_EXISTS,PULL_FORALL,IN_DISJOINT]
      \\ rw [] \\ metis_tac [])
    \\ rename [‘(x,y) ∈ base_area (area a)’]
    \\ CCONTR_TAC \\ gvs []
    >- (gvs [base_area_def] \\ rw [] \\ metis_tac [])
    \\ gvs [io_cutout_iunion]
    \\ Cases_on ‘a = z’ >- gvs []
    \\ dxrule_at_then (Pos last) (dxrule_at (Pos last)) in_io_cutout_lemma
    \\ reverse impl_tac >- gvs []
    \\ gvs [SF SFY_ss]
    \\ ‘z ≠ a’ by gvs []
    \\ gvs [SF SFY_ss])
  \\ reverse conj_tac >- simp [SF SFY_ss, mods_wf_circ_mod]
  \\ simp [disjoint_mods_def,disjoint_mod_def,circ_mod_def]
  \\ simp [IN_DISJOINT]
  \\ rpt strip_tac \\ CCONTR_TAC \\ gvs []
  \\ rename [‘z ∈ circ_area (area y) (ins y) (outs y) n’]
  \\ PairCases_on ‘z’
  \\ qabbrev_tac ‘b = (n MOD 60 < 30)’
  \\ first_x_assum (fn th => drule th \\ drule (GSYM th))
  \\ rpt strip_tac
  \\ ‘DISJOINT (base_area (area x)) (base_area (area y))’ by
    (simp [IN_DISJOINT,FORALL_PROD]
     \\ CCONTR_TAC \\ gvs []
     \\ ‘∀x y a. (x,y) ∈ area a ⇒ x % 2 = 0 ∧ y % 2 = 0’ by
       metis_tac [circ_mod_wf_def,PULL_EXISTS]
     \\ metis_tac [base_area_disjoint])
  \\ fs [circ_area_eq]
  >- (gvs [IN_DISJOINT] \\ metis_tac [])
  \\ last_assum $ qspec_then ‘x’ strip_assume_tac
  \\ last_x_assum $ qspec_then ‘y’ strip_assume_tac
  >- (gvs [SF DNF_ss] \\ drule_all in_io_cutout_lemma \\ gvs [])
  >- (gvs [SF DNF_ss] \\ drule_all in_io_cutout_lemma \\ gvs [])
  \\ gvs [io_cutout_def]
  \\ dxrule_then dxrule IN_circ_io_areas
  \\ strip_tac \\ gvs []
  >-
   (gvs [IN_DISJOINT]
    \\ ‘r1 = r2’ by (fs [circ_mod_wf_def] \\ metis_tac []) \\ BasicProvers.var_eq_tac
    \\ ntac 2 $ dxrule circ_mod_wf_imp \\ metis_tac [PAIR])
  >-
   (rpt $ dxrule circ_mod_wf_imp_dir_test
    \\ PairCases_on ‘r1’ \\ PairCases_on ‘r2’
    \\ rpt strip_tac \\ res_tac
    \\ imp_res_tac IN_dir_test
    \\ Cases_on ‘b’ \\ gvs [])
  >-
   (rpt $ dxrule circ_mod_wf_imp_dir_test
    \\ PairCases_on ‘r1’ \\ PairCases_on ‘r2’
    \\ rpt strip_tac \\ res_tac
    \\ imp_res_tac IN_dir_test
    \\ Cases_on ‘b’ \\ gvs [])
  >-
   (gvs [IN_DISJOINT]
    \\ ‘r1 = r2’ by (fs [circ_mod_wf_def] \\ metis_tac []) \\ BasicProvers.var_eq_tac
    \\ ntac 2 $ dxrule circ_mod_wf_imp \\ metis_tac [PAIR])
QED

Theorem circuit_run_compose_union:
  ∀a1 a2 ins1 ins2 outs1 outs2 init1 init2.
  (* each element in the family must be a circuit_run *)
  circuit_run a1 ins1 outs1 init1 ∧
  circuit_run a2 ins2 outs2 init2 ∧
  DISJOINT a1 a2 ∧
  (∀p d r.
     ((p,d,r) ∈ ins1  ∧ sub_pt p (dir_to_xy d) ∈ a2 ⇒ (p,d,r) ∈ outs2) ∧
     ((p,d,r) ∈ outs1 ∧ add_pt p (dir_to_xy d) ∈ a2 ⇒ (p,d,r) ∈ ins2) ∧
     ((p,d,r) ∈ ins2  ∧ sub_pt p (dir_to_xy d) ∈ a1 ⇒ (p,d,r) ∈ outs1) ∧
     ((p,d,r) ∈ outs2 ∧ add_pt p (dir_to_xy d) ∈ a1 ⇒ (p,d,r) ∈ ins1))
  ⇒
  circuit_run (a1 ∪ a2) (ins1 ∪ ins2) (outs1 ∪ outs2) (init1 ∪ init2)
Proof
  rpt gen_tac \\ strip_tac
  \\ qspecl_then [‘λb. if b then a1 else a2’,
                  ‘λb. if b then ins1 else ins2’,
                  ‘λb. if b then outs1 else outs2’,
                  ‘λb. if b then init1 else init2’]
       mp_tac circuit_run_compose_bigunion
  \\ impl_tac
  >- (rw [] \\ gvs [IN_DISJOINT] \\ metis_tac [])
  \\ gvs [iunion_if]
QED

Definition translate_set_def:
  translate_set x s a ⇔ sub_pt a x ∈ s
End

Theorem mem_translate_set[simp]:
  a ∈ translate_set x s ⇔ sub_pt a x ∈ s
Proof
  simp [IN_DEF, translate_set_def]
QED

Theorem translate_set_empty[simp]:
  translate_set p ∅ = ∅
Proof
  simp [EXTENSION]
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

Definition translate_port_def:
  translate_port x s (a,d:dir,r) ⇔ (sub_pt a x,d,r) ∈ s
End

Theorem mem_translate_port[simp]:
  (a,d,r) ∈ translate_port x s ⇔ (sub_pt a x,d,r) ∈ s
Proof
  simp [IN_DEF, translate_port_def]
QED

Theorem live_adj_translate:
  live_adj (translate_set (p0,p1) s) x0 x1 = live_adj s (x0-p0) (x1-p1)
Proof
  rewrite_tac [live_adj_eq, translate_set_def, IN_DEF, sub_pt_def]
  \\ rpt (reverse (cong_tac 1)
    >- (simp [] \\ cong_tac 2 \\ simp [] \\ ARITH_TAC))
QED

Theorem infl_translate[simp]:
  infl (translate_set p s) = translate_set p (infl s)
Proof
  PairCases_on `p`
  \\ simp [Once EXTENSION, FORALL_PROD, infl_def, IN_DEF, translate_set_def,
    live_adj_translate]
QED

Theorem translate_subset[simp]:
  translate_set p s ⊆ translate_set p t ⇔ s ⊆ t
Proof
  `∀x p. x + p - p = x ∧ x - p + p = x` by ARITH_TAC
  \\ PairCases_on `p` \\ simp [SUBSET_DEF, FORALL_PROD] \\ metis_tac []
QED

Theorem step_translate[simp]:
  step (translate_set p s) = translate_set p (step s)
Proof
  PairCases_on `p`
  \\ rw [Once EXTENSION, FORALL_PROD, IN_step, live_adj_translate]
QED

Theorem translate_set_inter:
  translate_set p (a ∩ b) = translate_set p a ∩ translate_set p b
Proof
  simp [EXTENSION, FORALL_PROD]
QED

Theorem translate_set_union:
  translate_set p (a ∪ b) = translate_set p a ∪ translate_set p b
Proof
  simp [EXTENSION, FORALL_PROD]
QED

Theorem translate_set_diff:
  translate_set p (a DIFF b) = translate_set p a DIFF translate_set p b
Proof
  simp [EXTENSION, FORALL_PROD]
QED

Theorem io_step_translate_mod:
  io_step mod s t ⇒
  io_step (translate_mod p mod) (translate_set p s) (translate_set p t)
Proof
  simp [io_step_def, translate_mod_def, GSYM translate_set_inter,
    GSYM translate_set_union, GSYM translate_set_diff]
QED

Theorem io_steps_translate_mods:
  io_steps k mod n s t ⇒
  io_steps k (translate_mods p mod) n (translate_set p s) (translate_set p t)
Proof
  MAP_EVERY qid_spec_tac [`n`,`s`] \\ Induct_on `k`
  \\ simp [io_steps_def, translate_mods_def]
  \\ metis_tac [io_step_translate_mod]
QED

Theorem run_to_translate_mods:
  run_to k mod s t ⇒
  run_to k (translate_mods p mod) (translate_set p s) (translate_set p t)
Proof
  rw [run_to_def, io_steps_translate_mods]
QED

Theorem run_translate_mods:
  run mod init ⇒
  run (translate_mods p mod) (translate_set p init)
Proof
  rw [run_def] \\ metis_tac [run_to_translate_mods]
QED

Theorem translate_port_empty[simp]:
  translate_port p ∅ = ∅
Proof
  simp [EXTENSION, FORALL_PROD]
QED

Theorem translate_port_union[simp]:
  translate_port p (a ∪ b) = translate_port p a ∪ translate_port p b
Proof
  simp [EXTENSION, FORALL_PROD]
QED

Theorem translate_port_inter[simp]:
  translate_port p (a ∩ b) = translate_port p a ∩ translate_port p b
Proof
  simp [EXTENSION, FORALL_PROD]
QED

Theorem translate_port_is_ns[simp]:
  translate_port p is_ns = is_ns
Proof
  simp [EXTENSION, FORALL_PROD, is_ns_def, IN_DEF]
QED

Theorem translate_port_is_ew[simp]:
  translate_port p is_ew = is_ew
Proof
  simp [EXTENSION, FORALL_PROD, is_ew_def, IN_DEF]
QED

Theorem image_lwss_translate:
  U (IMAGE (lwss_at n) (translate_port p ins)) =
    translate_set (mul_pt 75 p) (U (IMAGE (lwss_at n) ins))
Proof
  PairCases_on `p`
  \\ `∀x0 x1 y0 y1 d r. (x0-75*p0,x1-75*p1) ∈ lwss_at n ((y0,y1),d,r) ⇔
      (x0,x1) ∈ lwss_at n ((y0+p0,y1+p1),d,r)` suffices_by (
    `∀x p. x + p - p = x ∧ x - p + p = x` by ARITH_TAC
    \\ simp [Once EXTENSION, FORALL_PROD, EXISTS_PROD] \\ metis_tac [])
  \\ rw [lwss_at_def, lwss_as_set_def]
  \\ CONV_TAC $ LHS_CONV $ REWR_CONV $
    GSYM $ Q.SPECL [`75*p0`,`75*p1`] from_rows_translate
  \\ cong_tac 2 >>> NTH_GOAL (cong_tac 2) 3 \\ ARITH_TAC
QED

Theorem circ_io_lwss_translate:
  translate_set (mul_pt 75 p) (circ_io_lwss ins n) =
    circ_io_lwss (translate_port p ins) n
Proof
  rw [circ_io_lwss_def, GSYM image_lwss_translate]
QED

Theorem box_translate:
  translate_set p (box x sz) = box (add_pt x p) sz
Proof
  MAP_EVERY PairCases_on [`p`,`x`,`sz`]
  \\ rw [Once EXTENSION, FORALL_PROD, box_def]
  \\ cong_tac 6 \\ ARITH_TAC
QED

Theorem io_box_translate:
  translate_set (mul_pt 75 p) (io_box x) = io_box (add_pt x p)
Proof
  PairCases_on `p` \\ PairCases_on `x`
  \\ rw [io_box_def, box_translate]
  \\ cong_tac 3 \\ ARITH_TAC
QED

Theorem circ_io_area_translate:
  translate_set (mul_pt 75 p) (circ_io_area outs) =
    circ_io_area (translate_port p outs)
Proof
  rw [Once EXTENSION, PULL_EXISTS, EXISTS_PROD, circ_io_area_def]
  \\ PairCases_on `p`
  \\ rewrite_tac [GSYM mem_translate_set, io_box_translate] \\ simp []
  \\ metis_tac [ARITH_PROVE ``∀x p:int. x + p - p = x ∧ x - p + p = x``]
QED

Theorem circ_output_area_translate:
  translate_set (mul_pt 75 p) (circ_output_area outs n) =
    circ_output_area (translate_port p outs) n
Proof
  rw [circ_output_area_def, circ_io_lwss_translate, circ_io_area_translate]
QED

Theorem base_area_translate:
  translate_set (mul_pt 75 p) (base_area area) =
    base_area (translate_set p area)
Proof
  rw [Once EXTENSION, PULL_EXISTS, base_area_def]
  \\ PairCases_on `p`
  \\ rewrite_tac [GSYM mem_translate_set, box_translate] \\ simp []
  \\ metis_tac [ARITH_PROVE ``∀x p:int. x + p - p = x ∧ x - p + p = x ∧
    75 * x − 75 + 75 * p = 75 * (x + p) - 75``]
QED

Theorem translate_port_dir_test[simp]:
  translate_port p (dir_test phase) = dir_test phase
Proof
  rw [dir_test_def]
QED

Theorem io_cutout_translate:
  translate_set (mul_pt 75 p) (io_cutout ins outs phase) =
    io_cutout (translate_port p ins) (translate_port p outs) phase
Proof
  rw [io_cutout_def, circ_io_area_translate]
QED

Theorem circ_area_translate:
  translate_set (mul_pt 75 p) (circ_area area ins outs n) =
    circ_area (translate_set p area)
      (translate_port p ins) (translate_port p outs) n
Proof
  rw [circ_area_eq, translate_set_union, translate_set_diff,
    base_area_translate, io_cutout_translate]
QED

Theorem translate_circ_mod:
  translate_mods (mul_pt 75 p) (circ_mod area ins outs) =
  circ_mod (translate_set p area) (translate_port p ins) (translate_port p outs)
Proof
  rw [FUN_EQ_THM, circ_mod_def, translate_mods_def, translate_mod_def,
    circ_io_lwss_translate, circ_output_area_translate, circ_area_translate]
QED

Theorem circuit_run_translate:
  FST p % 2 = 0 ∧ SND p % 2 = 0 ∧
  circuit_run area ins outs init ⇒
  circuit_run (translate_set p area)
    (translate_port p ins) (translate_port p outs)
    (translate_set (mul_pt 75 p) init)
Proof
  rw [circuit_run_def]
  >- simp [FORALL_BOOL, iffLR DISJOINT_SYM, iunion_if,
    GSYM translate_circ_mod, run_translate_mods]
  \\ PairCases_on `p` \\ fs [circ_mod_wf_def, FORALL_PROD]
  \\ conj_tac >- (ntac 3 strip_tac \\ last_x_assum drule \\ ARITH_TAC)
  \\ `∀x0 x1 d. add_pt (x0-p0,x1-p1) d = sub_pt (add_pt (x0,x1) d) (p0,p1) ∧
      sub_pt (x0-p0,x1-p1) d = sub_pt (sub_pt (x0,x1) d) (p0,p1)` by (
    simp [FORALL_PROD] \\ ARITH_TAC)
  \\ metis_tac []
QED

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
