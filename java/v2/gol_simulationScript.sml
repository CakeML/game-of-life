(*
  Definitions that help simulation
*)
open preamble gol_rulesTheory gol_simTheory;

val _ = new_theory "gol_simulation";

(* simulating a grid of optional booleans *)

Definition bool_def[simp]:
  bool NONE = F ∧
  bool (SOME b) = b
End

Definition next_row_def:
  (next_row (x1::x2::x3::xs) (y1::y2::y3::ys) (z1::z2::z3::zs) (q::qs) ⇔
     gol (bool x1) (bool x2) (bool x3)
         (bool y1) (bool y2) (bool y3)
         (bool z1) (bool z2) (bool z3) = bool q ∧
     next_row (x2::x3::xs) (y2::y3::ys) (z2::z3::zs) qs) ∧
  (next_row (x1::x2::[]) (y1::y2::[]) (z1::z2::[]) (q::[]) ⇔
     gol (bool x1) (bool x2) F
         (bool y1) (bool y2) F
         (bool z1) (bool z2) F = bool q) ∧
  (next_row _ _ _ _ ⇔ F)
End

Definition next_frame_def:
  (next_frame (x::y::z::xs) (q::qs) ⇔
     next_row (NONE :: x) (NONE :: y) (NONE :: z) q ∧
     next_frame (y::z::xs) qs) ∧
  (next_frame (x::y::[]) (q::[]) ⇔
     next_row (NONE :: x) (NONE :: y) (NONE :: MAP (K NONE) y) q) ∧
  (next_frame _ _ ⇔ F)
End

Definition next_sim_def:
  next_sim (x::xs) qs = next_frame (MAP (K NONE) x :: x :: xs) qs
End


(* from_row/frame *)

Definition from_row_def:
  from_row x y [] = [] ∧
  from_row x y (NONE::ts) = from_row (x+1) y ts ∧
  from_row x y (SOME b::ts) = ((x:int,y:int),b) :: from_row (x+1) y ts
End

Definition from_frame_def:
  from_frame x y [] = [] ∧
  from_frame x y (r::rows) = from_row x y r ++ from_frame x (y+1) rows
End


(* dimensions of the frame *)

Definition frame_ok_def:
  frame_ok (w,h) xs ⇔
    LENGTH xs = h ∧ h ≠ 0 ∧
    EVERY (λx. LENGTH x = w) xs ∧ w ≠ 0
End

Triviality next_row_length:
  ∀xs ys zs x y z qs n.
    next_row (x::xs) (y::ys) (z::zs) qs ∧
    LENGTH xs = LENGTH ys ∧ xs ≠ [] ∧
    LENGTH xs = LENGTH zs ∧ n = LENGTH xs ⇒
    LENGTH qs = n
Proof
  Induct \\ fs []
  \\ Cases_on ‘ys’ \\ fs []
  \\ Cases_on ‘zs’ \\ fs []
  \\ Cases_on ‘qs’ \\ fs [next_row_def]
  \\ Cases_on ‘xs = []’
  >- (rename [‘next_row _ _ _ (h5::t5)’] \\ Cases_on ‘t5’ \\ gvs [next_row_def])
  \\ Cases_on ‘xs’ \\ fs []
  \\ Cases_on ‘t’ \\ Cases_on ‘t'’ \\ gvs []
  \\ fs [next_row_def] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem frame_ok_next_sim:
  next_sim xs ys ∧ frame_ok (w,h) xs ⇒
  frame_ok (w,h) ys
Proof
  Cases_on ‘xs’ \\ fs [next_sim_def,frame_ok_def] \\ strip_tac
  \\ rename [‘LENGTH h = w’]
  \\ qsuff_tac ‘
    ∀xs ys.
      next_frame xs ys ∧ EVERY (λx. LENGTH x = LENGTH h ∧ x ≠ []) xs ∧ 1 < LENGTH xs ⇒
      LENGTH ys + 1 = LENGTH xs ∧
      EVERY (λx. LENGTH x = LENGTH h) ys’
  >-
   (disch_then drule \\ fs [ADD1]
    \\ disch_then irule  \\ CCONTR_TAC \\ gvs []
    \\ gvs [EVERY_MEM,EXISTS_MEM]
    \\ res_tac \\ fs [])
  \\ rpt $ pop_assum kall_tac
  \\ gen_tac
  \\ completeInduct_on ‘LENGTH xs’ \\ fs []
  \\ rpt gen_tac \\ strip_tac \\ gvs [PULL_FORALL]
  \\ strip_tac
  \\ Cases_on ‘xs’ \\ fs []
  \\ rename [‘next_frame (x::ys)’]
  \\ Cases_on ‘ys’ \\ fs []
  \\ rename [‘next_frame (x::y::zs) qs’]
  \\ Cases_on ‘zs’ \\ gvs [next_frame_def,ADD1]
  >-
   (Cases_on ‘qs’ \\ gvs [next_frame_def,ADD1]
    \\ Cases_on ‘t’ \\ gvs [next_frame_def,ADD1]
    \\ rw [] \\ drule next_row_length \\ rw [])
  \\ Cases_on ‘qs’ \\ gvs [next_frame_def,ADD1]
  \\ strip_tac \\ gvs []
  \\ drule next_row_length
  \\ strip_tac \\ gvs []
  \\ first_x_assum $ drule_at $ Pos $ el 2
  \\ gvs []
QED

(* simulation is accurate if the borders are NONE initially *)

Definition frame_borders_none_def:
  frame_borders_none xs ⇔
    EVERY IS_NONE (HD xs) ∧
    EVERY IS_NONE (LAST xs) ∧
    EVERY (IS_NONE o HD) xs ∧
    EVERY (IS_NONE o LAST) xs
End

Definition to_state_def:
  to_state xs = { p | MEM (p,T) xs } : gol_rules$state
End

Theorem IN_to_state:
  (x,y) IN to_state xs ⇔ MEM ((x,y),T) xs
Proof
  fs [to_state_def]
QED

Theorem to_state_thm:
  to_state xs (x,y) ⇔ MEM ((x,y),T) xs
Proof
  fs [GSYM IN_to_state,IN_DEF]
QED

Triviality MEM_from_row:
  ∀h x y ax ay.
    MEM ((ax,ay),T) (from_row x y h) ⇔
    ∃m. ay = y ∧ ax − x = &m ∧ m < LENGTH h ∧ EL m h = SOME T
Proof
  Induct \\ fs [from_row_def]
  \\ Cases \\ fs [from_row_def]
  \\ rw [] \\ eq_tac \\ rw []
  >- (qexists_tac ‘SUC m’ \\ fs [ADD1] \\ intLib.COOPER_TAC)
  >- (Cases_on ‘m’ \\ fs [] \\ first_x_assum $ irule_at $ Pos last \\ fs []
      \\ intLib.COOPER_TAC)
  >- (qexists_tac ‘SUC m’ \\ fs [ADD1] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘m’ \\ fs [] \\ disj2_tac
  \\ first_x_assum $ irule_at $ Pos last \\ fs []
  \\ intLib.COOPER_TAC
QED

Theorem MEM_from_frame:
  ∀xs x y ax ay w h.
    frame_ok (w,h) xs ⇒
    (MEM ((ax,ay),T) (from_frame x y xs) =
     ∃m n.
       ax - x = & m ∧
       ay - y = & n ∧
       m < w ∧ n < h ∧
       EL m (EL n xs) = SOME T)
Proof
  qsuff_tac ‘
   ∀xs x y ax ay w h.
     LENGTH xs = h ∧ EVERY (λx. LENGTH x = w) xs ⇒
     (MEM ((ax,ay),T) (from_frame x y xs) =
      ∃m n.
        ax - x = & m ∧
        ay - y = & n ∧
        m < w ∧ n < h ∧
        EL m (EL n xs) = SOME T)’
  >- fs [frame_ok_def]
  \\ Induct
  \\ fs [from_frame_def] \\ rw []
  \\ Cases_on ‘ay = y’ \\ gvs [MEM_from_row]
  >- (res_tac \\ fs [])
  \\ first_x_assum drule
  \\ strip_tac \\ fs []
  \\ eq_tac \\ rw []
  >- (qexists_tac ‘m’ \\ qexists_tac ‘SUC n’ \\ fs [] \\ intLib.COOPER_TAC)
  \\ qexists_tac ‘m’ \\ fs []
  \\ Cases_on ‘n’ \\ fs []
  \\ first_x_assum $ irule_at $ Pos last \\ fs []
  \\ intLib.COOPER_TAC
QED

Definition el_el_def:
  el_el x y xd yd ys ⇔
    xd ≤ x ∧ yd ≤ y ∧
    y-yd < LENGTH ys ∧
    x-xd < LENGTH (EL (y-yd) ys) ∧
    EL (x-xd) (EL (y-yd) ys) = SOME T
End

Theorem next_sim_gol[local]:
  next_sim xs ys ∧ frame_ok (w,h) xs ⇒
  (EL nx (EL ny ys) = SOME T ⇔
   gol (el_el nx ny     1 1 xs) (el_el nx ny     0 1 xs) (el_el (nx+1) ny     0 1 xs)
       (el_el nx ny     1 0 xs) (el_el nx ny     0 0 xs) (el_el (nx+1) ny     0 0 xs)
       (el_el nx (ny+1) 1 0 xs) (el_el nx (ny+1) 0 0 xs) (el_el (nx+1) (ny+1) 0 0 xs))
Proof
  cheat
QED

Theorem step_from_frame:
  next_sim xs ys ∧ frame_borders_none xs ∧ frame_ok (w,h) xs ⇒
  step (to_state (from_frame x y xs)) = to_state (from_frame x y ys)
Proof
  rw [EXTENSION,FORALL_PROD]
  \\ rename [‘(ax,ay) IN _’]
  \\ fs [IN_step,IN_to_state]
  \\ drule_all frame_ok_next_sim \\ strip_tac
  \\ dxrule MEM_from_frame
  \\ drule MEM_from_frame
  \\ rpt strip_tac \\ fs []
  \\ Cases_on ‘ax < x’
  >-
   (qsuff_tac ‘live_adj (to_state (from_frame x y xs)) ax ay = 0’
    >- (fs [] \\ CCONTR_TAC \\ fs [] \\ intLib.COOPER_TAC)
    \\ fs [live_adj_def,to_state_thm]
    \\ CCONTR_TAC \\ gvs []
    \\ rpt intLib.COOPER_TAC
    \\ ‘m = 0’ by intLib.COOPER_TAC
    \\ gvs []
    \\ gvs [frame_borders_none_def,frame_ok_def]
    \\ gvs [EVERY_EL])
  \\ Cases_on ‘ay < y’
  >-
   (qsuff_tac ‘live_adj (to_state (from_frame x y xs)) ax ay = 0’
    >- (fs [] \\ CCONTR_TAC \\ fs [] \\ intLib.COOPER_TAC)
    \\ fs [live_adj_def,to_state_thm]
    \\ CCONTR_TAC \\ gvs []
    \\ rpt intLib.COOPER_TAC
    \\ ‘n = 0’ by intLib.COOPER_TAC
    \\ gvs []
    \\ gvs [frame_borders_none_def,frame_ok_def]
    \\ Cases_on ‘xs’ \\ gvs []
    \\ gvs [EVERY_EL])
  \\ ‘0 ≤ ax - x’ by intLib.COOPER_TAC
  \\ dxrule integerTheory.NUM_POSINT_EXISTS
  \\ ‘0 ≤ ay - y’ by intLib.COOPER_TAC
  \\ dxrule integerTheory.NUM_POSINT_EXISTS
  \\ strip_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ rename [‘EL nx (EL ny xs) = SOME T’]
  \\ ‘ay = y + &ny ∧ ax = x + &nx’ by intLib.COOPER_TAC \\ gvs []
  \\ reverse $ Cases_on ‘nx < w’
  >-
   (‘live_adj (to_state (from_frame x y xs)) (x + &nx) (y + &ny) = 0’ suffices_by fs []
    \\ fs [live_adj_def,to_state_thm]
    \\ CCONTR_TAC \\ gvs []
    \\ rpt intLib.COOPER_TAC
    \\ ‘m = w-1’ by intLib.COOPER_TAC \\ gvs []
    \\ gvs [frame_borders_none_def,frame_ok_def]
    \\ qpat_x_assum ‘EVERY (IS_NONE ∘ LAST) xs’ mp_tac
    \\ rewrite_tac [EVERY_EL] \\ strip_tac
    \\ pop_assum drule \\ strip_tac \\ fs []
    \\ qpat_x_assum ‘EVERY (λx. LENGTH x = w) xs’ mp_tac
    \\ rewrite_tac [EVERY_EL] \\ strip_tac
    \\ pop_assum drule \\ strip_tac \\ fs []
    \\ rename [‘LAST xx’]
    \\ Cases_on ‘xx’ using SNOC_CASES \\ fs []
    \\ gvs [SNOC_APPEND,EL_LENGTH_APPEND])
  \\ reverse $ Cases_on ‘ny < h’
  >-
   (‘live_adj (to_state (from_frame x y xs)) (x + &nx) (y + &ny) = 0’ suffices_by fs []
    \\ fs [live_adj_def,to_state_thm]
    \\ CCONTR_TAC \\ gvs []
    \\ rpt intLib.COOPER_TAC
    \\ ‘n = h-1’ by intLib.COOPER_TAC \\ gvs []
    \\ gvs [frame_borders_none_def,frame_ok_def]
    \\ Cases_on ‘xs’ using SNOC_CASES \\ fs []
    \\ gvs [SNOC_APPEND,EL_LENGTH_APPEND]
    \\ gvs [EVERY_EL])
  \\ fs []
  \\ simp [live_adj_def,to_state_thm]
  \\ ‘∀(x:int) a. x + &a + 1 − x = & (a + 1)’ by intLib.COOPER_TAC \\ fs []
  \\ ‘∀(x:int) a. x + &a − x = & a’ by intLib.COOPER_TAC \\ fs []
  \\ ‘∀(x:int) n m. x + &n − 1 − x = &m ⇔ m = n - 1 ∧ n ≠ 0’ by intLib.COOPER_TAC \\ fs []
  \\ gvs [] \\ rewrite_tac [ADD_ASSOC]
  \\ drule_all next_sim_gol
  \\ disch_then $ rewrite_tac o single
  \\ fs [gol_def]
  \\ fs [el_el_def]
  \\ ‘∀ny. ny < LENGTH xs ⇒ LENGTH (EL ny xs) = w’ by fs [frame_ok_def,EVERY_EL]
  \\ fs []
  \\ ‘LENGTH xs = h’ by fs [frame_ok_def]
  \\ full_simp_tac std_ss [SF CONJ_ss,DECIDE “1 ≤ nx ⇔ nx:num ≠ 0”]
  \\ pop_assum kall_tac
  \\ ‘0 < h ∧ 0 < w’ by fs [frame_ok_def]
  \\ full_simp_tac std_ss [AC CONJ_COMM CONJ_ASSOC]
  \\ full_simp_tac std_ss [AC ADD_COMM ADD_ASSOC]
  \\ IF_CASES_TAC \\ fs []
QED


(* important definitions *)


Definition gol_simulation_def:
  (gol_simulation [] ⇔ T) ∧
  (gol_simulation [x] ⇔ T) ∧
  (gol_simulation (x::y::ys) ⇔
     step (to_state x) = to_state y ∧
     gol_simulation (y::ys))
End

(*  *)


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
