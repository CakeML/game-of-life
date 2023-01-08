(*
  Definitions that help simulation
*)
open preamble gol_rulesTheory gol_coreTheory;

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

Definition next_row'_def:
  (next_row' (x1::x2::x3::xs) (y1::y2::y3::ys) (z1::z2::z3::zs) (q::qs) ⇔
     gol (bool x1) (bool x2) (bool x3)
         (bool y1) (bool y2) (bool y3)
         (bool z1) (bool z2) (bool z3) = bool q ∧
     next_row' (x2::x3::xs) (y2::y3::ys) (z2::z3::zs) qs) ∧
  (next_row' (x1::x2::[]) (y1::y2::[]) (z1::z2::[]) [] ⇔ T) ∧
  (next_row' _ _ _ _ ⇔ F)
End

Definition next_frame'_def:
  (next_frame' (x::y::z::xs) (q::qs) ⇔
     next_row' x y z q ∧ next_frame' (y::z::xs) qs) ∧
  (next_frame' (x::y::[]) [] ⇔ T) ∧
  (next_frame' _ _ ⇔ F)
End

Overload bel = “λx y xs. bool (EL x (EL y xs))”

Triviality list_split3:
  SUC n < LENGTH xs ∧ n ≠ 0 ⇒
  ∃ys y1 y2 y3 zs.
    xs = ys ++ y1::y2::y3::zs ∧
    n = LENGTH ys + 1
Proof
  rw []
  \\ drule miscTheory.LESS_LENGTH
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘ys1’ using SNOC_CASES >- fs []
  \\ gvs []
  \\ Cases_on ‘l’ using SNOC_CASES >- fs []
  \\ full_simp_tac std_ss [SNOC_APPEND]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [LENGTH_APPEND]
  \\ metis_tac []
QED

Triviality EL_lemma:
  EL (LENGTH xs) (xs ++ y::ys) = y ∧
  EL (SUC (LENGTH xs)) (xs ++ y::y1::ys) = y1 ∧
  EL (SUC (SUC (LENGTH xs))) (xs ++ y::y1::y2::ys) = y2
Proof
  Induct_on ‘xs’ \\ fs []
QED

Theorem next_frame'_gol[local]:
  ∀xs ys nx ny.
    next_frame' xs ys ∧ xs ≠ [] ∧
    EVERY (λx. LENGTH x = LENGTH (HD xs)) xs ∧
    ny ≠ 0 ∧ nx ≠ 0 ∧
    ny + 1 < LENGTH xs ∧ nx + 1 < LENGTH (EL ny xs) ⇒
    (EL (nx-1) (EL (ny-1) ys) = SOME T ⇔
     gol (bel (nx-1) (ny-1) xs) (bel nx (ny-1) xs) (bel (nx+1) (ny-1) xs)
         (bel (nx-1) ny     xs) (bel nx ny     xs) (bel (nx+1) ny     xs)
         (bel (nx-1) (ny+1) xs) (bel nx (ny+1) xs) (bel (nx+1) (ny+1) xs))
Proof
  rw []
  \\ pop_assum mp_tac \\ fs [GSYM ADD1]
  \\ drule_all list_split3
  \\ qabbrev_tac ‘k = LENGTH (HD xs)’
  \\ strip_tac \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ rewrite_tac [GSYM ADD1,EL_lemma]
  \\ strip_tac
  \\ drule_all list_split3
  \\ ‘SUC nx < LENGTH y1’ by fs []
  \\ drule_all list_split3
  \\ ‘SUC nx < LENGTH y3’ by fs []
  \\ drule_all list_split3
  \\ rpt strip_tac \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ rewrite_tac [GSYM ADD1,EL_lemma]
  \\ rename [‘rs1 ++
              (xs ++ x0::x1::x2::xs1)::
              (ys ++ y0::y1::y2::ys1)::
              (zs ++ z0::z1::z2::zs1)::rs2’]
  \\ ‘LENGTH xs = LENGTH ys’ by fs [] \\ fs [EL_lemma]
  \\ ‘LENGTH ys = LENGTH zs’ by fs [] \\ fs [EL_lemma]
  \\ gvs []
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘ys'’
  \\ qid_spec_tac ‘rs1’
  \\ Induct
  \\ Cases_on ‘ys'’
  \\ fs [next_frame'_def]
  >-
   (rw [] \\ qpat_x_assum ‘next_row' _ _ _ _’ mp_tac
    \\ qpat_x_assum ‘LENGTH _ = LENGTH _ ’ mp_tac
    \\ qpat_x_assum ‘LENGTH _ = LENGTH _ ’ mp_tac
    \\ qid_spec_tac ‘h’
    \\ qid_spec_tac ‘zs’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ gvs []
    >-
     (Cases \\ fs [next_row'_def]
      \\ rename [‘h = SOME _’] \\ Cases_on ‘h’ \\ fs [])
    \\ gen_tac \\ Cases \\ gvs [] \\ Cases \\ fs []
    \\ gvs [next_row'_def]
    \\ rename [‘LENGTH ts1 = LENGTH ts2 ⇒ LENGTH ts3 = _ ⇒ _’]
    \\ Cases \\ fs [next_row'_def]
    >- (Cases_on ‘ts1’ \\ Cases_on ‘ts2’ \\ Cases_on ‘ts3’ \\ fs [next_row'_def]
        \\ rename [‘_ (_::_::(ts1++_)) (_::_::(ts2++_)) (_::_::(ts3++_))’]
        \\ Cases_on ‘ts1’ \\ Cases_on ‘ts2’ \\ Cases_on ‘ts3’ \\ fs [next_row'_def])
    \\ rw []
    \\ rename [‘_ (_::(ts1++_)) (_::(ts2++_)) (_::(ts3++_)) _’]
    \\ first_x_assum irule \\ fs []
    \\ qexists_tac ‘ts2’ \\ fs []
    \\ Cases_on ‘ts1’ \\ Cases_on ‘ts2’ \\ Cases_on ‘ts3’ \\ fs [next_row'_def]
    \\ Cases_on ‘t'’ \\ fs [next_row'_def]
    \\ rename [‘_ (_::_::(ts1++_)) (_::_::(ts2++_)) (_::_::(ts3++_))’]
    \\ Cases_on ‘ts1’ \\ Cases_on ‘ts2’ \\ Cases_on ‘ts3’ \\ fs [next_row'_def])
  >- (Cases_on ‘rs1'’ \\ fs [next_frame'_def]
      \\ Cases_on ‘t’ \\ fs [next_frame'_def])
  \\ Cases_on ‘rs1'’ \\ fs []
  >-
   (fs [next_frame'_def]
    \\ Cases_on ‘t’ \\ fs [next_frame'_def] \\ rw [] \\ fs [])
  \\ Cases_on ‘t'’ \\ fs [next_frame'_def]
QED

Triviality MAP_K_eq_REPLICATE_LENGTH:
  ∀xs x. MAP (K x) xs = REPLICATE (LENGTH xs) x
Proof
  Induct \\ fs []
QED

Theorem next_row_imp_next_row':
  ∀xs ys zs rs.
    next_row xs ys zs rs ⇒
    next_row' (xs ++ [NONE]) (ys ++ [NONE]) (zs ++ [NONE]) rs ∧
    LENGTH xs = LENGTH ys
Proof
  Induct >- fs [next_row_def]
  \\ rpt gen_tac
  \\ simp [Once (DefnBase.one_line_ify NONE next_row_def)]
  \\ every_case_tac \\ fs []
  \\ fs [next_row'_def,next_row_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem next_sim_imp_next_frame':
  next_sim xs ys ∧ xs ≠ [] ⇒
  next_frame' ([NONE::REPLICATE (LENGTH (HD xs)) NONE ++ [NONE]] ++
               MAP (λx. [NONE] ++ x ++ [NONE]) xs ++
               [NONE::REPLICATE (LENGTH (HD xs)) NONE ++ [NONE]]) ys
Proof
  Cases_on ‘xs’ \\ fs [next_sim_def]
  \\ qsuff_tac ‘
       ∀xs ys.
         next_frame xs ys ∧ 2 ≤ LENGTH xs ⇒
         next_frame' (MAP (λx. NONE::(x ++ [NONE])) xs ++
                      [NONE::(REPLICATE (LENGTH (HD xs)) NONE ++ [NONE])]) ys’
  >- (rw [] \\ first_x_assum drule \\ fs [MAP_K_eq_REPLICATE_LENGTH])
  \\ Induct >- fs []
  \\ Cases_on ‘xs’ >- fs []
  \\ Cases_on ‘t’ \\ rw []
  >-
   (Cases_on ‘ys’ \\ fs [next_frame_def]
    \\ Cases_on ‘t’ \\ fs [next_frame_def]
    \\ fs [next_frame'_def,MAP_K_eq_REPLICATE_LENGTH]
    \\ drule next_row_imp_next_row' \\ fs [])
  \\ Cases_on ‘ys’ \\ fs [next_frame_def]
  \\ fs [next_frame'_def]
  \\ drule next_row_imp_next_row' \\ fs []
QED

Theorem next_sim_gol[local]:
  next_sim xs ys ∧ frame_ok (w,h) xs ∧
  ny < LENGTH xs ∧ nx < LENGTH (EL ny xs) ⇒
  (EL nx (EL ny ys) = SOME T ⇔
   gol (el_el nx ny     1 1 xs) (el_el nx ny     0 1 xs) (el_el (nx+1) ny     0 1 xs)
       (el_el nx ny     1 0 xs) (el_el nx ny     0 0 xs) (el_el (nx+1) ny     0 0 xs)
       (el_el nx (ny+1) 1 0 xs) (el_el nx (ny+1) 0 0 xs) (el_el (nx+1) (ny+1) 0 0 xs))
Proof
  rw [] \\ Cases_on ‘xs = []’ >- fs []
  \\ drule_all next_sim_imp_next_frame' \\ strip_tac
  \\ drule next_frame'_gol
  \\ disch_then $ qspecl_then [‘nx+1’,‘ny+1’] mp_tac
  \\ impl_tac >- (fs [GSYM ADD1] \\ fs [EVERY_MAP,ADD1]
                  \\ fs [rich_listTheory.EL_APPEND1,EL_MAP]
                  \\ fs [frame_ok_def]
                  \\ Cases_on ‘xs’ \\ fs [])
  \\ strip_tac \\ fs []
  \\ pop_assum kall_tac
  \\ fs [GSYM ADD1,DECIDE “n+2 = SUC (SUC n)”]
  \\ irule $ prove(
       “x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧
        x4 = y4 ∧ x5 = y5 ∧ x6 = y6 ∧
        x7 = y7 ∧ x8 = y8 ∧ x9 = y9 ⇒
        gol x1 x2 x3 x4 x5 x6 x7 x8 x9 =
        gol y1 y2 y3 y4 y5 y6 y7 y8 y9”, fs [])
  \\ rpt strip_tac
  \\ fs [el_el_def]
  >-
   (Cases_on ‘ny’ \\ fs []
    \\ Cases_on ‘nx’ \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ ‘LENGTH (EL (SUC n) xs) = LENGTH (EL n xs)’ by fs [frame_ok_def,EVERY_EL]
    \\ strip_tac \\ gvs []
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (Cases_on ‘ny’ \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs []
    \\ ‘LENGTH (EL (SUC n) xs) = LENGTH (EL n xs)’ by fs [frame_ok_def,EVERY_EL]
    \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (Cases_on ‘ny’ \\ fs []
    >- (Cases_on ‘SUC nx = LENGTH $ HD xs’
        >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs [] \\ fs [EL_MAP])
        \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
        \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs [])
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ ‘LENGTH (EL (SUC n) xs) = LENGTH (EL n xs)’ by fs [frame_ok_def,EVERY_EL]
    \\ fs []
    \\ Cases_on ‘SUC nx = LENGTH (EL n xs)’
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs [] \\ fs [EL_MAP])
    \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ Cases_on ‘nx’ \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ Cases_on ‘EL nx (EL ny xs)’ \\ fs [])
  >-
   (DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ Cases_on ‘SUC nx = LENGTH (EL ny xs)’
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs [] \\ fs [EL_MAP])
    \\ fs []
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs [] \\ fs [EL_MAP]
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (Cases_on ‘SUC ny = LENGTH xs’ \\ fs []
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs []
        \\ Cases_on ‘nx’ \\ fs []
        \\ DEP_REWRITE_TAC [EL_APPEND1]
        \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs []
        \\ gvs [frame_ok_def,EVERY_EL] \\ Cases_on ‘xs’ \\ fs []
        \\ first_x_assum $ qspec_then ‘0’ mp_tac \\ fs [])
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs []
    \\ DEP_REWRITE_TAC [EL_MAP] \\ fs []
    \\ Cases_on ‘nx’ \\ fs []
    \\ Cases_on ‘n = LENGTH (EL (SUC ny) xs)’ \\ fs []
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs [])
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs []
    \\ ‘LENGTH (EL (SUC ny) xs) = LENGTH (EL ny xs)’ by fs [frame_ok_def,EVERY_EL]
    \\ fs []
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (Cases_on ‘SUC ny = LENGTH xs’ \\ fs []
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs []
        \\ DEP_REWRITE_TAC [EL_APPEND1]
        \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs []
        \\ gvs [frame_ok_def,EVERY_EL] \\ Cases_on ‘xs’ \\ fs []
        \\ first_x_assum $ qspec_then ‘0’ mp_tac \\ fs [])
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs []
    \\ DEP_REWRITE_TAC [EL_MAP] \\ fs []
    \\ ‘LENGTH (EL (SUC ny) xs) = LENGTH (EL ny xs)’ by fs [frame_ok_def,EVERY_EL]
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs []
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
  >-
   (Cases_on ‘SUC ny = LENGTH xs’ \\ fs []
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs []
        \\ Cases_on ‘SUC nx = LENGTH (HD xs)’
        >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs [])
        \\ DEP_REWRITE_TAC [EL_APPEND1]
        \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs []
        \\ gvs [frame_ok_def,EVERY_EL] \\ Cases_on ‘xs’ \\ fs []
        \\ first_x_assum $ qspec_then ‘0’ mp_tac \\ fs [])
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs []
    \\ DEP_REWRITE_TAC [EL_MAP] \\ fs []
    \\ Cases_on ‘SUC nx = LENGTH (EL (SUC ny) xs)’
    >- (DEP_REWRITE_TAC [EL_APPEND2] \\ fs [])
    \\ DEP_REWRITE_TAC [EL_APPEND1] \\ fs []
    \\ ‘LENGTH (EL (SUC ny) xs) = LENGTH (EL ny xs)’ by fs [frame_ok_def,EVERY_EL]
    \\ fs []
    \\ rename [‘bel n1 n2 xs’] \\ Cases_on ‘EL n1 (EL n2 xs)’ \\ fs [])
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
  \\ ‘ny < LENGTH xs ∧ nx < LENGTH (EL ny xs)’ by fs [frame_ok_def,EVERY_EL]
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

Theorem step_from_frame_200_200:
  ∀xs ys.
    next_sim xs ys ∧ frame_borders_none xs ∧ frame_ok (200,200) xs ⇒
    step (to_state (from_frame (-100) (-100) xs)) = to_state (from_frame (-100) (-100) ys)
Proof
  rw [] \\ drule_all step_from_frame \\ fs []
QED

Theorem next_row_none:
  next_row (NONE::NONE::NONE::xs)
           (NONE::NONE::NONE::ys)
           (NONE::NONE::NONE::zs)
           (NONE::rs) =
  next_row (NONE::NONE::xs)
           (NONE::NONE::ys)
           (NONE::NONE::zs)
           rs ∧
  next_row (NONE::NONE::[])
           (NONE::NONE::[])
           (NONE::NONE::[])
           (NONE::[]) = T
Proof
  fs [next_row_def,gol_simp]
QED

Inductive steps_sim:
[~base:]
  (∀w h policy xs.
     frame_ok (w,h) xs ⇒
     steps_sim w h policy 0n xs xs) ∧
[~step:]
  (∀w h policy xs ys zs.
     steps_sim w h policy n xs ys ∧
     frame_borders_none ys ∧
     policy n ys ∧
     next_sim ys zs ⇒
     steps_sim w h policy (n+1) xs zs)
End

Theorem steps_sim_step_thm:
  steps_sim w h policy n xs ys ⇒
  ∀zs.
    frame_borders_none ys ∧
    policy n ys ∧
    next_sim ys zs ⇒
    steps_sim w h policy (n+1) xs zs
Proof
  rw [] \\ drule_all steps_sim_step   \\ fs []
QED

val _ = export_theory();
