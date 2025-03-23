(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open HolKernel bossLib boolLib Parse;
open arithmeticTheory alistTheory gol_rulesTheory gol_lemmasTheory;

val _ = new_theory "gol_sim";

Datatype:
  dir = N | S | W | E
End

Definition dir_to_xy_def[simp]:
  dir_to_xy N = (0,-1) ∧
  dir_to_xy S = (0,1) ∧
  dir_to_xy E = (1,0) ∧
  dir_to_xy W = (-1,0)
End

Definition is_ns_def:
  is_ns (p,d,r) = (d = N ∨ d = S)
End

Definition is_ew_def:
  is_ew (p,d,r) = (d = E ∨ d = W)
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

Definition mul_pt_def[simp]:
  mul_pt (n:int) (a, b) ⇔ (n * a, n * b)
End

Datatype:
  var = A | B
End

Datatype:
  bexp = True | False | Var var num
       | Not bexp | And bexp bexp | Or bexp bexp
End

Definition eval_def[simp]:
  eval env True      = T ∧
  eval env False     = F ∧
  eval env (Var v n) = env (v,n) ∧
  eval env (Not x)   = ~(eval env x) ∧
  eval env (And x y) = (eval env x ∧ eval env y) ∧
  eval env (Or x y) = (eval env x ∨ eval env y)
End

Definition bvar_lt_def:
  bvar_lt (n1,g1) (n2,g2:num) =
    if n1 = n2 then g1 < g2 else n1 = A
End

Definition add_to_sorted_def:
  add_to_sorted [] v = [v] ∧
  add_to_sorted (x::xs) v =
    if bvar_lt x v then x :: add_to_sorted xs v else
    if x = v then x :: xs else v :: x :: xs
End

Definition get_bvars_def:
  get_bvars False acc = acc ∧
  get_bvars True acc = acc ∧
  get_bvars (Not x) acc = get_bvars x acc ∧
  get_bvars (Or x y) acc = get_bvars x (get_bvars y acc) ∧
  get_bvars (And x y) acc = get_bvars x (get_bvars y acc) ∧
  get_bvars (Var n g) acc = add_to_sorted acc (n,g)
End

Definition build_Not_def:
  build_Not x =
    case x of
    | True => False
    | False => True
    | Not y => y
    | _ => Not x
End

Definition build_If_def:
  build_If x y z =
    if y = z then y else
    if y = True ∧ z = False then x else
    if y = False ∧ z = True then build_Not x else
    if z = False then And x y else
    if y = True then Or x z else
    if z = True then Or y (build_Not x) else
    if y = False then And z (build_Not x) else
      Or (And x y) (And (build_Not x) z)
End

Definition build_Or_def:
  build_Or x y =
    if x = True then True else
    if y = True then True else
    if x = False then y else
    if y = False then x else
      Or x y
End

Definition subst_def[simp]:
  subst env True      = True ∧
  subst env False     = False ∧
  subst env (Var v n) = env (v,n) ∧
  subst env (Not x)   = build_Not (subst env x) ∧
  subst env (And x y) = build_If (subst env x) (subst env y) False ∧
  subst env (Or x y) = build_Or (subst env x) (subst env y)
End

Definition get_bvars8_def:
  get_bvars8 (y1,y2,y3,y4,y5,y6,y7,y8) =
    (get_bvars y1 $ get_bvars y2 $ get_bvars y3 $ get_bvars y4 $
     get_bvars y5 $ get_bvars y6 $ get_bvars y7 $ get_bvars y8 [])
End

Definition eval_bexp_def[simp]:
  eval_bexp env True      = T ∧
  eval_bexp env False     = F ∧
  eval_bexp env (Not x)   = ~(eval_bexp env x) ∧
  eval_bexp env (And x y) = (eval_bexp env x ∧ eval_bexp env y) ∧
  eval_bexp env (Or x y)  = (eval_bexp env x ∨ eval_bexp env y) ∧
  eval_bexp env (Var v n) = case ALOOKUP env (v,n) of SOME b => b | NONE => F
End

Definition eval_bexp8_def:
  eval_bexp8 env (y1,y2,y3,y4,y5,y6,y7,y8) =
    b2n (eval_bexp env y1) +
    b2n (eval_bexp env y2) +
    b2n (eval_bexp env y3) +
    b2n (eval_bexp env y4) +
    b2n (eval_bexp env y5) +
    b2n (eval_bexp env y6) +
    b2n (eval_bexp env y7) +
    b2n (eval_bexp env y8)
End

Definition count_falses_def:
  count_falses x (y1,y2,y3,y4,y5,y6,y7,y8) =
    b2n (x  = False) +
    b2n (y1 = False) +
    b2n (y2 = False) +
    b2n (y3 = False) +
    b2n (y4 = False) +
    b2n (y5 = False) +
    b2n (y6 = False) +
    b2n (y7 = False) +
    b2n (y8 = False)
End

Definition to_bexp_def[simp]:
  to_bexp T = True ∧
  to_bexp F = False
End

Definition gol_eval_def:
  gol_eval vars env x ys =
    case vars of
    | ((n,g)::vs) =>
        build_If (Var n g)
          (gol_eval vs (((n,g),T)::env) x ys)
          (gol_eval vs (((n,g),F)::env) x ys)
    | [] =>
        let k = eval_bexp8 env ys in
        let mid = eval_bexp env x in
          to_bexp (if mid then (k = 2 ∨ k = 3) else (k = 3))
End

Definition gol_cell_def:
  gol_cell x ys =
    if count_falses x ys >= 7 then False else
      let vars = get_bvars x (get_bvars8 ys) in
        gol_eval vars [] x ys
End

Definition inc_def:
  inc (Var n g) = Var n (g+1) ∧
  inc (And x y) = And (inc x) (inc y) ∧
  inc (Or x y)  = Or (inc x) (inc y) ∧
  inc (Not x)   = Not (inc x) ∧
  inc True      = True ∧
  inc False     = False
End

Definition make_area_def:
  make_area w h = FLAT (GENLIST (λy. GENLIST (λx. (2 * &x:int, 2 * &y:int)) w) h)
End

Definition add_margin_def:
  add_margin fill n xss =
    let ys = REPLICATE n fill in
    let yss = MAP (λxs. ys ++ xs ++ ys) xss in
    let l = (case yss of (row::_) => LENGTH row | _ => n+n) in
    let ts = REPLICATE n (REPLICATE l fill) in
      ts ++ yss ++ ts
End

Definition make_base_area_def:
  make_base_area w h =
    let trues = REPLICATE (h * 150) (REPLICATE (w * 150) T) in
      add_margin F 10 trues : bool list list
End

Definition shrink_row_def:
  shrink_row (x1::x2::x3::xs)
             (y1::y2::y3::ys)
             (z1::z2::z3::zs) =
    ((x1 ∧ x2 ∧ x3 ∧ y1 ∧ y2 ∧ y3 ∧ z1 ∧ z2 ∧ z3) :: shrink_row (x2::x3::xs)
                                                                (y2::y3::ys)
                                                                (z2::z3::zs)) ∧
  shrink_row _ _ _ = []
End

Definition shrink_all_def:
  shrink_all (r1::r2::r3::rest) =
    shrink_row r1 r2 r3 :: shrink_all (r2::r3::rest) ∧
  shrink_all _ = []
End

Definition shrink_def:
  shrink xs = add_margin F 1 (shrink_all xs)
End

Definition or_box_row_def:
  or_box_row x w [] = [] ∧
  or_box_row x w (r::rs) =
    if x = 0:num then if w = 0:num then r :: rs else T :: or_box_row x (w-1) rs
    else r :: or_box_row (x-1) w rs
End

Definition or_box_def:
  or_box x y w h [] = [] ∧
  or_box x y w h (r::rs) =
    if y = 0:num then
      if h = 0:num then r :: rs else
        or_box_row x w r :: or_box x y w (h-1) rs
    else
      r :: or_box x (y-1) w h rs
End

Definition or_io_areas_def:
  or_io_areas [] t = t ∧
  or_io_areas (((x,y),r)::rest) t =
    or_box (Num (85 + 75 * x - 6)) (Num (85 + 75 * y - 6)) 12 12
      (or_io_areas rest t)
End

Definition or_def:
  or xss yss =
    MAP2 (λxs ys. MAP2 (λx y. x ∨ y) xs ys) xss yss
    : bool list list
End

Definition diff_def:
  diff (xss : bool list list) (yss : bool list list) =
    MAP2 (λxs ys. MAP2 (λx y. if y then F else x) xs ys) xss yss
    : bool list list
End

Definition masks_def:
  masks w h ins outs =
    let base_area_bools = make_base_area w h in
    let bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F) in
    let sets1 = or_io_areas (FILTER is_ns ins ++ FILTER is_ew outs) bools in
    let sets2 = or_io_areas (FILTER is_ew ins ++ FILTER is_ns outs) bools in
      (or sets2 (diff base_area_bools sets1),
       or sets1 (diff base_area_bools sets2))
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

Datatype:
  blist = Nil | Falses num blist | Cell bexp blist
End

Datatype:
  mask = End | Allow num mask | Forbid num mask
End

Definition mk_Falses_def:
  mk_Falses n (Falses m b) = Falses (m+n) b ∧
  mk_Falses n b = if n = 0 then b else Falses n b
End

Definition mk_Cell_def:
  mk_Cell e b = if e = False then mk_Falses 1 b else Cell e b
End

Definition mask_length_def:
  mask_length End = 0 ∧
  mask_length (Allow k m) = k + mask_length m ∧
  mask_length (Forbid k m) = k + mask_length m
End

Definition mk_Allow_def:
  mk_Allow m (Allow n rest) = Allow (n+m) rest ∧
  mk_Allow m other = Allow m other
End

Definition mk_Forbid_def:
  mk_Forbid m (Forbid n rest) = Forbid (n+m) rest ∧
  mk_Forbid m other = Forbid m other
End

Definition to_mask_def:
  to_mask [] = End ∧
  to_mask (x::xs) = if x then mk_Allow 1 (to_mask xs) else mk_Forbid 1 (to_mask xs)
End

Definition from_mask_def:
  from_mask End = [] ∧
  from_mask (Allow n m) = REPLICATE n T ++ from_mask m ∧
  from_mask (Forbid n m) = REPLICATE n F ++ from_mask m
End

Definition blist_length_def:
  blist_length Nil = 0 ∧
  blist_length (Falses n b) = n + blist_length b ∧
  blist_length (Cell e b) = 1 + blist_length b
End

Definition blist_simple_checks_def:
  blist_simple_checks w h ins outs rows ⇔
    LENGTH rows = 150 * h + 20 ∧
    EVERY (λrow. blist_length row = 150 * w + 20) rows ∧
    h ≠ 0 ∧ w ≠ 0 ∧
    ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
    let area = make_area w h in
      ALL_DISTINCT area ∧
      EVERY (λ(p,d,r). MEM (add_pt p (dir_to_xy d)) area ∧
                      ¬MEM (sub_pt p (dir_to_xy d)) area) ins ∧
      EVERY (λ(p,d,r). MEM (sub_pt p (dir_to_xy d)) area ∧
                      ¬MEM (add_pt p (dir_to_xy d)) area) outs
End

Definition mask_hd_def:
  mask_hd End = NONE ∧
  mask_hd (Forbid n rest) = (if n = 0 then mask_hd rest else SOME F) ∧
  mask_hd (Allow n rest) = (if n = 0 then mask_hd rest else SOME T)
End

Definition mask_drop_def:
  mask_drop n End = End ∧
  mask_drop n (Forbid k rest) =
    (if n = 0 then Forbid k rest else
     if n ≤ k then Forbid (k - n) rest else
       mask_drop (n - k) rest) ∧
  mask_drop n (Allow k rest) =
    (if n = 0 then Allow k rest else
     if n ≤ k then Allow (k - n) rest else
       mask_drop (n - k) rest)
End

Definition blist_inter_row_def:
  blist_inter_row r b =
    case r of
    | Nil => Nil
    | Falses k rest =>
       mk_Falses k (blist_inter_row rest (mask_drop k b))
    | Cell e l =>
       (case mask_hd b of
        | NONE => mk_Cell e l
        | SOME T => mk_Cell e (blist_inter_row l (mask_drop 1 b))
        | SOME F => mk_Falses 1 (blist_inter_row l (mask_drop 1 b)))
End

Definition blist_inter_rows_def:
  blist_inter_rows [] del = [] ∧
  blist_inter_rows r [] = r ∧
  blist_inter_rows (r::rows) (b::bools) =
    blist_inter_row r b :: blist_inter_rows rows bools
End

Definition blist_diff_row_def:
  blist_diff_row r b =
    case r of
    | Nil => Nil
    | Falses k rest =>
       mk_Falses k (blist_diff_row rest (mask_drop k b))
    | Cell e l =>
       (case mask_hd b of
        | NONE => mk_Cell e l
        | SOME F => mk_Cell e (blist_diff_row l (mask_drop 1 b))
        | SOME T => mk_Falses 1 (blist_diff_row l (mask_drop 1 b)))
End

Definition blist_diff_rows_def:
  blist_diff_rows [] del = [] ∧
  blist_diff_rows r [] = r ∧
  blist_diff_rows (r::rows) (b::bools) =
    blist_diff_row r b :: blist_diff_rows rows bools
End

Definition blist_append_def:
  blist_append Nil ys = ys ∧
  blist_append (Cell e xs) ys = Cell e (blist_append xs ys) ∧
  blist_append (Falses k xs) ys = mk_Falses k (blist_append xs ys)
End

Definition blist_rev_def:
  blist_rev Nil acc = acc ∧
  blist_rev (Cell e b) acc = blist_rev b (mk_Cell e acc) ∧
  blist_rev (Falses n b) acc = blist_rev b (mk_Falses n acc)
End

Definition blist_or_row_acc_def:
  blist_or_row_acc (x:num) [] (row:blist) acc =
    blist_append (blist_rev acc Nil) row ∧
  blist_or_row_acc (x:num) (p::ps) (row:blist) acc =
    case row of
    | Nil => blist_rev acc Nil
    | Cell e b =>
        if x = 0 then
          blist_or_row_acc 0 ps b (mk_Cell (build_Or p e) acc)
        else
          blist_or_row_acc (x-1) (p::ps) b (mk_Cell e acc)
    | Falses n b =>
        if n ≤ x then
          blist_or_row_acc (x - n) (p::ps) b (mk_Falses n acc)
        else
          blist_or_row_acc 0 ps (mk_Falses (n - x - 1) b)
            (mk_Cell p (mk_Falses x acc))
End

Definition blist_or_row_def:
  blist_or_row x ps row = blist_or_row_acc x ps row Nil
End

Definition blist_or_at_def:
  blist_or_at x y pat [] = [] ∧
  blist_or_at x y [] (row::rows) = row::rows ∧
  blist_or_at x y (p::pat) (row::rows) =
    if y = 0:num then
      blist_or_row x p row :: blist_or_at x y pat rows
    else
      row :: blist_or_at x (y-1) (p::pat) rows
End

Definition blist_or_lwss_def:
  blist_or_lwss rows [] = SOME (rows : blist list) ∧
  blist_or_lwss rows (((x,y),d,v)::rest) =
    case blist_or_lwss rows rest of
    | NONE => NONE
    | SOME rows1 =>
        SOME (blist_or_at (Num (x * 75 − 5 + 85)) (Num (y * 75 − 5 + 85))
               (MAP (MAP (λb. if b then v else False)) (io_gate d)) rows1)
End

Definition blist_inc_def:
  blist_inc Nil = Nil ∧
  blist_inc (Falses n b) = Falses n (blist_inc b) ∧
  blist_inc (Cell e b) = Cell (inc e) (blist_inc b)
End

Definition blist_inc_vars_def:
  blist_inc_vars rows = MAP blist_inc rows
End

Definition mask_or_io_areas_def:
  mask_or_io_areas outs bools =
    (* this is a bit lazy, but this is not a performance critical part *)
    MAP to_mask (or_io_areas outs (MAP from_mask bools))
End

Definition fast_forward_def:
  fast_forward mask x0 (Falses x1 xs) y0 (Falses y1 ys) z0 (Falses z1 zs) acc =
    (if x0 = False ∨ y0 = False ∨ z0 = False then
     if 1 < x1 ∧ 1 < y1 ∧ 1 < z1 then
       let m = MIN x1 (MIN y1 z1) - 1 in
         SOME (mask_drop m mask,
               mk_Falses (x1 - m) xs,
               mk_Falses (y1 - m) ys,
               mk_Falses (z1 - m) zs,
               mk_Falses m acc)
     else NONE else NONE) ∧
  fast_forward mask x0 _ y0 _ z0 _ acc = NONE
End

Definition blist_hd_def:
  blist_hd Nil = NONE ∧
  blist_hd (Falses n b) = (if n = 0 then blist_hd b else SOME False) ∧
  blist_hd (Cell e b) = SOME e
End

Definition blist_hd3_def:
  blist_hd3 x y z =
    case (blist_hd x, blist_hd y, blist_hd z) of
    | (SOME h1, SOME h2, SOME h3) => SOME (h1,h2,h3)
    | _ => NONE
End

Definition blist_hd_or_false_def:
  blist_hd_or_false Nil = False ∧
  blist_hd_or_false (Cell e b) = e ∧
  blist_hd_or_false (Falses n b) = if n = 0 then blist_hd_or_false b else False
End

Definition blist_tl_def:
  blist_tl Nil = Nil ∧
  blist_tl (Cell e b) = b ∧
  blist_tl (Falses n b) =
    if n = 0 then blist_tl b else
    if n = 1 then b else Falses (n-1) b
End

Theorem blist_length_mk_Falses:
  blist_length (mk_Falses n b) = blist_length (Falses n b)
Proof
  Cases_on ‘b’ \\ rw [blist_length_def,mk_Falses_def]
QED

Theorem blist_length_tl:
  ∀ys. blist_length (blist_tl ys) = blist_length ys - 1
Proof
  Induct \\ gvs [blist_tl_def,blist_length_def]
  \\ rw [] \\ gvs [blist_tl_def,blist_length_def]
QED

Theorem blist_hd_some:
  ∀ys e. blist_hd ys = SOME e ⇒ blist_length ys ≠ 0
Proof
  Induct \\ gvs [blist_hd_def,blist_length_def]
QED

Definition blist_check_mask_def:
  blist_check_mask Nil m = T ∧
  blist_check_mask (Falses k rest) m =
    blist_check_mask rest (mask_drop k m) ∧
  blist_check_mask (Cell e rest) m =
    case mask_hd m of
    | SOME F => if e = False then blist_check_mask rest (mask_drop 1 m) else F
    | _ => blist_check_mask rest (mask_drop 1 m)
End

Definition blist_gol_row_acc_def:
  blist_gol_row_acc mask x0 xs y0 ys z0 zs acc =
    case fast_forward mask x0 xs y0 ys z0 zs acc of
    | SOME (mask1,xs1,ys1,zs1,acc1) =>
        blist_gol_row_acc mask1 False xs1 False ys1 False zs1 acc1
    | NONE =>
        case blist_hd3 xs ys zs of
        | NONE => if blist_check_mask ys mask then SOME (blist_rev acc Nil) else NONE
        | SOME (x1,y1,z1) =>
            if y1 ≠ False ∧ mask_hd mask ≠ SOME T then NONE else
              let xs = blist_tl xs in
              let ys = blist_tl ys in
              let zs = blist_tl zs in
              let x2 = blist_hd_or_false xs in
              let y2 = blist_hd_or_false ys in
              let z2 = blist_hd_or_false zs in
              let c = gol_cell y1 (x0,x1,x2,y0,y2,z0,z1,z2) in
                blist_gol_row_acc (mask_drop 1 mask) x1 xs y1 ys z1 zs (mk_Cell c acc)
Termination
  WF_REL_TAC ‘measure $ λ(mask,x0,xs,y0,ys,z0,zs,acc). blist_length ys’
  \\ rw [] \\ gvs [blist_hd3_def,AllCaseEqs(),oneline fast_forward_def]
  \\ gvs [blist_length_def,blist_length_mk_Falses,blist_length_tl]
  \\ imp_res_tac blist_hd_some \\ gvs [blist_hd_def]
  \\ gvs [blist_length_def,blist_length_mk_Falses,blist_length_tl]
  \\ rw [MIN_DEF] \\ gvs []
End

Definition blist_gol_row_def:
  blist_gol_row mask x0 xs y0 ys z0 zs =
    if blist_length ys = mask_length mask then
      blist_gol_row_acc mask x0 xs y0 ys z0 zs Nil
    else NONE
End

Definition blist_gol_rows_def:
  blist_gol_rows (mask::masks) prev (row::rest) =
    (case blist_gol_row mask False prev False row False
            (case rest of [] => Falses (blist_length row) Nil | (r::_) => r) of
     | NONE => NONE
     | SOME row1 =>
         case blist_gol_rows masks row rest of
         | NONE => NONE
         | SOME rows1 => SOME (row1 :: rows1)) ∧
  blist_gol_rows [] prev [] = SOME [] ∧
  blist_gol_rows _  prev _  = NONE
End

Definition blist_gol_checked_step_def:
  blist_gol_checked_step mask [] = (if NULL mask then SOME [] else NONE) ∧
  blist_gol_checked_step mask (r::rs) =
    blist_gol_rows mask (Falses (blist_length r) Nil) (r::rs)
End

Definition blist_gol_checked_steps_def:
  blist_gol_checked_steps (n:num) rows (mask : mask list) =
    if n = 0 then SOME rows else
      case blist_gol_checked_step mask rows of
      | NONE => NONE
      | SOME rows1 => blist_gol_checked_steps (n-1) rows1 mask
End

Definition admissible_ins_def:
  admissible_ins [(p1:int#int,d1:dir,Var A da)] = SOME (da, NONE) ∧
  admissible_ins [(p1,d1,Var A da); (p2,d2,Var B db)] = SOME (da, SOME db) ∧
  admissible_ins _ = NONE
End

Definition admissible_bexpr_def:
  (admissible_bexpr env (Var A d) ⇔ d < FST env) ∧
  (admissible_bexpr env (Var B d) ⇔ case SND env of NONE => F | SOME db => d < db) ∧
  (admissible_bexpr env True ⇔ T) ∧
  (admissible_bexpr env False ⇔ T) ∧
  (admissible_bexpr env (Not x) ⇔ admissible_bexpr env x) ∧
  (admissible_bexpr env (And x y) ⇔ admissible_bexpr env x ∧ admissible_bexpr env y) ∧
  (admissible_bexpr env (Or x y) ⇔ admissible_bexpr env x ∧ admissible_bexpr env y)
End

Definition admissible_row_def:
  (admissible_row env Nil ⇔ T) ∧
  (admissible_row env (Falses _ rest) ⇔ admissible_row env rest) ∧
  (admissible_row env (Cell e rest) ⇔ admissible_bexpr env e ∧ admissible_row env rest)
End

Definition blist_simulation_ok_def:
  blist_simulation_ok w h ins outs (rows : blist list) ⇔
    blist_simple_checks w h ins outs rows ∧
    (case admissible_ins ins of
    | NONE => F
    | SOME (da, db) =>
      EVERY (λ(_,_,v). admissible_bexpr (da, db) v) outs ∧
      EVERY (admissible_row (da, db)) rows) ∧
    let (m1,m2) = masks w h ins outs in
    let mask1 = MAP to_mask (shrink m1) in
    let mask2 = MAP to_mask (shrink m2) in
    let bools = REPLICATE (150 * h + 20) (Forbid (150 * w + 20) End) in
    let del1 = mask_or_io_areas (FILTER is_ns outs) bools in
    let del2 = mask_or_io_areas (FILTER is_ew outs) bools in
    let ins1 = FILTER is_ns ins in
    let ins2 = FILTER is_ew ins in
    let outs1 = FILTER is_ns outs in
    let outs2 = FILTER is_ew outs in
    let empty = REPLICATE (150 * h + 20) (Falses (150 * w + 20) Nil) in
      case blist_gol_checked_steps 30 rows mask1 of
      | NONE => F
      | SOME rows1 =>
        if blist_or_lwss empty outs1 ≠
           SOME (blist_inter_rows rows1 del1)
        then F else
          case blist_or_lwss (blist_diff_rows rows1 del1) ins1 of
          | NONE => F
          | SOME rowsA =>
            case blist_gol_checked_steps 30 rowsA mask2 of
            | NONE => F
            | SOME rows2 =>
                if blist_or_lwss empty outs2 ≠
                   SOME (blist_inter_rows rows2 del2)
                then F else
                  case blist_or_lwss (blist_diff_rows rows2 del2) ins2 of
                  | NONE => F
                  | SOME rowsB => blist_inc_vars rows = rowsB
End

Datatype:
  env_kind = Zeros | Pulse num num | PulseThis num num
End

Definition eval_env_kind_def:
  (eval_env_kind Zeros n = False) ∧
  (eval_env_kind (Pulse a b) n = if a ≤ n ∧ n < b then True else False) ∧
  (eval_env_kind (PulseThis a b) n = if a ≤ n ∧ n < b then Var A 0 else False)
End

Definition instantiate_var_def:
  instantiate_var (ea, _) (A, n) = eval_env_kind ea n ∧
  instantiate_var (_, eb) (B, n) = eval_env_kind eb n
End

Definition instantiate_row_def:
  instantiate_row env Nil = Nil ∧
  instantiate_row env (Falses n b) =
    mk_Falses n (instantiate_row env b) ∧
  instantiate_row env (Cell e b) =
    mk_Cell (subst (instantiate_var env) e) (instantiate_row env b)
End

Definition instantiate_def:
  instantiate env = MAP (instantiate_row env)
End

val _ = export_theory();
