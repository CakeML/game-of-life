(*
  Definitions that help symbolically simulate GOL instances

  The plane is represented as a square.
*)
open preamble gol_rulesTheory gol_listTheory gol_transTheory
     integerTheory sortingTheory;

val _ = new_theory "gol_sim";

val gol_def = zDefine ‘
  gol x1 x2 x3 y1 y2 y3 z1 z2 z3 ⇔
    let n = SUM (MAP b2n [x1;x2;x3;y1;y3;z1;z2;z3]) in
      if y2 then n = 2 ∨ n = 3 else n = 3’

Definition next_row_def:
  next_row (x1::x2::x3::xs) (y1::y2::y3::ys) (z1::z2::z3::zs) =
    gol x1 x2 x3 y1 y2 y3 z1 z2 z3 ::
      next_row (x2::x3::xs) (y2::y3::ys) (z2::z3::zs) ∧
  next_row _ _ _ = []
End

Definition next_frame_def:
  next_frame prev (x::y::xs) = next_row prev x y :: next_frame x (y::xs) ∧
  next_frame prev _ = []
End

Definition zero_borders_def:
  zero_borders rows ⇔
    ~NULL rows ∧
    EVERY (λn. n = F) (HD rows) ∧
    EVERY (λn. n = F) (LAST rows) ∧
    EVERY (λr. HD r = F ∧ LAST r = F ∧ LENGTH r = LENGTH (HD rows)) rows
End

Definition add_zero_borders_def:
  add_zero_borders frame =
    (F::F::MAP (K F) (HD frame)) ::
    MAP (λr. F :: r ++ [F]) frame ++ [F::F::MAP (K F) (HD frame)]
End

Definition tick_def:
  tick frame =
    if zero_borders frame then
      let rows = add_zero_borders frame in
        SOME (next_frame (HD rows) (TL rows))
    else NONE
End

Definition tick_n_def:
  tick_n n frame =
    if n = 0 then SOME frame else
      case tick frame of
      | NONE => NONE
      | SOME f => tick_n (n-1:num) f
End



Theorem gol_sim:
  gol a F F F b F F F F = F ∧
  gol T T T F b F F F F = T ∧
  gol T T F F b F F F F = b ∧
  gol T T T T b c d e f = F
Proof
  Cases_on ‘a’ \\ Cases_on ‘b’
  \\ fs [gol_def,b2n_def]
  \\ Cases_on ‘c’
  \\ Cases_on ‘d’
  \\ Cases_on ‘e’
  \\ Cases_on ‘f’
  \\ EVAL_TAC
QED

fun insert 0 x xs = x::xs
  | insert n x [] = x::[]
  | insert n x (y::ys) = y :: insert (n-1) x ys;

fun all_perm [] = [[]]
  | all_perm (x::xs) =
      let val ys = all_perm xs
          val k = length xs + 1
      in flatten (map (fn l => List.tabulate (k, fn i => insert i x l)) ys) end

fun all_distinct [] = []
  | all_distinct (x::xs) = x :: all_distinct (filter (not o aconv x) xs);

val b = “b:bool”

Theorem gol1[compute] = (* at most one T *)
  all_perm [“a:bool”,F,F,F,F,F,F,F]
  |> map (fn l => mk_eq(list_mk_comb(“gol”,insert 4 b l),F))
  |> all_distinct
  |> map (fn tm => prove(tm,  Cases_on ‘a’ \\ Cases_on ‘b’ \\ fs [gol_def,b2n_def]))
  |> LIST_CONJ;

Theorem gol2F[compute] = (* at most two T, but F in middle *)
  all_perm [“a:bool”,T,F,F,F,F,F,F]
  |> map (fn l => mk_eq(list_mk_comb(“gol”,insert 4 F l),F))
  |> all_distinct
  |> map (fn tm => prove(tm,  Cases_on ‘a’ \\ fs [gol_def,b2n_def]))
  |> LIST_CONJ;

Theorem gol2[compute] = (* exactly two T *)
  all_perm [T,T,F,F,F,F,F,F]
  |> map (fn l => mk_eq(list_mk_comb(“gol”,insert 4 b l),b))
  |> all_distinct
  |> map (fn tm => prove(tm, Cases_on ‘b’ \\ fs [gol_def,b2n_def]))
  |> LIST_CONJ;

Theorem gol3F[compute] = (* exactly two T *)
  all_perm [T,T,b,F,F,F,F,F]
  |> map (fn l => mk_eq(list_mk_comb(“gol”,insert 4 F l),b))
  |> all_distinct
  |> map (fn tm => prove(tm, Cases_on ‘b’ \\ fs [gol_def,b2n_def]))
  |> LIST_CONJ;

Theorem gol3[compute] = (* exactly three T *)
  all_perm [T,T,T,F,F,F,F,F]
  |> map (fn l => mk_eq(list_mk_comb(“gol”,insert 4 b l),T))
  |> all_distinct
  |> map (fn tm => prove(tm, Cases_on ‘b’ \\ fs [gol_def,b2n_def]))
  |> LIST_CONJ;

val c = “c:bool”

fun change_vars vars tm =
  if aconv tm c then (hd vars, tl vars) else
  if is_var tm then (tm,vars) else
  if is_comb tm then
    let val (x,vars) = change_vars vars (rator tm)
        val (y,vars) = change_vars vars (rand tm)
    in (mk_comb (x, y), vars) end
  else (tm,vars);

Theorem gol4[compute] = (* four or more T *)
  all_perm [T,T,T,T,c,c,c,c]
  |> map (fn l => mk_eq(list_mk_comb(“gol”,insert 4 b l),F))
  |> all_distinct
  |> map (change_vars [“c:bool”,“d:bool”,“e:bool”,“f:bool”]) |> map fst
  |> map (fn tm => prove(tm,
       Cases_on ‘b’ \\ Cases_on ‘c’ \\ Cases_on ‘d’
       \\ Cases_on ‘e’ \\ Cases_on ‘f’ \\ fs [gol_def,b2n_def]))
  |> LIST_CONJ;

(*

        EVAL “tick_n 1 [[F;F;F;F;F;F;F];
                        [F;F;F;T;F;F;F];
                        [F;F;F;b;F;F;F];
                        [F;F;F;T;F;F;F];
                        [F;F;F;F;F;F;F]]”

*)

val _ = export_theory();
