(*
  Definitions that help symbolically simulate GOL instances
*)
open preamble gol_rulesTheory integerTheory;

val _ = new_theory "gol_sim";

(* Main definition *)

Definition gol_def[nocompute]:
  gol x1 x2 x3 y1 y2 y3 z1 z2 z3 ⇔
    let n = SUM (MAP b2n [x1;x2;x3;y1;y3;z1;z2;z3]) in
      if y2 then n = 2 ∨ n = 3 else n = 3
End

(* The automation below derives theorems such as these:
     gol a F F F b F F F F = F ∧
     gol T T T F b F F F F = T ∧
     gol T T F F b F F F F = b ∧
     gol T T T T b c d e f = F
*)

val _ = (max_print_depth := 30);

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

val gol_1var = let
  fun all_comb 0 = [[]]
    | all_comb n = let
        val xs = all_comb (n-1)
        in map (fn x => c::x) xs @ map (fn x => F::x) xs end
  val xs = all_comb 9
  fun one vs = let
    val tm = list_mk_comb(“gol”,vs)
    val tac = TRY (tmCases_on c [])
              THEN fs [gol4,gol3,gol3F,gol2,gol2F,gol1]
              THEN NO_TAC
    fun auto_prove goal = tac ([],goal) |> snd |> (fn f => f [])
    val lemma = auto_prove (mk_eq(tm,F)) handle HOL_ERR _ =>
                auto_prove (mk_eq(tm,c)) handle HOL_ERR _ =>
                auto_prove (mk_eq(tm,T))
    in lemma end
  in LIST_CONJ (map one xs) end;

Theorem gol_1var[compute] = gol_1var;

Theorem gol_simp =
  [gol4,gol3,gol3F,gol2,gol2F,gol1,gol_1var]
  |> LIST_CONJ |> PURE_REWRITE_RULE [GSYM CONJ_ASSOC];

val _ = export_theory();
