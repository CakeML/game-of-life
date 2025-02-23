open HolKernel bossLib gol_simLib gol_simTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory gol_sim_cvTheory;

val _ = new_theory "gol_gates";

(*
Definition falses_def:
  falses 0 l = l ∧
  falses (SUC n) l = falses n (False :: l)
End
val _ = cv_auto_trans falses_def;
*)

local
  val A_tm  = prim_mk_const {Name = "A",  Thy = "gol_sim"}
  val B_tm  = prim_mk_const {Name = "B",  Thy = "gol_sim"}
  val N_tm  = prim_mk_const {Name = "N",  Thy = "gol_circuit"}
  val E_tm  = prim_mk_const {Name = "E",  Thy = "gol_circuit"}
  val S_tm  = prim_mk_const {Name = "S",  Thy = "gol_circuit"}
  val W_tm  = prim_mk_const {Name = "W",  Thy = "gol_circuit"}
  val true_tm  = prim_mk_const {Name = "True",  Thy = "gol_sim"}
  val false_tm = prim_mk_const {Name = "False", Thy = "gol_sim"}
  val var_tm   = prim_mk_const {Name = "Var", Thy = "gol_sim"}
  val not_tm   = prim_mk_const {Name = "Not", Thy = "gol_sim"}
  val and_tm   = prim_mk_const {Name = "And", Thy = "gol_sim"}
  val or_tm    = prim_mk_const {Name = "Or",  Thy = "gol_sim"}
(*
  val falses_tm = prim_mk_const {Name = "falses", Thy = "gol_gates"}
*)
  val bexp_ty = ``:bexp``

  fun ERR x = mk_HOL_ERR "gol_gatesScript" x ""
(*
  val dest_falses = dest_binop falses_tm (ERR "dest_falses")
*)
  val dest_and = dest_binop and_tm (ERR "dest_and")
  val dest_or = dest_binop or_tm (ERR "dest_or")
  val dest_var = dest_binop var_tm (ERR "dest_var")
  val dest_not = dest_monop not_tm (ERR "dest_not")
in
  fun tr_var 0 = A_tm
    | tr_var 1 = B_tm
    | tr_var _ = raise Fail "unknown variable"

  fun tr_bexp True         = true_tm
    | tr_bexp False        = false_tm
    | tr_bexp (Var (v, n)) = mk_binop var_tm (tr_var v, numSyntax.term_of_int n)
    | tr_bexp (Not x)      = mk_monop not_tm (tr_bexp x)
    | tr_bexp (And (x, y)) = mk_binop and_tm (tr_bexp x, tr_bexp y)
    | tr_bexp (Or (x, y))  = mk_binop or_tm (tr_bexp x, tr_bexp y)

  fun tr_vector ty f =
    Vector.foldr (fn (a, r) => listSyntax.mk_cons (f a, r)) (listSyntax.mk_nil ty)

  val Nil_tm = prim_mk_const {Name = "Nil", Thy = "gol_sim"}
  val Cell_tm = prim_mk_const {Name = "Cell", Thy = "gol_sim"}
  val Falses_tm = prim_mk_const {Name = "Falses", Thy = "gol_sim"}
  fun mk_Cell (e,l) = list_mk_comb (Cell_tm,[e,l])
  fun mk_Falses (k,l) = list_mk_comb (Falses_tm,[numSyntax.term_of_int k, l])

  fun tr_falses (0, r) = r
    | tr_falses (n, r) = mk_Falses (n, r)

  val tr_bexps = let
    fun go (False, (n, r)) = (n + 1, r)
      | go (a, r) = (0, mk_Cell(tr_bexp a, tr_falses r))
    in tr_falses o Vector.foldr go (0, Nil_tm) end

  val tr_bexpss = tr_vector ``:blist`` tr_bexps

  fun tr_dir N = N_tm
    | tr_dir E = E_tm
    | tr_dir S = S_tm
    | tr_dir W = W_tm

  fun tr_io_port (((a, b), d, v):io_port) =
    pairSyntax.mk_pair (
      pairSyntax.mk_pair (
        intSyntax.term_of_int (Arbint.fromInt a),
        intSyntax.term_of_int (Arbint.fromInt b)),
      pairSyntax.mk_pair (tr_dir d, tr_bexp v))

  val tr_io_ports = let
    val ty = ``:(int # int) # dir # bexp``
    in fn l => listSyntax.mk_list (map tr_io_port l, ty) end

  fun dest_var' t =
    if term_eq A_tm t then 0
    else if term_eq B_tm t then 1
    else raise ERR "dest_var'"

  fun dest_bexp (t:term): bexp =
    if term_eq false_tm t then False
    else if term_eq true_tm t then True
    else if can dest_var t then
      Var ((dest_var' ## numSyntax.int_of_term) (dest_var t))
    else if can dest_and t then And ((dest_bexp ## dest_bexp) (dest_and t))
    else if can dest_or t then Or ((dest_bexp ## dest_bexp) (dest_or t))
    else if can dest_not t then Not (dest_bexp (dest_not t))
    else raise ERR "dest_bexp"

(*
  fun dest_bexps w t = let
    val st = ref (0, t)
    fun pull (0, t) =
        if can dest_falses t then let
          val (n, t) = dest_falses t
          in pull (numSyntax.int_of_term n, t) end
        else if listSyntax.is_cons t then let
          val (a, t) = listSyntax.dest_cons t
          in st := (0, t); dest_bexp a end
        else raise ERR "dest_bexps"
      | pull (n, t) =  (st := (n-1, t); False)
    in Vector.tabulate (w, fn _ => pull (!st)) end

  fun dest_bexpss h w t = let
    val st = ref t
    fun pull t =
      if listSyntax.is_cons t then let
        val (a, t) = listSyntax.dest_cons t
        in st := t; dest_bexps w a end
      else raise ERR "dest_bexpss"
    in Vector.tabulate (h, fn _ => pull (!st)) end
*)

end

fun translate_gate dirs gate = let
  val start = load gate
  fun tr i = let
    val stem = List.nth (#stems gate, i)
    val _ = print ("translate: " ^ stem ^ "\n")
    val {inputs, outputs, grid} = run_to_fixpoint (prepare (rotate i start))
    val tm = tr_bexpss grid
    val defn = boolLib.new_definition (stem^"_def",
      mk_eq (mk_var (stem, ``:blist list``), tm))
    val _ = cv_trans_deep_embedding EVAL defn
    val rows = lhs (concl defn)
    val w = numSyntax.term_of_int (#width gate)
    val h = numSyntax.term_of_int (#height gate)
    val ins = tr_io_ports inputs
    val outs = tr_io_ports outputs
    val thm = store_thm (stem^"_thm",
      ``blist_simulation_ok ^w ^h ^ins ^outs ^rows``,
      CONV_TAC cv_eval)
    in (defn, thm) end
  in map tr dirs end;

val _ = translate_gate [2] terminator_e;
val _ = translate_gate [0,1,2,3] wire_e_e;
val _ = translate_gate [0,1,2,3] cross_es_es;
val _ = translate_gate [0] and_en_e;
val _ = translate_gate [0] and_es_e;
val _ = translate_gate [0] and_ew_n;
val _ = translate_gate [0,1,2,3] or_en_e;
val _ = translate_gate [0,3] not_e_e;
(* val _ = translate_gate [0,1,2,3] turn_e_s; *)
val _ = translate_gate [0,1,2,3] turn_e_n;
val _ = translate_gate [0,1,2,3] fast_turn_e_s;
val _ = translate_gate [3] slow_turn_e_s;
val _ = translate_gate [0,1,2] fork_e_es;
val _ = translate_gate [0,1,2,3] fork_e_en;
val _ = translate_gate [1,2,3] half_adder_ee_es;
val _ = translate_gate [0,1,2,3] half_adder_ee_ee;
val _ = translate_gate [0,1,2,3] slow_wire_e_e;
(* val _ = translate_gate [2] slower_wire_e_e; *)

Definition delay_def:
  delay n a i = if i < n then F else a (i - n:num)
End

Definition conj_def:
  conj a b = (λn. a n ∧ b n)
End

Definition disj_def:
  disj a b = (λn. a n ∨ b n)
End

Definition set_env_def:
  set_env a b (A,n) = a n ∧
  set_env a b (B,n) = b n
End

Theorem delay_simp:
  (λn. delay k a (k + n)) = a ∧
  (λn. delay k a (n + k)) = a
Proof
  gvs [FUN_EQ_THM,delay_def]
QED

Theorem simulation_ok_2:
  simulation_ok w h [((x1,x2),d,Var A a_d); ((x1',x2'),d',Var B b_d)] outs init ⇒
  ∀a b.
    circuit
      (make_area w h)
      [((x1,x2),d,a); ((x1',x2'),d',b)]
      (eval_io (set_env (delay a_d a) (delay b_d b)) outs) []
      (from_rows (-85,-85)
        (MAP (MAP (eval (set_env (delay a_d a) (delay b_d b)))) init))
Proof
  rw []
  \\ drule simulation_ok_IMP_circuit
  \\ disch_then $ qspec_then ‘(set_env (delay a_d a) (delay b_d b))’ mp_tac
  \\ gvs [eval_io_def,set_env_def,delay_simp]
QED

fun make_abbrev name tm =
  let
    val v = mk_var(name,type_of tm)
    val th = new_definition(name,mk_eq(v,tm))
  in SYM th end

Theorem and_en_e_circuit =
  MATCH_MP blist_simulation_ok_thm (theorem "and_en_e_thm")
  |> MATCH_MP simulation_ok_2
  |> CONV_RULE ((QUANT_CONV o QUANT_CONV o RAND_CONV o RAND_CONV)
       (REWRITE_CONV [definition "and_en_e_def"] THENC EVAL
        THENC make_abbrev "and_en_e_concrete"))
  |> SRULE [eval_io_def,set_env_def,GSYM conj_def,GSYM disj_def,
            SF ETA_ss, make_area_def];

val _ = (max_print_depth := 10); (* avoids blow up in size of Theory.sig file *)
val _ = export_theory();
