open HolKernel bossLib gol_simLib gol_rulesTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory gol_sim_cvTheory;

val _ = new_theory "gol_gates";

Definition falses_def:
  falses 0 l = l ∧
  falses (SUC n) l = falses n (False :: l)
End
val _ = cv_auto_trans falses_def;

local
  val A_tm  = prim_mk_const {Name = "A",  Thy = "gol_rules"}
  val B_tm  = prim_mk_const {Name = "B",  Thy = "gol_rules"}
  val N_tm  = prim_mk_const {Name = "N",  Thy = "gol_rules"}
  val E_tm  = prim_mk_const {Name = "E",  Thy = "gol_rules"}
  val S_tm  = prim_mk_const {Name = "S",  Thy = "gol_rules"}
  val W_tm  = prim_mk_const {Name = "W",  Thy = "gol_rules"}
  val true_tm  = prim_mk_const {Name = "True",  Thy = "gol_rules"}
  val false_tm = prim_mk_const {Name = "False", Thy = "gol_rules"}
  val var_tm   = prim_mk_const {Name = "Var", Thy = "gol_rules"}
  val not_tm   = prim_mk_const {Name = "Not", Thy = "gol_rules"}
  val and_tm   = prim_mk_const {Name = "And", Thy = "gol_rules"}
  val or_tm    = prim_mk_const {Name = "Or",  Thy = "gol_rules"}
  val falses_tm = prim_mk_const {Name = "falses", Thy = "gol_gates"}
  val bexp_ty = ``:bexp``

  fun ERR x = mk_HOL_ERR "gol_gatesScript" x ""
  val dest_falses = dest_binop falses_tm (ERR "dest_falses")
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

  fun tr_falses (0, r) = r
    | tr_falses (1, r) = listSyntax.mk_cons (false_tm, r)
    | tr_falses (n, r) = mk_binop falses_tm (numSyntax.term_of_int n, r)
      (* tr_falses (n, r) = if n = 0 then r else tr_falses (n-1, listSyntax.mk_cons (false_tm, r)) *)

  val tr_bexps = let
    fun go (False, (n, r)) = (n + 1, r)
      | go (a, r) = (0, listSyntax.mk_cons (tr_bexp a, tr_falses r))
    in tr_falses o Vector.foldr go (0, listSyntax.mk_nil bexp_ty) end

  val tr_bexpss = tr_vector ``:bexp list`` tr_bexps

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
end

fun translate_gate stems gate = let
  val start = load gate
  fun tr (stem, i) = let
    val _ = print ("translate: " ^ stem ^ "\n")
    val {inputs, outputs, grid} = run_to_fixpoint (prepare (funpow i rotate start))
    val tm = tr_bexpss grid
    val defn = boolLib.new_definition (stem^"_def",
      mk_eq (mk_var (stem, ``:bexp list list``), tm))
    val _ = cv_trans_deep_embedding EVAL defn
    val rows = lhs (concl defn)
    val w = numSyntax.term_of_int (#width gate)
    val h = numSyntax.term_of_int (#height gate)
    val ins = tr_io_ports inputs
    val outs = tr_io_ports outputs
    val thm = store_thm (stem^"_thm",
      ``simulation_ok ^w ^h ^ins ^outs ^rows``,
      CONV_TAC cv_eval)
    in (defn, thm) end
  in map tr stems end;

val _ = translate_gate [("wire_e_e", 0)] wire_e_e;
val _ = translate_gate [("cross_es_es", 0)] cross_es_es;
val _ = translate_gate [("cross_en_en", 0)] cross_en_en;
val _ = translate_gate [("and_en_e", 0)] and_en_e;
val _ = translate_gate [("and_es_e", 0)] and_es_e;
val _ = translate_gate [("and_ew_n", 0)] and_ew_n;
val _ = translate_gate [("or_en_e", 0)] or_en_e;
val _ = translate_gate [("not_e_e", 0)] not_e_e;
val _ = translate_gate [("turn_e_s", 0)] turn_e_s;
val _ = translate_gate [("turn_e_n", 0)] turn_e_n;
val _ = translate_gate [("fork_e_es", 0)] fork_e_es;
val _ = translate_gate [("fork_e_en", 0)] fork_e_en;
val _ = translate_gate [("half_adder_ee_es", 0)] half_adder_ee_es;
val _ = translate_gate [("half_adder_ee_ee", 0)] half_adder_ee_ee;
val _ = translate_gate [("slow_wire_e_e", 0)] slow_wire_e_e;

val _ = (max_print_depth := 10); (* avoids blow up in size of Theory.sig file *)
val _ = export_theory();
