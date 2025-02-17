open HolKernel bossLib gol_simLib gol_rulesTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory gol_sim_cvTheory;

val _ = new_theory "gol_gates";

local
val A_tm  = prim_mk_const {Name = "A",  Thy = "gol_rules"}
val B_tm  = prim_mk_const {Name = "B",  Thy = "gol_rules"}
val N_tm  = prim_mk_const {Name = "N",  Thy = "gol_rules"}
val E_tm  = prim_mk_const {Name = "E",  Thy = "gol_rules"}
val S_tm  = prim_mk_const {Name = "S",  Thy = "gol_rules"}
val W_tm  = prim_mk_const {Name = "W",  Thy = "gol_rules"}
val true_tm  = prim_mk_const {Name = "True",  Thy = "gol_rules"}
val false_tm = prim_mk_const {Name = "False", Thy = "gol_rules"}
val mk_var   = mk_binop (prim_mk_const {Name = "Var", Thy = "gol_rules"})
val mk_not   = mk_monop (prim_mk_const {Name = "Not", Thy = "gol_rules"})
val mk_and   = mk_binop (prim_mk_const {Name = "And", Thy = "gol_rules"})
val mk_or    = mk_binop (prim_mk_const {Name = "Or",  Thy = "gol_rules"})

in
fun tr_var "a" = A_tm
  | tr_var "b" = B_tm
  | tr_var _ = raise Fail "unknown variable"

fun tr_var_i 0 = A_tm
  | tr_var_i 1 = B_tm
  | tr_var_i _ = raise Fail "unknown variable"

fun tr_bexp True         = true_tm
  | tr_bexp False        = false_tm
  | tr_bexp (Var (v, n)) = mk_var (tr_var v, numSyntax.term_of_int n)
  | tr_bexp (Not x)      = mk_not (tr_bexp x)
  | tr_bexp (And (x, y)) = mk_and (tr_bexp x, tr_bexp y)
  | tr_bexp (Or (x, y))  = mk_or (tr_bexp x, tr_bexp y)

fun tr_vector ty f =
  Vector.foldr (fn (a, r) => listSyntax.mk_cons (f a, r)) (listSyntax.mk_nil ty)

val tr_bexpss = tr_vector ``:bexp list`` (tr_vector ``:bexp`` tr_bexp)

fun tr_dir N = N_tm
  | tr_dir E = E_tm
  | tr_dir S = S_tm
  | tr_dir W = W_tm

fun tr_io_port i (((a, b), d):io_port) =
  pairSyntax.mk_pair (
    pairSyntax.mk_pair (
      intSyntax.term_of_int (Arbint.fromInt a),
      intSyntax.term_of_int (Arbint.fromInt b)),
    pairSyntax.mk_pair (
      tr_dir d,
      mk_var (tr_var_i i, numSyntax.term_of_int 0 (* ?? *))))

val tr_io_ports = let
  val ty = ``:(int # int) # dir # bexp``
  in fn l => listSyntax.mk_list (mapi tr_io_port l, ty) end

end

fun translate_gate stem gate = let
  val board = run_to_fixpoint (load gate)
  val tm = tr_bexpss board
  val defn = boolLib.new_definition (stem^"_def",
    mk_eq (mk_var (stem, ``:bexp list list``), tm))
  val rows = lhs (concl defn)
  val w = numSyntax.term_of_int (#width gate)
  val h = numSyntax.term_of_int (#height gate)
  val ins = tr_io_ports (#inputs gate)
  val outs = tr_io_ports (#outputs gate)
  val thm = store_thm (stem^"_thm",
    ``simulation_ok ^w ^h ^ins ^outs ^rows``,
    CONV_TAC cv_eval)
  in (defn, thm) end;

val _ = translate_gate "and_en_e" and_en_e;
(* val _ = translate_gate "and_es_e" and_es_e;
val _ = translate_gate "and_ew_n" and_ew_n;
val _ = translate_gate "or_en_e" or_en_e;
val _ = translate_gate "not_e_e" not_e_e;
val _ = translate_gate "turn_e_s" turn_e_s;
val _ = translate_gate "turn_e_n" turn_e_n;
val _ = translate_gate "wire_e_e" wire_e_e;
val _ = translate_gate "fork_e_es" fork_e_es;
val _ = translate_gate "fork_e_en" fork_e_en;
val _ = translate_gate "cross_es_es" cross_es_es;
val _ = translate_gate "cross_en_en" cross_en_en;
val _ = translate_gate "half_adder_ee_es" half_adder_ee_es;
val _ = translate_gate "half_adder_ee_ee" half_adder_ee_ee;
val _ = translate_gate "slow_wire_e_e" slow_wire_e_e; *)

val _ = export_theory();
