open HolKernel bossLib boolLib Parse;
open gol_simLib gol_simTheory boolSyntax computeLib cv_transLib
     cv_stdTheory gol_sim_cvTheory gol_simSyntax;

val _ = new_theory "gol_gates";

fun ERR x = mk_HOL_ERR "gol_gatesScript" x ""

fun tr_var 0 = A_tm
  | tr_var 1 = B_tm
  | tr_var _ = raise Fail "unknown variable"

fun tr_bexp True         = True_tm
  | tr_bexp False        = False_tm
  | tr_bexp (Var (v, n)) = mk_binop Var_tm (tr_var v, numSyntax.term_of_int n)
  | tr_bexp (Not x)      = mk_monop Not_tm (tr_bexp x)
  | tr_bexp (And (x, y)) = mk_binop And_tm (tr_bexp x, tr_bexp y)
  | tr_bexp (Or (x, y))  = mk_binop Or_tm (tr_bexp x, tr_bexp y)

fun tr_vector ty f =
  Vector.foldr (fn (a, r) => listSyntax.mk_cons (f a, r)) (listSyntax.mk_nil ty)

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
  if term_eq False_tm t then False
  else if term_eq True_tm t then True
  else if can dest_Var t then
    Var ((dest_var' ## numSyntax.int_of_term) (dest_Var t))
  else if can dest_And t then And ((dest_bexp ## dest_bexp) (dest_And t))
  else if can dest_Or t then Or ((dest_bexp ## dest_bexp) (dest_Or t))
  else if can dest_Not t then Not (dest_bexp (dest_Not t))
  else raise ERR "dest_bexp"

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
    (* <workaround for https://hol.zulipchat.com/#narrow/channel/486798-.E2.9D.84.EF.B8.8F-HOL4/topic/cv.20theorems.20not.20showing.20up.20in.20another.20file/near/503146927> *)
    val _ = save_thm (stem^"_cv_eq'[cv_rep]", definition (stem^"_cv_def") |> SPEC_ALL |>
      INST [mk_var ("x", cvSyntax.cv) |-> cvSyntax.mk_cv_num (numSyntax.term_of_int 0)] |> SYM)
    (* </workaround> *)
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

val _ = (max_print_depth := 10); (* avoids blow up in size of Theory.sig file *)
val _ = export_theory();
