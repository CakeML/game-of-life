open preamble gol_simulationTheory;

val _ = new_theory "gol_wires";

val _ = (max_print_depth := 0);

fun read_file filename = let
  val f = TextIO.openIn filename
  fun loop aux =
    case TextIO.inputLine(f) of
      NONE => List.rev aux
    | SOME line => loop (line :: aux)
  val lines = loop []
  val _ = TextIO.closeIn(f)
  in lines end

val filename = "lwss-and-ns-w.rle.txt"
val filename = "lwss-wire-e-e.rle.txt"

val xs = read_file filename
fun part p xs = let
  fun partition_at p [] aux res = if null aux then rev res else rev (rev aux :: res)
    | partition_at p (x::xs) aux res =
        if p x then
          partition_at p xs [] (if null aux then res else rev aux :: res)
        else
          partition_at p xs (x::aux) res
  in partition_at p xs [] [] end
val ps = part (fn s => String.isPrefix "GOL" s orelse String.isPrefix "End" s) xs
fun parse_bool_str s = Term [QUOTE (s ^ ":bool")]
fun parse_line l = let
  val rs = String.tokens (fn c => c = #":") l
  val p = hd rs
  val t = hd (tl rs)
  val tm = parse_bool_str t
  val rs = String.tokens (fn c => mem c [#",",#")",#"("]) p
  val x = rs |> el 1 |> string_to_int
  val y = rs |> el 2 |> string_to_int
  in ((x,y),tm) end
val data = map (map parse_line) ps

val (d1::d2::_) = data

val _ = (max_print_depth := 500);

fun prove_all_distinct goal =
  prove(goal,
    (irule SORTED_ii_lt_IMP
     \\ fs [sortingTheory.SORTED_DEF]
     \\ EVAL_TAC) ORELSE EVAL_TAC)

fun prove_step_to_state d1 d2 = let
  fun mk_int i = intSyntax.term_of_int (Arbint.fromInt i)
  fun mk_pair f g (x,y) = pairSyntax.mk_pair(f x, g y)
  fun mk_iib_list xs = listSyntax.mk_list(xs,“:(int # int) # bool”)
  fun mk_ii_list xs = listSyntax.mk_list(xs,“:int # int”)
  fun infl [] = []
    | infl ((x,y)::xs) =
       (x-1,y-1) :: (x,y-1) :: (x+1,y-1) ::
       (x-1,y  ) :: (x,y  ) :: (x+1,y  ) ::
       (x-1,y+1) :: (x,y+1) :: (x+1,y+1) ::  infl xs
  fun remove_dups [] = []
    | remove_dups [x] = [x]
    | remove_dups (x::y::ys) =
        if x = y then remove_dups (x::ys) else x :: remove_dups (y::ys)
  val ps = infl (d1 |> map fst)
           |> sort (fn (i,j) => fn (i',j') => (i < i') orelse ((i = i') andalso (j < j')))
           |> remove_dups
  val xs_tm = map (mk_pair (mk_pair mk_int mk_int) I) d1 |> mk_iib_list
  val ys_tm = map (mk_pair (mk_pair mk_int mk_int) I) d2 |> mk_iib_list
  val ps_tm = map (mk_pair mk_int mk_int) ps |> mk_ii_list
  val th = SPECL [xs_tm,ys_tm,ps_tm] IMP_step_to_state
           |> PURE_REWRITE_RULE [MAP,FST]
           |> CONV_RULE (PATH_CONV "lr" (REWR_CONV LET_THM THENC BETA_CONV))
           |> CONV_RULE (PATH_CONV "lr" (REWR_CONV LET_THM THENC BETA_CONV))
  val goal = th |> concl |> dest_imp |> fst
  val (dist_goal1,goal) = dest_conj goal
  val (dist_goal2,goal) = dest_conj goal
  val (every_mem_goal,goal) = dest_conj goal
  val (infl_goal,check_pos_goal) = dest_conj goal
  val _ = print " - Proving ALL_DISINCT\n"
  val dist_thm1 = prove_all_distinct dist_goal1
  val dist_thm2 = prove_all_distinct dist_goal2
  val _ = print " - Proving EVERY_MEM\n"
  val every_mem_thm = prove_all_distinct every_mem_goal
  val _ = print " - Proving check_infl\n"
  val check_infl_thm = prove_all_distinct infl_goal
  val _ = print " - Proving check_pos\n"
  fun case_all_goal_vars_tac (asms,goal) = let
    val vs = free_vars goal
    fun tac [] = all_tac
      | tac (v::vs) = tmCases_on v [] THEN tac vs
    in tac vs (asms,goal) end
(*
    set_goal([],check_pos_goal)
*)
  val check_pos_thm = prove(check_pos_goal,
    rpt (once_rewrite_tac [EVERY_DEF]
         \\ conj_tac >- (EVAL_TAC \\ rewrite_tac [gol_simTheory.gol_simp]
                         \\ case_all_goal_vars_tac
                         \\ rewrite_tac [gol_simTheory.gol_simp]))
    \\ rewrite_tac [EVERY_DEF])
  val _ = print " - Composing all lemmas\n"
  val lemma =
    LIST_CONJ [dist_thm1,dist_thm2,every_mem_thm,check_infl_thm,check_pos_thm]
  in MP th lemma end

fun prove_all_steps data = let
  fun prove_steps i [] = []
    | prove_steps i [d] = []
    | prove_steps i (d1::d2::ds) = let
    val _ = print ("Step " ^ int_to_string i ^ ":\n")
    val th = prove_step_to_state d1 d2
    in th :: prove_steps (i+1) (d2::ds) end
  in prove_steps 1 data end

val thms = time prove_all_steps (curry List.take data 3);

val _ = export_theory();
