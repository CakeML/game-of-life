open preamble gol_simulationTheory gol_coreTheory gol_specTheory;
open gol_interfacesTheory;

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

fun parse_file filename = let
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
  in data end;

val (d1::d2::_) = parse_file filename;

val _ = (max_print_depth := 10);

fun min m n = if n < m then n else m;
fun list_min [] = hd []
  | list_min [n] = n
  | list_min (n::m::ns) = min n (list_min (m::ns));

fun max m n = if n > m then n else m;
fun list_max [] = hd []
  | list_max [n] = n
  | list_max (n::m::ns) = max n (list_max (m::ns));

fun mk_list_list d = let
  val none = optionSyntax.mk_none bool
  fun some tm = optionSyntax.mk_some tm
  fun lookup [] (x:int * int) = none
    | lookup ((y,b)::xs) x = if x = y then some b else lookup xs x
  fun list225 f = List.tabulate (225,fn i => f (i-100));
  fun mk_list tms = listSyntax.mk_list(tms,type_of (hd tms))
  val d = map (fn ((i,j),x) => ((i-63,j+12),x)) d
  val dx = map (fst o fst) d
  val dx_min = list_min dx
  val dx_max = list_max dx
  val dy = map (snd o fst) d
  val dy_min = list_min dy
  val dy_max = list_max dy
  val _ = print "\n----\n"
  in mk_list (list225 (fn j => mk_list (list225 (fn i => lookup d (i,j))))) end

val policy = ‘λn xs. T’

val xs = d1

fun prove_steps_sim_base policy xs = let
  val th = steps_sim_base |> Q.SPECL [‘225’,‘225’,policy]
  val th = SPEC (mk_list_list xs) th
  val frame_ok_tm = th |> concl |> dest_imp |> fst
  val frame_ok_th = prove(frame_ok_tm,
    rewrite_tac [frame_ok_def,EVAL “225 ≠ 0:num”]
    \\ CONV_TAC (PATH_CONV "lrlr" listLib.LENGTH_CONV)
    \\ rewrite_tac [EVERY_DEF]
    \\ rpt strip_tac
    \\ CONV_TAC BETA_CONV
    \\ CONV_TAC (PATH_CONV "lr" listLib.LENGTH_CONV)
    \\ rewrite_tac [])
  in MP th frame_ok_th end

val th = prove_steps_sim_base policy d1

val zs = d2
val n = 1
val policy_def = TRUTH

fun prove_steps_sim_step policy_def n th zs = let
  val _ = print (int_to_string n ^ " ")
  val th1 = MATCH_MP steps_sim_step_thm th
  val th2 = SPEC (mk_list_list zs) th1
            |> CONV_RULE (PATH_CONV "rllr" EVAL)
  val (x,_) = th2 |> concl |> dest_imp
  val (borders_tm,x) = x |> dest_conj
  val (policy_tm,next_sim_tm) = x |> dest_conj
  val borders_th = prove(borders_tm,
    rewrite_tac [frame_borders_none_def,HD,LAST_CONS]
    \\ rewrite_tac [EVERY_DEF,combinTheory.o_THM,HD,IS_NONE_DEF,LAST_CONS])
(*
  set_goal([],policy_tm)
*)
  val policy_rw =
    policy_tm
    |> ONCE_REWRITE_CONV [policy_def]
    |> CONV_RULE (PATH_CONV "rlllr" EVAL)
    |> CONV_RULE (PATH_CONV "rlrllr" EVAL)
    |> CONV_RULE (RAND_CONV $ REWRITE_CONV [])

  val (tm,y) = dest_comb (policy_rw |> concl |> rand)
  val (_,tm) = dest_comb tm
val a =
  listSyntax.dest_list tm |> fst |> map (fst o listSyntax.dest_list) |>
    map (map (aconv T))
val b =
  listSyntax.dest_list y |> fst |> map (fst o listSyntax.dest_list) |>
    map (map optionSyntax.is_some)
  fun b2n true = 1 | b2n _ = 0
  val _ = print "\n"
  val _ = map2 (map2 (fn b1 => fn b2 => b2n b1 + b2n b2)) a b
    |> filter (fn xs => mem 2 xs)
    |> map (fn xs => List.drop(xs,length xs - 70))
    |> map (fn xs => concat (map int_to_string xs) ^ "\n")
    |> concat |> print
  val policy_th = prove(policy_tm,
    (* ONCE_REWRITE_TAC [policy_def]
    \\ REWRITE_TAC [EVAL “0<20:num”]
    \\ REWRITE_TAC [EVAL “0<20:num”,check_mask_def,check_mask_rows_def,TL]
    \\ EVAL_TAC \\ *) cheat)
(*
val tm = top_goal() |> snd
val (tm,y) = dest_comb tm
val (_,tm) = dest_comb tm

val a =
  listSyntax.dest_list tm |> fst |> map (fst o listSyntax.dest_list) |>
    map (map (aconv T))

val b =
  listSyntax.dest_list y |> fst |> map (fst o listSyntax.dest_list) |>
    map (map optionSyntax.is_some)

fun b2n true = 1 | b2n _ = 0

  map2 (map2 (fn b1 => fn b2 => b2n b1 + b2n b2)) a b
  |> filter (fn xs => mem 2 xs)
  |> map (fn xs => concat (map int_to_string xs) ^ "\n")
  |> concat |> print
*)
  fun case_all_goal_vars_tac (asms,goal) = let
    val vs = free_vars goal
    fun tac [] = all_tac
      | tac (v::vs) = tmCases_on v [] THEN tac vs
    in tac vs (asms,goal) end
  val next_sim_th = prove(next_sim_tm,
    rewrite_tac [next_sim_def,MAP,K_THM]
    \\ rewrite_tac [next_frame_def,next_row_none,bool_def]
    \\ rewrite_tac [next_row_def,MAP,K_THM]
    \\ rpt conj_tac
    \\ TRY (rewrite_tac [bool_def,gol_simp] \\ NO_TAC)
    \\ case_all_goal_vars_tac
    \\ rewrite_tac [bool_def,gol_simp])
  in MP th2 (LIST_CONJ [borders_th,policy_th,next_sim_th]) end;

fun prove_steps policy policy_def filename = let
  val _ = print ("Reading " ^ filename ^ " ... ")
  val data = parse_file filename
  val _ = print "done.\n"
  val _ = print "Simulating steps: "
  val th0 = prove_steps_sim_base policy (hd data)
(*
  val th = th0
  val n = 1
  val (d::_) = tl data
*)
  fun steps n th0 [] = th0
    | steps n th0 (d::ds) = steps (n+1) (prove_steps_sim_step policy_def n th0 d) ds
  val th = steps 1 th0 (tl data)
  val _ = print "done.\n"
  in th end;

(*
Theorem wire_e_e = prove_steps policy policy_def "lwss-wire-e-e.rle.txt";
Theorem and_ns_w = prove_steps policy policy_def "lwss-and-ns-w.rle.txt";
*)

  val lemma = gol_specTheory.imp_spec_00 |> SPEC_ALL |> Q.GENL [‘ins’,‘outs’]
              |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  val ins = “[((-1:int,0:int),(EAST,a:bool))]”
  val outs = “[((1:int,0:int),(EAST,b:bool))]”

  val th = SPECL [ins,outs] lemma |> REWRITE_RULE [MAP,APPEND,FST]
  val th = th |> CONV_RULE (PATH_CONV "lr" EVAL) |> (fn th => MP th TRUTH)
  val c = SIMP_CONV std_ss [EVERY_DEF,MEM]
  val th = th |> CONV_RULE (PATH_CONV "lr" c) |> (fn th => MP th TRUTH)
  val c = REWRITE_CONV [FILTER,UNCURRY] THENC
          DEPTH_CONV BETA_CONV THENC
          REWRITE_CONV [PAIR_EQ,EVAL “1=0:int”,EVAL “-1=0:int”,EVAL “-1=1:int”,
                                EVAL “0=1:int”,EVAL “0=-1:int”,EVAL “1=-1:int”,
                                interface_rewrites]
  val th = th |> CONV_RULE (PATH_CONV "lr" c)
  val tm = th |> concl |> dest_imp |> fst |> rator |> rator |> rator |> rand
  val policy_def = zDefine ‘policy = ^tm’
  val th = th |> REWRITE_RULE [GSYM policy_def]
  val policy_def = policy_def
    |> CONV_RULE (REWRITE_CONV [border_e, border_w, border_n, border_s])
    |> CONV_RULE (RAND_CONV EVAL)
    |> ONCE_REWRITE_RULE [FUN_EQ_THM]
    |> SPEC_ALL
    |> CONV_RULE $ RAND_CONV BETA_CONV
  val policy = policy_def |> concl |> dest_eq |> fst |> rator |> ANTIQUOTE |> single
  val lemma = prove_steps policy policy_def filename
  val th = MATCH_MP th lemma

(*
max_print_depth := 10
*)

val _ = export_theory();
