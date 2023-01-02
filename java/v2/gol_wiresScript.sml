open preamble gol_simulationTheory gol_simTheory;

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
  fun list200 f = List.tabulate (200,fn i => f (i-100));
  fun mk_list tms = listSyntax.mk_list(tms,type_of (hd tms))
  val d = map (fn ((i,j),x) => ((i-75,j),x)) d
  val dx = map (fst o fst) d
  val dx_min = list_min dx
  val dx_max = list_max dx
  val dy = map (snd o fst) d
  val dy_min = list_min dy
  val dy_max = list_max dy
  val _ = print "\n----\n"
  val _ = print ("x-min/max: " ^ int_to_string dx_min ^ ", " ^ int_to_string dx_max ^ "\n")
  val _ = print ("y-min/max: " ^ int_to_string dy_min ^ ", " ^ int_to_string dy_max ^ "\n")
  val _ = print "----\n"
  in mk_list (list200 (fn j => mk_list (list200 (fn i => lookup d (i,j))))) end

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

val policy = ‘λn xs. T’

val xs = d1

fun prove_steps_sim_base policy xs = let
  val th = steps_sim_base |> Q.SPECL [‘200’,‘200’,policy]
  val th = SPEC (mk_list_list xs) th
  val frame_ok_tm = th |> concl |> dest_imp |> fst
  val frame_ok_th = prove(frame_ok_tm,
    REWRITE_TAC [frame_ok_def,EVAL “200 ≠ 0:num”]
    \\ CONV_TAC (PATH_CONV "lrlr" listLib.LENGTH_CONV)
    \\ REWRITE_TAC [EVERY_DEF]
    \\ rpt strip_tac
    \\ CONV_TAC BETA_CONV
    \\ CONV_TAC (PATH_CONV "lr" listLib.LENGTH_CONV)
    \\ REWRITE_TAC [])
  in MP th frame_ok_th end

val th = prove_steps_sim_base policy d1

val zs = d2
val n = 1

fun prove_steps_sim_step n th zs = let
  val _ = print (int_to_string n ^ " ")
  val th1 = MATCH_MP steps_sim_step_thm th
  val th2 = SPEC (mk_list_list zs) th1
            |> CONV_RULE (PATH_CONV "rllr" EVAL)
  val (x,_) = th2 |> concl |> dest_imp
  val (borders_tm,x) = x |> dest_conj
  val (policy_tm,next_sim_tm) = x |> dest_conj
  val borders_th = prove(borders_tm,
    REWRITE_TAC [frame_borders_none_def,HD,LAST_CONS]
    \\ REWRITE_TAC [EVERY_DEF,combinTheory.o_THM,HD,IS_NONE_DEF,LAST_CONS])
  val policy_th = prove(policy_tm,EVAL_TAC)
  val next_sim_th = prove(next_sim_tm,
    REWRITE_TAC [next_sim_def,MAP,K_THM]
    \\ REWRITE_TAC [next_frame_def,next_row_none,bool_def]
    \\ REWRITE_TAC [next_row_def,MAP,K_THM]
    \\ rpt conj_tac
    \\ TRY (REWRITE_TAC [bool_def,gol_simp] \\ NO_TAC))
  in MP th2 (LIST_CONJ [borders_th,policy_th,next_sim_th]) end;

fun prove_steps policy filename = let
  val _ = print ("Reading " ^ filename ^ " ... ")
  val data = parse_file filename
  val _ = print "done.\n"
  val _ = print "Simulating steps: "
  val th0 = prove_steps_sim_base policy (hd data)
  fun steps n th0 [] = th0
    | steps n th0 (d::ds) = steps (n+1) (prove_steps_sim_step n th0 d) ds
  val th = steps 1 th0 (tl data)
  val _ = print "done.\n"
  in th end;

Theorem wire_e_e = prove_steps policy "lwss-wire-e-e.rle.txt";
Theorem and_ns_w = prove_steps policy "lwss-and-ns-w.rle.txt";

val _ = export_theory();
