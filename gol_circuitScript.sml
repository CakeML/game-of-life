(* val _ = HOL_Interactive.toggle_quietdec(); *)
open HolKernel bossLib gol_simLib gol_rulesTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory gol_sim_cvTheory;

val _ = new_theory "gol_circuit";

structure CircuitDiag = struct

type diag = string * string vector

val CSIZE = 21
val SIZE = CSIZE * 2 + 1

fun parse [QUOTE s]: diag = let
    val lines = String.fields (fn x => x = #"\n") s
    val (header, lines) = case lines of _::a::b => (a,b) | _ => raise Bind
    val lines = Vector.fromList (List.take (lines, length lines - 2))
    in (header, lines) end
  | parse _ = raise Bind

datatype small_gate = Node | SlowNode | AndG | OrG | NotG
datatype large_gate = HalfAddG | SlowWire

datatype sigil =
    Empty
  | Wire of dir
  | Wall of bool
  | Small of small_gate
  | Large of large_gate

fun coord ((_, lines):diag) (x, y) =
  case String.substring (Vector.sub (lines, y), 3 + 2 * x, 2) of
    "  " => Empty
  | "> " => Wire E
  | "v " => Wire S
  | "< " => Wire W
  | "^ " => Wire N
  | "| " => Wall true
  | "- " => Wall false
  | "o " => Small Node
  | "s " => Small SlowNode
  | "A " => Small AndG
  | "O " => Small OrG
  | "N " => Small NotG
  | "H " => Large HalfAddG
  | "S " => Large SlowWire
  | s => raise Fail s

fun sigil_to_string s = case s of
    Empty => "  "
  | Wire E => "> "
  | Wire S => "v "
  | Wire W => "< "
  | Wire N => "^ "
  | Wall true => "| "
  | Wall false => "- "
  | Small Node => "o "
  | Small SlowNode => "s "
  | Small AndG => "A "
  | Small OrG => "O "
  | Small NotG => "N "
  | Large HalfAddG => "H "
  | Large SlowWire => "S "

fun lineHeader line =
  (String.substring (line, 0, 3), String.extract (line, 3 + 2 * SIZE, NONE))

fun rotate_sigil s = case s of
    Wire dir => Wire (rotate_dir dir)
  | Wall b => Wall (not b)
  | s => s

fun rotate (d as (header, lines):diag) = let
  val lines' = Vector.tabulate (SIZE, fn i => let
    val (left, right) = lineHeader (Vector.sub (lines, i))
    val body = List.tabulate (SIZE, fn j =>
      sigil_to_string $ rotate_sigil (coord d (i, SIZE-1-j)))
    in left ^ String.concat body ^ right end)
  in (header, lines') end

fun print' ((header, lines):diag) = (
  print (header^"\n");
  Vector.app (fn s => print (s^"\n")) lines;
  print (header^"\n"));

fun neighbors d (x, y) = let
  fun get a b = coord d (2*x+a, 2*y+b)
  in (get 1 1, (get 0 1, get 1 0, get 2 1, get 1 2)) end

fun smallNodePattern n = case n of
    Node => [
      (terminator_e, (Wire E, Empty, Empty, Empty)),
      (wire_e_e, (Wire E, Empty, Wire E, Empty)),
      (fast_turn_e_s, (Wire E, Empty, Empty, Wire S)),
      (turn_e_n, (Wire E, Wire N, Empty, Empty)),
      (fork_e_es, (Wire E, Empty, Wire E, Wire S)),
      (fork_e_en, (Wire E, Wire N, Wire E, Empty)),
      (cross_es_es, (Wire E, Wire S, Wire E, Wire S))]
  | SlowNode => [
    (slow_wire_e_e, (Wire E, Empty, Wire E, Empty)),
    (slow_turn_e_s, (Wire E, Empty, Empty, Wire S))]
  | NotG => [(not_e_e, (Wire E, Empty, Wire E, Empty))]
  | AndG => [
      (and_en_e, (Wire E, Empty, Wire E, Wire N)),
      (and_es_e, (Wire E, Wire S, Wire E, Empty)),
      (and_ew_n, (Wire E, Wire N, Wire W, Empty))]
  | OrG => [(or_en_e, (Wire E, Empty, Wire E, Wire N))]

fun rotate_sigils (a,b,c,d) =
  (rotate_sigil d, rotate_sigil a, rotate_sigil b, rotate_sigil c)

fun rotate_sigils22 (a,b,c,d) =
  (rotate_sigils d, rotate_sigils a, rotate_sigils b, rotate_sigils c)

fun rotate_sigils31 (false,a,b,c) =
    (true, rotate_sigils a, rotate_sigils b, rotate_sigils c)
  | rotate_sigils31 (true,a,b,c) =
    (false, rotate_sigils c, rotate_sigils b, rotate_sigils a)

fun match_with f pat nei = let
  exception Found of gate * int
  fun go 4 _ = ()
    | go i (gate, pat) =
      if nei = pat then raise Found (gate, i) else
      go (i+1) (gate, f pat)
  in
    (app (go 0) pat; raise Match)
    handle Found out => out
  end

type gates = ((int * int) * (gate * int)) list

val int2cmp = pair_compare (Int.compare, Int.compare)
val int3cmp = pair_compare (int2cmp, Int.compare)

fun recognize d = let
  val gates = ref []
  val _ = for_loop 0 CSIZE (fn y =>
    for_loop 0 CSIZE (fn x => let
      fun push (x, y) (gate, i) = gates := ((x, y), (gate, i)) :: !gates
      val r = neighbors d (x, y)
      fun nn p = #2 (neighbors d p)
      in
        (case r of
          (Empty, (Empty, Empty, Empty, Empty)) => ()
        | (Small n, nei) => push (x, y) (match_with rotate_sigils (smallNodePattern n) nei)
        | (Large n, nei) =>
          if #1 (neighbors d (x-1, y)) = Large n orelse
             #1 (neighbors d (x, y-1)) = Large n then () else
          (case n of
            HalfAddG => push (x, y) $ match_with rotate_sigils22
              [(half_adder_ee_es, (
                (Wire E, Empty, Wall false, Wall true),
                (Wall false, Empty, Wire E, Wall true),
                (Wall false, Wall true, Empty, Wire S),
                (Wire E, Wall true, Wall false, Empty))),
              (half_adder_ee_ee, (
                (Wire E, Empty, Wall false, Wall true),
                (Wall false, Empty, Wire E, Wall true),
                (Wall false, Wall true, Wire E, Empty),
                (Wire E, Wall true, Wall false, Empty)))]
              (nei, nn (x+1, y), nn (x+1, y+1), nn (x, y+1))
          | SlowWire => push (x, y) $ match_with rotate_sigils31
              [(slow_wire_e_e, (false,
                (Wire E, Empty, Wall false, Empty),
                (Wall false, Empty, Wall false, Empty),
                (Wall false, Empty, Wire E, Empty)))]
              (if #3 nei = Wall false then
                (false, nn (x, y), nn (x+1, y), nn (x+2, y))
              else (true, nn (x, y), nn (x, y+1), nn (x, y+2))))
        | _ => (PolyML.print ((x, y), r); raise Fail "unknown node type"))
        handle Match => (PolyML.print ((x, y), r); raise Fail "unknown connection pattern")
      end))
  in !gates end

fun inbounds (a, b) = 0 <= a andalso a < CSIZE andalso 0 <= b andalso b < CSIZE

datatype rvalue =
    Cell of int * int
  | RAnd of rvalue * rvalue
  | ROr of rvalue * rvalue
  | RNot of rvalue
  | RXor of rvalue * rvalue

datatype evalue =
    Clock
  | NotClock
  | NextCell
  | ThisCell
  | ThisCellUntilClock of int

datatype value = Regular of int * rvalue | Exact of int * evalue

fun mk_ROr p = case p of
    (RAnd (a1, ROr (RAnd (a2, RNot b1), RAnd (RNot a3, RAnd (b2, RNot b3)))),
     RAnd (RNot a4, ROr (a5, b4))) =>
    if (a1,a1,a1,a1,b1,b1,b1)=(a2,a3,a4,a5,b2,b3,b4) then RXor (a1, b1)
    else ROr p
  | _ => ROr p

fun delay d (Regular (d', v)) = Regular (d + d', v)
  | delay d (Exact (d', v)) = Exact (d + d', v)

val nextCell = let
  val e1 = RXor (Cell (0, 1), Cell (~1, 1))
  val e2 = RXor (Cell (1, 0), Cell (1, 1))
  val e3 = RXor (Cell (0, ~1), Cell (1, ~1))
  val e4 = RXor (Cell (~1, 0), Cell (~1, ~1))
  val e5 = RAnd (Cell (0, 1), Cell (~1, 1))
  val e6 = RAnd (Cell (0, ~1), Cell (1, ~1))
  val e7 = RAnd (Cell (~1, 0), Cell (~1, ~1))
  val e8 = RAnd (Cell (1, 0), Cell (1, 1))
  val e9 = (e1, RXor (e2, RXor (e3, e4)))
  val e10 = ROr (RAnd (e2, RXor (e3, e4)), e8)
  val e11 = ROr (RAnd e9, e5)
  val e12 = (ROr (RAnd (e3, e4), e6), e7)
  val e13 = (e11, RXor (e10, RXor e12))
  in
    RAnd (ROr (Cell (0, 0), RXor e9), RAnd (RXor e13,
      RNot (ROr (RAnd e13, ROr (RAnd (e10, RXor e12), RAnd e12)))))
  end

type io_port = (int*int)*dir*value

val gateData = ref (Redblackmap.mkDict String.compare)
fun getGateData (gate, i) = let
  val key = List.nth (#stems gate, i)
  in
    (key, case Redblackmap.peek (!gateData, key) of
      SOME v => v
    | NONE => let
      val {inputs, outputs, ...} = gol_simLib.rotate i (load gate)
      val value = case (#stems gate, (inputs, outputs)) of
          ("cross_es_es" :: _,
            ([(a1,a2,Var(_,a3)),(b1,b2,Var(_,b3))],
             [(o1,o2,Var(_,o3)),(p1,p2,Var(_,p3))])) =>
            [([(a1,a2,Var(0,a3))],[(o1,o2,Var(0,o3))]),
             ([(b1,b2,Var(0,b3))],[(p1,p2,Var(0,p3))])]
        | (_, v) => [v]
      in gateData := Redblackmap.insert (!gateData, key, value); value end)
  end

fun wpos ((x,y),(a,b)) = (2*x+a, 2*y+b)
fun dirToXY d = case d of E => (1,0) | S => (0,1) | W => (~1,0) | N => (0,~1)

fun build d (gates:gates) period pulse (ins: io_port list, outs: io_port list) = let
  datatype target = Gate of (int * int) * int | Done of value
  val wireIn = ref $ foldl (fn ((w, d, v), map) =>
    Redblackmap.insert (map, wpos (w, dirToXY d), Done v)) (Redblackmap.mkDict int2cmp) outs
  val gates = ref (foldl
    (fn ((p, gate), map) => let
      val (g, ls) = getGateData gate
      in #2 $ foldl
        (fn (data, (i, map)) => (
          C app (#1 data) (fn (x, _, _) =>
            wireIn := Redblackmap.insert (!wireIn,
              wpos (p, x), Gate (p, i)));
          (i+1, Redblackmap.insert (map, (p, i), (ref false, g, data)))))
        (0, map) ls end)
    (Redblackmap.mkDict int3cmp) gates)
  val queue = ref []
  val wires = ref (Redblackmap.mkDict int2cmp)
  fun isMissingWire p port = not (Redblackmap.inDomain (!wires, wpos (p, #1 port)))
  fun runGate (missing, (p,i), g, ins, outs) = let
    (* val _ = TextIO.output (file, "run gate " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n") *)
    val ins = Vector.fromList $ C map ins (fn
        (x, _, Var (_, delay)) => (delay, Redblackmap.find (!wires, wpos (p, x)))
      | _ => raise Match)
    fun evalExp (Var (i, d')) = let
        val (d, value) = Vector.sub (ins, i)
        in delay (d - d') value end
      | evalExp (Or (e1, e2)) = (case (evalExp e1, evalExp e2) of
          (Regular (d1, v1), Regular (d2, v2)) =>
          Regular (Int.max (d1, d2), mk_ROr (v1, v2))
        | (Exact (d1, ThisCell), Regular (d2, v2)) =>
          Regular (Int.max (d1, d2), mk_ROr (Cell (0, 0), v2))
        | (Exact (d1, NextCell), Exact (d2, ThisCellUntilClock d3)) =>
          if d1 = d2 + d3 then Exact (d1 - period, ThisCell)
          else (PolyML.print (d2, d1, d2 + d3); raise Fail "clock timing 1")
        | r => (PolyML.print (ins, Or (e1, e2), r); raise Fail "evalExp Or"))
      | evalExp (And (e1, e2)) = (case (evalExp e1, evalExp e2) of
          (Regular (d1, v1), Regular (d2, v2)) =>
          Regular (Int.max (d1, d2), RAnd (v1, v2))
        | (Exact (d1, ThisCell), Exact (d2, NotClock)) =>
          if d1 > d2 orelse pulse < d1 then
            (PolyML.print (pulse, d1, d2); raise Fail "clock timing 2") else
          Exact (d1, ThisCellUntilClock (d2 - d1))
        | (Exact (d1, Clock), Regular (d2, v2)) =>
          if v2 <> nextCell then raise Fail "calculated wrong function" else
          if d1 < d2 then (PolyML.print (d1, d2); raise Fail "clock timing 3") else
          Exact (d1, NextCell)
        | r => (PolyML.print (ins, And (e1, e2), r); raise Fail "evalExp And"))
      | evalExp (Not e1) = (case evalExp e1 of
          Regular (d1, v1) => Regular (d1, RNot v1)
        | Exact (d1, Clock) => Exact (d1, NotClock)
        | _ => raise Fail "evalExp Not")
      | evalExp bv = (PolyML.print (ins, bv); raise Fail "evalExp other")
    in
      app (fn (x, d, bv) => let
        (* val w = wpos (p, x)
        val _ = TextIO.output (file, "out wire "
          ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^" -> "
          ^ Int.toString (#1 w)^"," ^ Int.toString (#2 w)^" @ "
          ^ Int.toString (#1 w div 2)^"," ^ Int.toString (#2 w div 2)^"\n") *)
        in processWire (wpos (p, x), evalExp bv) end) outs
    end
  and processQueue (missing, (p,i), r, g, ins, outs) = if !r then
        (* (TextIO.output (file, "already done gate " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n"); *)
   true else
    case filter (isMissingWire p) missing of
      [] => (
        (* TextIO.output (file, "set gate " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n"); *)
        r := true; runGate (missing, (p,i), g, ins, outs); true)
    | missing => (
      (* TextIO.output (file, "enqueue " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n"); *)
      queue := (missing, (p,i), r, g, ins, outs) :: !queue; false)
  and processWire (w, value) =
    case Redblackmap.peek (!wires, w) of
      SOME old => (case (value, old) of
        (Exact (n1, Clock), Exact (n2, Clock)) =>
          if n1 = n2 + period then () else
          (PolyML.print ("clock period mismatch", period, n1 - n2); ())
      | (Exact (n1, ThisCell), Exact (n2, ThisCell)) =>
        if n1 = n2 then () else
          (PolyML.print ("thiscell mismatch", period, period + n1 - n2); ())
      | (e1, e2) => if e1 = e2 then () else
          (PolyML.print ("cycle mismatch", w, value, old); ()))
    | NONE => let
      val (wireIn', tgt) = Redblackmap.remove (!wireIn, w)
      val _ = wireIn := wireIn'
      (* val _ = TextIO.output (file, "insert wire "
         ^ Int.toString (#1 w)^"," ^ Int.toString (#2 w)^" @ "
          ^ Int.toString (#1 w div 2)^"," ^ Int.toString (#2 w div 2)^"\n") *)
      val _ = wires := Redblackmap.insert (!wires, w, value)
      in
        case tgt of
          Gate p => let
          val (r, g, (ins, outs)) = Redblackmap.find (!gates, p)
          in (processQueue (ins, p, r, g, ins, outs); ()) end
        | Done out => (
          (* PolyML.print ("output match", w, value, out); *)
          if value = out then () else
          if
            case (value, out) of
              (Exact (d1, ThisCell), Regular (d2, Cell (0, 0))) => d1 = d2
            | _ => false
          then ()
          else
             (PolyML.print ("output mismatch", w, value, out); ()))
      end
  val _ = app (fn (w,d,v) => processWire (wpos (w, dirToXY d), v)) ins
  fun loop () = case !queue of
    [] => ()
  | q =>
    if foldl (fn (x, r) => processQueue x orelse r) (queue := []; false) q then
      loop ()
    else raise Fail "queue stuck"
  val _ = loop ()
  (* val (header, lines) = d
  val lines' = Vector.tabulate (SIZE, fn y => let
    val (left, right) = lineHeader (Vector.sub (lines, y))
    val body = List.tabulate (SIZE, fn x =>
      case coord d (x, y) of
        w as Wire _ =>
        if Redblackmap.inDomain (!wires, (x-1, y-1)) then "* " else ". "
      | w =>
        if List.exists ((fn (a,b) => (x, y) = (2*a+1,2*b+1)) o #1 o #2) (!queue) then
          "% "
        else
          (* "+ " *)
        sigil_to_string w
        )
    in left ^ String.concat body ^ right end)
  val _ = print' (header, lines') *)
  in !wires end

fun getWire res p dir = Redblackmap.find (res, wpos (p, dirToXY dir))

end;

Quote diag = CircuitDiag.parse:
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
         ^   ^                                                               v   v         |
 0   o > o > o > o > o > o > o > o > o > o > o > o > o > o > s > s > s > s > o > o > o   0 |
     ^   ^   ^                       v                                       v   v   v     |
 1 > o > o > o > H - H > o > o > o > o > o > o > o > o > o   o > o > o > o > o > o > o > 1 |
     ^   ^       |   |               v                   v   ^               v   v   v     |
 2 > o > o > o > H - H > o > o > o > o > o > o > o > o > o > o > o > o       o   o > o > 2 |
     ^   ^                           v                   v   ^       v       v   v   v     |
 3   o   o           o > O > A > o > o > o > o           o   o       o       H - H   s   3 |
     ^   ^           ^   ^   ^       v       v           v   ^       v       |   |   v     |
 4   o   o   o > A > o > o > o       o   s > A > O > o > o > o > o   o   o < H - H   s   4 |
     ^   ^   ^   ^   ^   ^           v   ^       ^   v   v       v   v   v       v   v     |
 5   o   o   o   N   o   o           o > o > N > A < o   o > o > o > o > o > o   o   s   5 |
     ^   ^   ^   ^   ^   ^                                       v   v   v   v   v   v     |
 6   s   o < o < o < o < o < o < o < o < o < o < o < o < o < o < o   o   o   H - H   s   6 |
     ^       ^   ^       ^                                   v   v   v   v   |   |   v     |
 7   s   o > o > o > o > o   o < o < o < o < o < o < o < o < o   o   o   o   H - H   s   7 |
     ^   ^   ^   ^                                           v   v   v   v   v   v   v     |
 8   s   o   o   O < o < o   o < o < o < o < o < o < o < o < o   o   o   o > O   o   s   8 |
     ^   ^   ^   ^       ^                                   v   v   v       v   v   v     |
 9   s   o   H - H       o   o < o < o < o < o < o < o < o < o   o   o > o   o   o   s   9 |
     ^   ^   |   |       ^                                   v   v       v   v   v   v     |
10   s   o   H - H       o   o < o < o < o < o < o < o < o < o   o       H - H   o   s   10|
     ^   ^   ^   ^       ^                                   v   v       |   |   v   v     |
11   s   o   o   o < o   o   o < o < o < o < o < o < o < o < o   o       H - H   o   s   11|
     ^   ^   ^       ^   ^                                   v   v       v   v   v   v     |
12   s   o   O < o   o   o   o < o < o < o < o < o < o < o < o   o > o   o   o   o   s   12|
     ^   ^   ^   ^   ^   ^                                   v       v   v   v   v   v     |
13   s   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o < o < o < o < o   s   13|
     ^   |   |   ^   ^   ^                                   v   v   v   v   v       v     |
14   s   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o   o > o > o > o   s   14|
     ^   ^   ^   ^   ^   ^   v                                   v       v   v   v   v     |
15   s   o   o < o < o < o < o < o   o < o < o < o < o < o < o < o < o < o   o   o   s   15|
     ^   ^       ^   ^   ^   v   ^   v                           v           v   v   v     |
16   s   H - H > o   o   o   o   o   o           o < o < o < o < o < o < o < o   o   s   16|
     ^   |   |       ^   ^   v   ^   v           v               v               v   v     |
17   s   H - H       o   o < o < o < O < H - H < o   o < o < o < o < o           o   s   17|
     ^   ^   ^       ^       v   ^       |   |       v           v   ^           v   v     |
18 < o < o   o       o < o < o < o < o < H - H < o < O < H - H < o   H - H < o < o < o < 18|
     ^   ^   ^               v   ^                       |   |       |   |       v   v     |
19 < o < o < o < o < o < o < o   o < o < o < o < o < o < H - H < o < H - H < o < o < o < 19|
     ^   ^   ^                                                               v   v   v     |
20   o < o < o < s < s < s < s < s < s < s < s < s < s < s < s < s < s < s < o < o < o   20|
         ^   ^                                                               v   v         |
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
End

open CircuitDiag
(* val _ = HOL_Interactive.toggle_quietdec(); *)

fun go () = let
  val _ = PolyML.print_depth 6
  fun f ((x,y), dir, (a,b), delay) = let
    val (c,d) = dirToXY dir
    in
      (((x,y), dir, Regular (delay, Cell (a,b))),
       ((x+CSIZE*c,y+CSIZE*d), dir, Regular (delay, Cell (a+c,b+d))))
    end
  val dE = 174
  val dS = 132
  val dW = 62
  val dN = 123
  val dNE = dE + 22
  val dSE = dS + 21
  val dSW = dW + 22
  val dNW = dN + 21
  val phase = 0
  val period = 586
  val pulse = 18
  val (ins, outs) = unzip $ map f [
    ((~1, 1), E, (~1, 0), dW), ((~1, 2), E, (~1, ~1), dNW),
    ((19, ~1), S, (0, ~1), dN), ((18, ~1), S, (1, ~1), dNE),
    ((21, 19), W, (1, 0), dE), ((21, 18), W, (1, 1), dSE),
    ((1, 21), N, (0, 1), dS), ((2, 21), N, (~1, 1), dSW)];
  val asrt = [
    ((16, 0), E, Exact (phase, Clock)),
    ((11, 4), E, Exact (0, ThisCell))];
  (* val file = TextIO.openOut "log.txt" *)
  val res = build diag (recognize diag) period pulse (ins @ asrt, outs)
  (* val _ = TextIO.closeOut file *)
  in res end;

val _ = go ();

(*
val res = getWire (go ());
val w_thiscell = res (11,4) E;
val w_top_and = (res (9,4) E, res (10,3) S, res (10,4) E);
val w_not = (res (9,5) E, res (10,5) E);
val w_bot_and = (res (10,5) E, res (12,5) W, res (11,5) N);
val w_or = (res (11,5) N, res (10,4) E, res (11,4) E);
val w_clock = (res (7,0) E, res (8,0) S, res (8,0) E);
val w_train = (res (14,0) E, res (15,0) E, res (16,0) E);
*)

val _ = export_theory();
