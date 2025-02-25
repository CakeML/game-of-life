(* val _ = HOL_Interactive.toggle_quietdec(); *)
open HolKernel bossLib boolLib Parse;
open gol_simLib gol_rulesTheory boolSyntax computeLib cv_transLib
     cv_stdTheory gol_sim_cvTheory gol_in_gol_circuit2Theory
     gol_gatesTheory pairSyntax listSyntax gol_simSyntax intLib;

val _ = new_theory "gol_in_gol_circuit";

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
type teleport = (int*int)*(int*int)*dir*rvalue*rvalue

fun wpos ((x,y),(a,b)) = (2*x+a, 2*y+b)
fun dirToXY d = case d of E => (1,0) | S => (0,1) | W => (~1,0) | N => (0,~1)

type 'a log = {
  newIn: 'a * (int * int) * (int * value) vector -> unit,
  newGate: 'a * (int * int) -> unit,
  gateKey: gate * int * loaded_gate -> 'a,
  teleport: (int * int) * (int * int) * rvalue * rvalue -> unit
}

fun build d (gates:gates) period pulse (ins: io_port list, teleport: teleport list)
    (log:'a log) = let
  val gateData = ref (Redblackmap.mkDict String.compare)
  fun getGateData (gate, i) = let
    val key = List.nth (#stems gate, i)
    in
      (key, case Redblackmap.peek (!gateData, key) of
        SOME v => v
      | NONE => let
        val res as {inputs, outputs, ...} = gol_simLib.rotate i (load gate)
        val value = (#gateKey log (gate, i, res),
          case (#stems gate, (inputs, outputs)) of
            ("cross_es_es" :: _,
              ([(a1,a2,Var(_,a3)),(b1,b2,Var(_,b3))],
              [(o1,o2,Var(_,o3)),(p1,p2,Var(_,p3))])) =>
              [([(a1,a2,Var(0,a3))],[(o1,o2,Var(0,o3))]),
              ([(b1,b2,Var(0,b3))],[(p1,p2,Var(0,p3))])]
          | (_, v) => [v])
        in gateData := Redblackmap.insert (!gateData, key, value); value end)
    end
  datatype target = Gate of (int * int) * int | Teleport of (int * int) * rvalue * rvalue
  val wireIn = ref $ foldl
    (fn ((win, wout, d, vin, vout), map) =>
      Redblackmap.insert (map, wpos (win, dirToXY d),
        Teleport (wpos (wout, dirToXY d), vin, vout)))
    (Redblackmap.mkDict int2cmp) teleport
  val gates = ref (foldl
    (fn ((p, gate), map) => let
      val (g, (a, ls)) = getGateData gate
      in #2 $ foldl
        (fn (data, (i, map)) => (
          C app (#1 data) (fn (x, _, _) =>
            wireIn := Redblackmap.insert (!wireIn,
              wpos (p, x), Gate (p, i)));
          (i+1, Redblackmap.insert (map, (p, i), (ref false, a, data)))))
        (0, map) ls end)
    (Redblackmap.mkDict int3cmp) gates)
  val queue = ref []
  val wires = ref (Redblackmap.mkDict int2cmp)
  fun isMissingWire p port = not (Redblackmap.inDomain (!wires, wpos (p, #1 port)))
  fun runGate (missing, (p,i), g, ins, outs) deep = let
    (* val _ = TextIO.output (file, "run gate " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n") *)
    val ins = Vector.fromList $ C map ins (fn
        (x, _, Var (_, delay)) => (delay, Redblackmap.find (!wires, wpos (p, x)))
      | _ => raise Match)
    val _ = if deep then #newGate log (g, p) else #newIn log (g, p, ins)
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
      app (fn (x, d, bv) =>
        processWire (wpos (p, x), evalExp bv) (if deep then 2 else 0)) outs
    end
  and processQueue (missing, (p,i), r, g, ins, outs) depth =
    if !r then true else
    if depth = 0 then (queue := (missing, (p,i), r, g, ins, outs) :: !queue; false) else
    case filter (isMissingWire p) missing of
      [] => (r := true; runGate (missing, (p,i), g, ins, outs) (depth > 1); true)
    | missing => (queue := (missing, (p,i), r, g, ins, outs) :: !queue; false)
  and processWire (w, value) depth =
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
      val _ = wires := Redblackmap.insert (!wires, w, value)
      in
        case tgt of
          Gate p => let
          val (r, g, (ins, outs)) = Redblackmap.find (!gates, p)
          in (processQueue (ins, p, r, g, ins, outs) depth; ()) end
        | Teleport (wout, vin, vout) => let
          val (d, vin') = case value of
              Regular v => v
            | Exact (d, ThisCell) => (d, Cell (0, 0))
            | _ => raise Fail "bad signal on teleport"
          val _ = if vin = vin' then () else
            (PolyML.print ("output mismatch", w, value, vin'); ())
          val _ = #teleport log (w, wout, vin, vout)
          in processWire (wout, Regular (d, vout)) depth end
      end
  val _ = app (fn (w,d,v) => processWire (wpos (w, dirToXY d), v) 1) ins
  fun loop () = case !queue of
    [] => ()
  | q =>
    if foldl (fn (x, r) => processQueue x 2 orelse r) (queue := []; false) q then
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

local

val Cell_tm  = prim_mk_const {Name = "Cell",  Thy = "gol_in_gol_circuit2"}
val RAnd_tm  = prim_mk_const {Name = "RAnd",  Thy = "gol_in_gol_circuit2"}
val ROr_tm   = prim_mk_const {Name = "ROr",   Thy = "gol_in_gol_circuit2"}
val RNot_tm  = prim_mk_const {Name = "RNot",  Thy = "gol_in_gol_circuit2"}
val RXor_tm  = prim_mk_const {Name = "RXor",  Thy = "gol_in_gol_circuit2"}

val Clock_tm    = prim_mk_const {Name = "Clock",    Thy = "gol_in_gol_circuit2"}
val NotClock_tm = prim_mk_const {Name = "NotClock", Thy = "gol_in_gol_circuit2"}
val ThisCell_tm = prim_mk_const {Name = "ThisCell", Thy = "gol_in_gol_circuit2"}
val NextCell_tm = prim_mk_const {Name = "NextCell", Thy = "gol_in_gol_circuit2"}
val ThisCellUntilClock_tm =
  prim_mk_const {Name = "ThisCellUntilClock", Thy = "gol_in_gol_circuit2"}

val Reg_tm   = prim_mk_const {Name = "Reg",   Thy = "gol_in_gol_circuit2"}
val Exact_tm = prim_mk_const {Name = "Exact", Thy = "gol_in_gol_circuit2"}

fun ERR x = mk_HOL_ERR "gol_in_gol_circuitScript" x ""

in

fun tr_rvalue (Cell p)  = mk_binop Cell_tm $ pair_map (intSyntax.term_of_int o Arbint.fromInt) p
  | tr_rvalue (RNot v)  = mk_monop RNot_tm $ tr_rvalue v
  | tr_rvalue (RAnd vs) = mk_binop RAnd_tm $ pair_map tr_rvalue vs
  | tr_rvalue (ROr vs)  = mk_binop ROr_tm $ pair_map tr_rvalue vs
  | tr_rvalue (RXor vs) = mk_binop ROr_tm $ pair_map tr_rvalue vs

fun tr_evalue Clock = Clock_tm
  | tr_evalue NotClock = NotClock_tm
  | tr_evalue ThisCell = ThisCell_tm
  | tr_evalue NextCell = NextCell_tm
  | tr_evalue (ThisCellUntilClock n) = mk_monop ThisCellUntilClock_tm (numSyntax.term_of_int n)

fun tr_value (Regular (n, v)) = mk_binop Reg_tm (numSyntax.term_of_int n, tr_rvalue v)
  | tr_value (Exact (n, v)) = mk_binop Exact_tm (numSyntax.term_of_int n, tr_evalue v)

end

(* val thm = ref floodfill_start *)
fun go () = let
  val _ = PolyML.print_depth 6
  fun f ((x,y), dir, (a,b)) = let
    val (c,d) = dirToXY dir
    in ((x+CSIZE*c,y+CSIZE*d), (x,y), dir, Cell (a+c,b+d), Cell (a,b)) end
  val phase = 0
  val period = 586
  val pulse = 18
  val teleports = map f [
    ((~1, 1), E, (~1, 0)), ((~1, 2), E, (~1, ~1)),
    ((19, ~1), S, (0, ~1)), ((18, ~1), S, (1, ~1)),
    ((21, 19), W, (1, 0)), ((21, 18), W, (1, 1)),
    ((1, 21), N, (0, 1)), ((2, 21), N, (~1, 1))];
  val asrt = [
    ((16, 0), E, Exact (phase, Clock)),
    ((11, 4), E, Exact (0, ThisCell))];
  fun gateKey _ = ()
  fun newGate _ = ()
  fun newIn _ = ()
  fun teleport _ = ()
  datatype gate_kind = Regular of thm | Crossover of thm list
  fun gateKey ((gate, i, lgate): gate * int * loaded_gate) = let
    val g = List.nth (#stems gate, i)
    val g0 = List.nth (#stems gate, 0)
    val genth = g0 ^ "_gate_gen"
    val thm = fetch "gol_gates" (g ^ "_thm")
    val res = if g0 = "cross_es_es" then let
      val thm1 = MATCH_MP blist_simulation_ok_imp_crossover thm
      val thm2 = MATCH_MP crossover_symm thm1
      in Crossover [save_thm (genth, thm1), save_thm (genth^"_rev", thm2)] end
    else let
      val (ins, outs) = apfst rand $ dest_comb $ rator $ concl thm
      val (ins', outs') =
        pair_map (map (apsnd dest_pair o dest_pair) o fst o dest_list) (ins, outs)
      val vars = List.take ([``a:value``, ``b:value``], length ins')
      val env = map2 (fn (_,(_,d)) => fn a => mk_pair (snd (dest_var d), a)) ins' vars
      val env = case env of
          [a] => (a, a)
        | [a, b] => (a, b)
        | _ => raise Match
      val thm = SPEC (mk_pair env) (MATCH_MP blist_simulation_ok_imp_gate thm)
      val thm = INST [``init':bool list list`` |-> ``[]:bool list list``] thm (* FIXME *)
      val thm = CONV_RULE (RATOR_CONV (BINOP_CONV (EVAL THENC SCONV []))) thm
      val thm = case g0 of
          "half_adder_ee_ee" => MATCH_MP half_adder_weaken thm
        | "half_adder_ee_es" => MATCH_MP half_adder_weaken thm
        | _ => thm
      in Regular (save_thm (genth, GENL vars thm)) end
    in PolyML.print (genth, res) end
  val thm = ref floodfill_start
  fun newIn ((s, g), (x', y'), ins) = let
    val _ = PolyML.print (s, g, (x', y'), ins, thm)
    val gth = case g of Regular g => g | _ => raise Match
    val gth = SPECL (Vector.foldr (fn ((_, v), r) => tr_value v :: r) [] ins) gth
    val thm' = MATCH_MP floodfill_add_ins (CONJ (!thm) gth)
    val (x, y) = pair_map (intSyntax.term_of_int o Arbint.fromInt) (2*x', 2*y')
    val (x', y') = pair_map numSyntax.term_of_int (x', y')
    val thm' = SPECL [x, y, x', y'] thm'
    val thm' = SRULE [] $ MATCH_MP thm' $ EQT_ELIM $ EVAL $ lhand $ concl thm'
    in thm := PolyML.print thm' end
  (* val file = TextIO.openOut "log.txt"
  fun newGate ((false, g), p) =
      TextIO.output (file, "newGate " ^ g ^ " " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n")
    | newGate ((true, g), p) =
      TextIO.output (file, "cross " ^ g ^ " " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n")
  fun newIn ((_, g), p, ins) =
    (PolyML.print ("newIn", g, p, ins);
    TextIO.output (file, "newIn " ^ g ^ " " ^ Int.toString (#1 p)^"," ^ Int.toString (#2 p)^"\n"))
  fun teleport (win, wout, vin, vout) =
    TextIO.output (file, "teleport " ^ Int.toString (#1 win)^"," ^ Int.toString (#2 win)^
      "->" ^ Int.toString (#1 wout)^"," ^ Int.toString (#2 wout)^"\n") *)
  val _ = build diag (recognize diag) period pulse (asrt, teleports)
    {gateKey = gateKey, newGate = newGate, newIn = newIn, teleport = teleport}
  (* val _ = TextIO.closeOut file *)
  in !thm end;

Theorem floodfill_result = go ();
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
