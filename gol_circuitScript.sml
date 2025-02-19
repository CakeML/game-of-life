(* val _ = HOL_Interactive.toggle_quietdec(); *)
open HolKernel bossLib gol_simLib gol_rulesTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory gol_sim_cvTheory;
(* val _ = HOL_Interactive.toggle_quietdec(); *)

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

datatype small_gate = Node | AndG | OrG | NotG
datatype large_gate = HalfAddG | PreLatchG | LatchG

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
  | "A " => Small AndG
  | "O " => Small OrG
  | "N " => Small NotG
  | "H " => Large HalfAddG
  | "P " => Large PreLatchG
  | "L " => Large LatchG
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
  | Small AndG => "A "
  | Small OrG => "O "
  | Small NotG => "N "
  | Large HalfAddG => "H "
  | Large PreLatchG => "P "
  | Large LatchG => "L "

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
      (turn_e_s, (Wire E, Empty, Empty, Wire S)),
      (turn_e_n, (Wire E, Wire N, Empty, Empty)),
      (fork_e_es, (Wire E, Empty, Wire E, Wire S)),
      (fork_e_en, (Wire E, Wire N, Wire E, Empty)),
      (cross_es_es, (Wire E, Wire S, Wire E, Wire S))]
  | NotG => [(not_e_e, (Wire E, Empty, Wire E, Empty))]
  | AndG => [
      (and_en_e, (Wire E, Empty, Wire E, Wire N)),
      (and_es_e, (Wire E, Wire S, Wire E, Empty)),
      (and_ew_n, (Wire E, Wire N, Wire W, Empty))]
  | OrG => [(or_en_e, (Wire E, Empty, Wire E, Wire N))]

fun rotate_sigils (a,b,c,d) =
  (rotate_sigil d, rotate_sigil a, rotate_sigil b, rotate_sigil c)

fun rotate_sigilss (a,b,c,d) =
  (rotate_sigils d, rotate_sigils a, rotate_sigils b, rotate_sigils c)

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

fun recognize d = let
  val gates = ref []
  val _ = for_loop 0 CSIZE (fn y =>
    for_loop 0 CSIZE (fn x => let
      fun push (x, y) (gate, i) = gates := ((x, y), List.nth (#stems gate, i)) :: !gates
      val r = neighbors d (x, y)
      in
        (case r of
          (Empty, (Empty, Empty, Empty, Empty)) => ()
        | (Small n, nei) => push (x, y) (match_with rotate_sigils (smallNodePattern n) nei)
        | (Large n, nei) =>
          if #1 (neighbors d (x-1, y)) = Large n orelse
             #1 (neighbors d (x, y-1)) = Large n then () else
          (case n of
            HalfAddG => push (x, y) $ match_with rotate_sigilss
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
              (nei, #2 (neighbors d (x+1, y)), #2 (neighbors d (x+1, y+1)), #2 (neighbors d (x, y+1)))
          | PreLatchG => ()
          | LatchG => ())
        | _ => (PolyML.print ((x, y), r); raise Fail "unknown node type"))
        handle Match => (PolyML.print ((x, y), r); raise Fail "unknown connection pattern")
      end))
  in !gates end

end;

Quote diag = CircuitDiag.parse:
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
         ^   ^                                                               v   v         |
 0   o > o > o > o > o > o > o > o > o > o > o > o > o > o > o > o > o > o > o > o > o   0 |
     ^   ^   ^                       v                                       v   v   v     |
 1 > o > o > o > H - H > o > o > o > o > o > o > o > o > o   o > o > o > o > o > o > o > 1 |
     ^   ^       |   |               v                   v   ^               v   v   v     |
 2 > o > o > o > H - H > o > o > o > o > o > o > o > o > o > o > o > o       o   o > o > 2 |
     ^   ^                           v                   v   ^       v       v   v   v     |
 3   o   o           o > O > A > o > o > o > o           o   o       o       H - H   o   3 |
     ^   ^           ^   ^   ^       v       v           v   ^       v       |   |   v     |
 4   o   o   o > A > o > o > o       o   P - P > L - L > o > o > o   o   o < H - H   o   4 |
     ^   ^   ^   ^   ^   ^           v   |   |   |   |   v       v   v   v       v   v     |
 5   o   o   o   N   o   o           o > P - P   L - L   o > o > o > o > o > o   o   o   5 |
     ^   ^   ^   ^   ^   ^                                       v   v   v   v   v   v     |
 6   o   o < o < o < o < o < o < o < o < o < o < o < o < o < o < o   o   o   H - H   o   6 |
     ^       ^   ^       ^                                   v   v   v   v   |   |   v     |
 7   o   o > o > o > o > o   o < o < o < o < o < o < o < o < o   o   o   o   H - H   o   7 |
     ^   ^   ^   ^                                           v   v   v   v   v   v   v     |
 8   o   o   o   O < o < o   o < o < o < o < o < o < o < o < o   o   o   o > O   o   o   8 |
     ^   ^   ^   ^       ^                                   v   v   v       v   v   v     |
 9   o   o   H - H       o   o < o < o < o < o < o < o < o < o   o   o > o   o   o   o   9 |
     ^   ^   |   |       ^                                   v   v       v   v   v   v     |
10   o   o   H - H       o   o < o < o < o < o < o < o < o < o   o       H - H   o   o   10|
     ^   ^   ^   ^       ^                                   v   v       |   |   v   v     |
11   o   o   o   o < o   o   o < o < o < o < o < o < o < o < o   o       H - H   o   o   11|
     ^   ^   ^       ^   ^                                   v   v       v   v   v   v     |
12   o   o   O < o   o   o   o < o < o < o < o < o < o < o < o   o > o   o   o   o   o   12|
     ^   ^   ^   ^   ^   ^                                   v       v   v   v   v   v     |
13   o   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o < o < o < o < o   o   13|
     ^   |   |   ^   ^   ^                                   v   v   v   v   v       v     |
14   o   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o   o > o > o > o   o   14|
     ^   ^   ^   ^   ^   ^   v                                   v       v   v   v   v     |
15   o   o   o < o < o < o < o < o   o < o < o < o < o < o < o < o < o < o   o   o   o   15|
     ^   ^       ^   ^   ^   v   ^   v                           v           v   v   v     |
16   o   H - H > o   o   o   o   o   o           o < o < o < o < o < o < o < o   o   o   16|
     ^   |   |       ^   ^   v   ^   v           v               v               v   v     |
17   o   H - H       o   o < o < o < O < H - H < o   o < o < o < o < o           o   o   17|
     ^   ^   ^       ^       v   ^       |   |       v           v   ^           v   v     |
18 < o < o   o       o < o < o < o < o < H - H < o < O < H - H < o   H - H < o < o < o < 18|
     ^   ^   ^               v   ^                       |   |       |   |       v   v     |
19 < o < o < o < o < o < o < o   o < o < o < o < o < o < H - H < o < H - H < o < o < o < 19|
     ^   ^   ^                                                               v   v   v     |
20   o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o   20|
         ^   ^                                                               v   v         |
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
End

val _ = CircuitDiag.recognize diag;

val _ = export_theory();
