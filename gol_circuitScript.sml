(* val _ = HOL_Interactive.toggle_quietdec(); *)
open HolKernel bossLib gol_simLib gol_rulesTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory gol_sim_cvTheory;
(* val _ = HOL_Interactive.toggle_quietdec(); *)

val _ = new_theory "gol_circuit";

structure CircuitDiag = struct

type diag = string * string vector

val SIZE = 21 * 2 + 1

fun parse [QUOTE s]: diag = let
    val lines = String.fields (fn x => x = #"\n") s
    val (header, lines) = case lines of _::a::b => (a,b) | _ => raise Bind
    val lines = Vector.fromList (List.take (lines, length lines - 2))
    in (header, lines) end
  | parse _ = raise Bind

fun coord ((_, lines):diag) (x, y) =
  String.substring (Vector.sub (lines, y), 3 + 2 * x, 2)

fun lineHeader line =
  (String.substring (line, 0, 3), String.extract (line, 3 + 2 * SIZE, NONE))

fun rotate (d as (header, lines):diag) = let
  fun rotate s = case s of
      "> " => "v "
    | "v " => "< "
    | "< " => "^ "
    | "^ " => "> "
    | "| " => "- "
    | "- " => "| "
    | s => s
  val lines' = Vector.tabulate (SIZE, fn i => let
    val (left, right) = lineHeader (Vector.sub (lines, i))
    val body = List.tabulate (SIZE, fn j =>
      rotate (coord d (i, SIZE-1-j)))
    in left ^ String.concat body ^ right end)
  in (header, lines') end

fun print' ((header, lines):diag) = (
  print (header^"\n");
  Vector.app (fn s => print (s^"\n")) lines;
  print (header^"\n"));

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
 7   o   o > o > o > o > o   T < o < o < o < o < o < o < o < o   o   o   o   H - H   o   7 |
     ^   ^   ^   ^                                           v   v   v   v   v   v   v     |
 8   o   o   o   O < o < o   T < o < o < o < o < o < o < o < o   o   o   o > O   o   o   8 |
     ^   ^   ^   ^       ^                                   v   v   v       v   v   v     |
 9   o   o   H - H       o   T < o < o < o < o < o < o < o < o   o   o > o   o   o   o   9 |
     ^   ^   ^   |       ^                                   v   v       v   v   v   v     |
10   o   o   H - H       o   T < o < o < o < o < o < o < o < o   o       H - H   o   o   10|
     ^   ^   ^   ^       ^                                   v   v       |   v   v   v     |
11   o   o   o   o < o   o   T < o < o < o < o < o < o < o < o   o       H - H   o   o   11|
     ^   ^   ^       ^   ^                                   v   v       v   v   v   v     |
12   o   o   O < o   o   o   T < o < o < o < o < o < o < o < o   o > o   o   o   o   o   12|
     ^   ^   ^   ^   ^   ^                                   v       v   v   v   v   v     |
13   o   H - H   o   o   o   T < o < o < o < o < o < o < o < o   o < o < o < o < o   o   13|
     ^   |   |   ^   ^   ^                                   v   v   v   v   v       v     |
14   o   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o   o > o > o > o   o   14|
     ^   ^   ^   ^   ^   ^   v                                   v       v   v   v   v     |
15   o   o   o < o < o < o < o < o   o < o < o < o < o < o < o < o < o < o   o   o   o   15|
     ^   ^       ^   ^   ^   v   ^   v                           v           v   v   v     |
16   o   H - H > o   o   o   o   o   o           o < o < o < o < o < o < o < o   o   o   16|
     ^   |   |       ^   ^   v   ^   v           v               v               v   v     |
17   o   H - H       o   o < o < o < O < H - H < o   o < o < o < o < o           o   o   17|
     ^   ^   ^       ^       v   ^       |   |       v           v   ^           v   v     |
18 < o < o   o       o < o < o < o < o < H < H < o < O < H - H < o   H - H < o < o < o < 18|
     ^   ^   ^               v   ^                       |   |       |   |       v   v     |
19 < o < o < o < o < o < o < o   o < o < o < o < o < o < H - H < o < H - H < o < o < o < 19|
     ^   ^   ^                                                               v   v   v     |
20   o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o < o   20|
         ^   ^                                                               v   v         |
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
End

val _ = export_theory();
