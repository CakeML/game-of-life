open HolKernel bossLib boolLib Parse;
open gol_simLib gol_rulesTheory boolSyntax computeLib cv_transLib
     cv_stdTheory gol_sim_cvTheory gol_in_gol_circuit2Theory
     gol_gatesTheory pairSyntax listSyntax gol_simSyntax intLib
     sortingTheory listTheory gol_diagramLib gol_in_gol_circuitLib;

val _ = new_theory "gol_in_gol_circuit";

Quote diag = gol_diagramLib.parse:
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
         ^   ^                                                               v   v         |
 0   o > o > o > o > o > o > o > o > o > s > s > s > s > s > s > s > o > o > o > o > o   0 |
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
 6   o   o < o < o < o < o < o < o < o < o < o < o < o < o < o < o   o   o   H - H   s   6 |
     ^       ^   ^       ^                                   v   v   v   v   |   |   v     |
 7   o   o > o > o > o > o   o < o < o < o < o < o < o < o < o   o   o   o   H - H   s   7 |
     ^   ^   ^   ^                                           v   v   v   v   v   v   v     |
 8   o   o   o   O < o < o   o < o < o < o < o < o < o < o < o   o   o   o > O   o   s   8 |
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

val params = {
  period = 586,
  pulse = 22,
  asserts = [((6, 0), E, Exact (~77, Clock)), ((11, 4), E, Exact (~15, ThisCell))],
  weaken = [((14, 4), E), ((14, 4), N)]
};

(* val _ = diag_to_svg (recognize diag) NONE "diag.svg"; *)
(* val _ = diag_to_svg_with_wires diag params
  {speed = 25.0, fade = 4, offset = ~4} "propagation.svg"; *)

Theorem floodfill_result = floodfill diag params;

val _ = cv_transLib.cv_auto_trans test_pt_slow_def
val _ = cv_transLib.cv_auto_trans $ definition "main_circuit_def"

val period = ``586:num``

Definition build_mega_cells_def:
  build_mega_cells = mega_cell_builder main_circuit
End

Theorem gol_in_gol_thm:
  gol_in_gol build_mega_cells (^period * 60) read_mega_cells
Proof
  REWRITE_TAC [build_mega_cells_def]
  \\ irule floodfill_finish \\ simp [floodfill_result]
  \\ CONV_TAC cv_eval
QED

val _ = export_theory();
