open HolKernel bossLib boolLib Parse;
open gol_simLib gol_rulesTheory boolSyntax computeLib cv_transLib
     cv_stdTheory gol_sim_cvTheory gol_in_gol_circuit2Theory
     gol_gatesTheory pairSyntax listSyntax gol_simSyntax intLib
     sortingTheory listTheory gol_in_gol_paramsLib gol_in_gol_circuitLib;

val _ = new_theory "gol_in_gol_circuit";

Theorem floodfill_result = floodfill diag params;

val _ = cv_transLib.cv_auto_trans test_pt_slow_def
val _ = cv_transLib.cv_auto_trans $ definition "main_circuit_def"

Definition build_mega_cells_def:
  build_mega_cells = mega_cell_builder main_circuit
End

Theorem gol_in_gol_thm:
  gol_in_gol build_mega_cells (^periodN * 60) read_mega_cells
Proof
  rewrite_tac [build_mega_cells_def]
  \\ irule floodfill_finish \\ simp [floodfill_result]
  \\ CONV_TAC cv_eval
QED

Theorem gol_in_gol_circuit_thm:
  ∀n s.
    FUNPOW step n s =
    read_mega_cells (FUNPOW step (n * ^periodN * 60) (build_mega_cells s))
Proof
  mp_tac gol_in_gol_thm
  \\ rewrite_tac [gol_in_gol_def]
  \\ metis_tac [arithmeticTheory.MULT_ASSOC]
QED

val _ = export_theory();
