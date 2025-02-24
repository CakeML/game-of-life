(* val _ = HOL_Interactive.toggle_quietdec(); *)
open HolKernel bossLib boolLib Parse;
open gol_simTheory;
(* val _ = HOL_Interactive.toggle_quietdec(); *)

val _ = new_theory "gol_sim2";

val _ = export_theory();
