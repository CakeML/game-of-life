(*
  Defines the classic GOL glider:
  https://www.nicolasloizeau.com/gol-computer#h.p_M4NVojd5Vy1D
*)
open preamble gol_rulesTheory gol_listTheory gol_transTheory
     integerTheory sortingTheory;

val _ = new_theory "gol_glider";

(* a glider with its nose one step from 0,0 *)
Definition glider_def:
  glider = build (-3) (-3) [ " X " ;
                             "  X" ;
                             "XXX" ]
End

Definition glider1_def:
  glider1 = next glider
End

Definition glider2_def:
  glider2 = next glider1
End

Definition glider3_def:
  glider3 = next glider2
End

Theorem glider0 = EVAL “glider”;
Theorem glider1 = EVAL “glider1”;
Theorem glider2 = EVAL “glider2”;
Theorem glider3 = EVAL “glider3”;

Theorem next_glider3_glider:
  move (-1) (-1) (next glider3) = glider
Proof
  EVAL_TAC
QED

val _ = export_theory();
