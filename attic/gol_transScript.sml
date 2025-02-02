(*
  Defines transformations: move, rotate, mirror
*)
open preamble gol_rulesTheory (* gol_listTheory *);

val _ = new_theory "gol_trans";

(*

(* moves all coordinates in one direction *)
Definition move_def:
  move di dj l = MAP (λ(i,j). (di + i:int, dj + j:int)) l
End

(* rotates the field by 90 degrees anti-clockwise *)
Definition rotate_def:
  rotate l = MAP (λ(i,j). (-j:int,i:int)) l
End

(* mirror against x-axis *)
Definition mirror_def:
  mirror l = MAP (λ(i,j). (-i:int,j:int)) l
End

*)

val _ = export_theory();
