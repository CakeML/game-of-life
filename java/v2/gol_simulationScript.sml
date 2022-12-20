(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open preamble gol_rulesTheory gol_simTheory;

val _ = new_theory "gol_simulation";

(* important definitions *)

Definition to_state_def:
  to_state xs = { p | MEM (p,T) xs } : gol_rules$state
End

Definition gol_simulation_def:
  (gol_simulation [] ⇔ T) ∧
  (gol_simulation [x] ⇔ T) ∧
  (gol_simulation (x::y::ys) ⇔
     step (to_state x) = to_state y ∧
     gol_simulation (y::ys))
End

(* minor definitions *)

Definition sort_def:
  sort xs = QSORT (λ((i:int,j:int),_) ((i',j'),_). i < i' ∨ (i = i' ∧ j < j')) xs
End

Definition state_lookup_def:
  state_lookup p xs =
    case ALOOKUP xs p of
    | SOME b => b
    | NONE => F
End

Definition check_pos_def:
  check_pos xs ys (i:int,j:int) ⇔
    state_lookup (i,j) ys =
    gol (state_lookup (i-1,j-1) xs) (state_lookup (i,j-1) xs) (state_lookup (i+1,j-1) xs)
        (state_lookup (i-1,j  ) xs) (state_lookup (i,j  ) xs) (state_lookup (i+1,j  ) xs)
        (state_lookup (i-1,j+1) xs) (state_lookup (i,j+1) xs) (state_lookup (i+1,j+1) xs)
End

Theorem IMP_step_to_state:
  (let xs = sort x in
   let ys = sort y in
   let xs' = MAP FST xs in
   let ys' = MAP FST ys in
   let ps' = influence_of xs' in
     ALL_DISTINCT xs' ∧
     ALL_DISTINCT ys' ∧
     EVERY (λy. MEM y ps') ys' ∧
     EVERY (check_pos xs ys) ps')
  ⇒
  step (to_state x) = to_state y
Proof
  cheat
QED

val _ = export_theory();
