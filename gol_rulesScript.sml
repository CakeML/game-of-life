(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open preamble;

val _ = new_theory "gol_rules";

(* Each cell is either alive or dead *)
Datatype:
  cell = Live | Dead
End

(* There is an unbounded 2D plane of cells *)
Type state[pp] = “:int -> int -> cell”;

(* Counting Live as 1 *)
Definition c2n_def:
  c2n Live = 1:num ∧
  c2n Dead = 0
End

(* Number of Live neighbours to a cell at i, j *)
Definition live_adj_def:
  live_adj (s:state) i j =
    c2n (s (i-1) (j-1)) + c2n (s (i) (j-1)) + c2n (s (i+1) (j-1)) +
    c2n (s (i-1) (j+0)) +                     c2n (s (i+1) (j+0)) +
    c2n (s (i-1) (j+1)) + c2n (s (i) (j+1)) + c2n (s (i+1) (j+1))
End

(* For each tick, the game takes a simultaneous step forward in time *)
Definition step_def:
  step (s:state) =
    λi j. case s i j of
          | Live => (if live_adj s i j ∈ {2; 3} then Live else Dead)
          | Dead => (if live_adj s i j = 3 then Live else Dead)
End

val _ = export_theory();
