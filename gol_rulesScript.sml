(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open HolKernel bossLib boolLib Parse;
open integerTheory;

val _ = new_theory "gol_rules";

(*---------------------------------------------------------------*
    Definition of the semantics of Conway's Game of Life (GOL)
 *---------------------------------------------------------------*)

(* There is an unbounded 2D plane of cells *)
Type state[pp] = “:(int # int) set”;

Definition b2n_def[simp]:
  b2n T = 1n ∧ b2n F = 0
End

(* Number of live neighbours to a cell at i, j *)
Definition live_adj_def:
  live_adj (s:state) i j =
    b2n (s (i-1, j-1)) + b2n (s (i, j-1)) + b2n (s (i+1, j-1)) +
    b2n (s (i-1, j+0)) +                    b2n (s (i+1, j+0)) +
    b2n (s (i-1, j+1)) + b2n (s (i, j+1)) + b2n (s (i+1, j+1))
End

(* For each tick, the game takes a simultaneous step forward in time *)
Definition step_def:
  step (s:state) (i,j) ⇔
    if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                 else live_adj s i j = 3
End

(*---------------------------------------------------------------*
    Define what ist means to simulate GOL in GOL.

        s0 --step---> s1 --step---> ... --step---> sN
         |             ∧             ∧              ∧
         | encode      |             |              | extract
         ∨             |             |              |
        t0 --steps--> s1 --steps--> ... --steps--> tN

    Here --steps--> is a fixed number of --step---> transitions.
 *---------------------------------------------------------------*)

Definition gol_in_gol_def:
  gol_in_gol encode step_count extract ⇔
    ∀ n s0 sN t0 tN .
       t0 = encode s0 ∧
       tN = FUNPOW step (n * step_count) t0 ∧
       sN = FUNPOW step n s0 ⇒
       sN = extract tN
End

val _ = export_theory();
