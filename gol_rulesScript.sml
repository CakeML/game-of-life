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

Definition adj_def:
  adj i j = {(i-1,j-1); (i,j-1); (i+1,j-1);
              (i-1,j) ;           (i+1,j) ;
             (i-1,j+1); (i,j+1); (i+1,j+1)}
End

Definition live_adj_def:
  live_adj s i j = CARD (s ∩ adj i j)
End

(* For each tick, the game takes a simultaneous step forward in time *)
Definition step_def:
  step (s:state) = { (i,j) | if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                                          else live_adj s i j = 3 }
End

Theorem IN_step:
  (i,j) ∈ step s ⇔ if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                                else live_adj s i j = 3
Proof
  fs [step_def]
QED

(*---------------------------------------------------------------*
    Define what it means to simulate GOL in GOL.

        s0 --step---> s1 --step---> ... --step---> sN
         |             ∧             ∧              ∧
         | encode      |             |              | extract
         ∨             |             |              |
        t0 --steps--> s1 --steps--> ... --steps--> tN

    Here --steps--> is a fixed number of --step---> transitions.
 *---------------------------------------------------------------*)

Definition gol_in_gol_def:
  gol_in_gol encode step_count extract ⇔
    ∀ n s0 s1 t0 t1 .
       t0 = encode s0 ∧
       t1 = FUNPOW step (n * step_count) t0 ∧
       s1 = FUNPOW step n s0 ⇒
       s1 = extract t1
End

val _ = export_theory();
