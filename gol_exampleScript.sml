open HolKernel bossLib gol_rulesTheory;

val _ = new_theory "gol_example";

(* --- examples --- *)

Definition set_env_def:
  set_env a b (A,n:num) = (a n):bool ∧
  set_env a b (B,n:num) = (b n):bool
End

Theorem wire_e_e_sim[local]: (* fake *)
  simulation_ok 1 1 [((-1,0),E,Var A 5)] [((1,0),E,Var A 0)] [ (* ... *) ]
Proof
  cheat
QED

Theorem wire_e_e_raw =
  MATCH_MP simulation_ok_IMP_circuit wire_e_e_sim
  |> Q.SPEC ‘set_env a b’
  |> SRULE [eval_io_def,EVAL “make_area 1 1”, set_env_def, SF ETA_ss];

val _ = export_theory();
