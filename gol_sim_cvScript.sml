open HolKernel bossLib boolLib Parse;
open gol_simTheory computeLib cv_transLib cv_stdTheory;

val _ = new_theory "gol_sim_cv";

Definition member_def:
  member x [] = F ∧
  member x (y::ys) = if x = y then T else member x ys
End

val _ = cv_trans member_def;

Theorem member_thm:
  ∀xs x. MEM x xs = member x xs
Proof
  Induct \\ gvs [member_def]
QED

val pre = cv_auto_trans_pre blist_gol_rows_def;

Theorem blist_gol_rows_pre[cv_pre]:
  ∀xs prev ys. blist_gol_rows_pre xs prev ys
Proof
  Induct_on ‘ys’ \\ gvs [] \\ simp [Once pre]
QED

Theorem blist_simple_checks_eq:
  blist_simple_checks w h ins outs rows
  ⇔
  LENGTH rows = 150 * h + 20 ∧
  EVERY (λrow. blist_length row = 150 * w + 20) rows ∧ h ≠ 0 ∧ w ≠ 0 ∧
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  let
     area = make_area w h
  in
    ALL_DISTINCT area ∧
    EVERY (λ(p,d,r). member (add_pt p (dir_to_xy d)) area ∧
                    ¬member (sub_pt p (dir_to_xy d)) area) ins ∧
    EVERY (λ(p,d,r). member (sub_pt p (dir_to_xy d)) area ∧
                    ¬member (add_pt p (dir_to_xy d)) area) outs
Proof
  gvs [blist_simple_checks_def, member_thm]
QED

val _ = cv_auto_trans blist_simple_checks_eq;
val _ = cv_auto_trans blist_simulation_ok_def;
val _ = cv_auto_trans instantiate_def;

val _ = export_theory();
