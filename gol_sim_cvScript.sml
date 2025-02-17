open HolKernel bossLib gol_simLib gol_rulesTheory boolLib boolSyntax
     computeLib cv_transLib cv_stdTheory;

val _ = new_theory "gol_sim_cv";

Definition single_check_def:
  single_check (x:int) y d delta =
     case d of
     | N => (x,y - delta)
     | S => (x,y + delta)
     | E => (x + delta,y)
     | W => (x - delta,y)
End

val _ = cv_trans single_check_def;

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

Definition check_io_def:
  check_io area [] (delta:int) = T ∧
  check_io area (((x,y),d,_)::rest) delta =
    (check_io area rest delta ∧
     member (single_check x y d delta) area)
End

val _ = cv_trans check_io_def;

Theorem check_io_thm:
  check_io area ins delta ⇔
  EVERY (λ((x,y),d,r). d = N ⇒ MEM (x,y − delta) area) ins ∧
  EVERY (λ((x,y),d,r). d = S ⇒ MEM (x,y + delta) area) ins ∧
  EVERY (λ((x,y),d,r). d = E ⇒ MEM (x + delta,y) area) ins ∧
  EVERY (λ((x,y),d,r). d = W ⇒ MEM (x − delta,y) area) ins
Proof
  Induct_on ‘ins’ \\ gvs [pairTheory.FORALL_PROD,check_io_def,member_thm]
  \\ gen_tac \\ gen_tac \\ Cases
  \\ gvs [single_check_def] \\ eq_tac \\ rw [] \\ gvs []
QED

Theorem simple_checks_eq:
  simple_checks w h ins outs rows
  ⇔
  rectangle w h rows ∧ h ≠ 0 ∧ w ≠ 0 ∧
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  EVERY (λ((x,y),r).
           (x % 2 = 0 ⇎ y % 2 = 0) ∧ -1 ≤ x ∧ -1 ≤ y ∧ x ≤ 2 * &w − 1 ∧
           y ≤ 2 * &h − 1) (ins ++ outs) ∧
  let
     area = make_area w h
  in
    ALL_DISTINCT area ∧
    check_io area ins 1 ∧
    check_io area outs (-1)
Proof
  gvs [simple_checks_def,check_io_thm, GSYM integerTheory.int_sub]
  \\ gvs [AC CONJ_COMM CONJ_ASSOC]
QED

val _ = cv_auto_trans simple_checks_eq;
val _ = cv_auto_trans simulation_ok_def;

val _ = export_theory();
