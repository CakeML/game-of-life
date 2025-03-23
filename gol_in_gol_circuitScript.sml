open HolKernel bossLib boolLib Parse;
open gol_simLib gol_rulesTheory boolSyntax computeLib cv_transLib
     cv_stdTheory gol_sim_cvTheory gol_in_gol_circuit2Theory
     gol_gatesTheory pairSyntax listSyntax gol_simSyntax intLib
     sortingTheory listTheory gol_in_gol_paramsLib gol_in_gol_circuitLib;

val _ = new_theory "gol_in_gol_circuit";

Definition union_blist2_def:
  union_blist2 _ NONE Nil ls = ls ∧
  union_blist2 m NONE (Falses n ls1) ls = union_blist2 (m + n) NONE ls1 ls ∧
  union_blist2 m NONE (Cell a ls1) ls = union_blist2 m (SOME a) ls1 ls ∧
  union_blist2 m (SOME a) ls1 Nil = Nil ∧
  union_blist2 m (SOME a) ls1 (Falses n ls) = (
    if m < n then mk_Falses m (Cell a (union_blist2 0 NONE ls1 (Falses (n - (m + 1)) ls)))
    else mk_Falses n (union_blist2 (m - n) (SOME a) ls1 ls)) ∧
  union_blist2 m (SOME a) ls1 (Cell b ls) = (
    if m = 0 then Cell (build_Or a b) (union_blist2 0 NONE ls1 ls)
    else Cell b (union_blist2 (m - 1) (SOME a) ls1 ls))
End

Theorem union_blist_eq:
  (∀m ls1 ls. union_blist m ls1 ls = union_blist2 m NONE ls1 ls) ∧
  (∀m a ls1 ls. union_blist' m a ls1 ls = union_blist2 m (SOME a) ls1 ls)
Proof
  HO_MATCH_MP_TAC union_blist_ind
  \\ simp [union_blist_def, union_blist2_def]
QED

(* val _ = cv_transLib.cv_trans_rec union_blist2_def (
  WF_REL_TAC ‘measure (λ_,_,ls1,ls. cv$cv_size ls1 + cv$cv_size ls)’
  \\ Cases \\ gvs [] \\ rw [] \\ gvs [])
  (fn goal => (set_goal goal; PolyML.print goal; NO_TAC goal))
) *)

val _ = cv_transLib.cv_trans_rec union_blist2_def cheat
val _ = cv_transLib.cv_trans union_blist_eq
val _ = cv_transLib.cv_auto_trans build_mega_cell_def

Theorem floodfill_result = floodfill diag params;

val _ = cv_transLib.cv_auto_trans test_blists_def
val _ = cv_transLib.cv_trans_deep_embedding EVAL $
  definition "main_circuit_def"

Definition build_mega_cells_def:
  build_mega_cells = mega_cell_builder main_circuit
End

Theorem gol_in_gol_thm:
  gol_in_gol build_mega_cells (^periodN * 60) read_mega_cells
Proof
  rewrite_tac [build_mega_cells_def]
  \\ irule floodfill_result_finish \\ simp [floodfill_result]
  \\ CONV_TAC cv_eval
QED

Theorem gol_in_gol_circuit_thm:
  ∀n s.
    FUNPOW step n s =
    read_mega_cells (FUNPOW step (n * ^periodN * 60) (build_mega_cells s))
Proof
  mp_tac gol_in_gol_thm
  \\ rewrite_tac [gol_in_gol_def]
  \\ metis_tac [arithmeticTheory.MULT_ASSOC]
QED

val _ = (max_print_depth := 10); (* avoids blow up in size of Theory.sig file *)
val _ = export_theory();
