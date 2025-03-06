open HolKernel bossLib boolLib Parse;
open gol_simTheory listTheory gol_gatesTheory gol_circuitTheory pred_setTheory
     pairTheory alistTheory arithmeticTheory sortingTheory integerTheory numLib
     dep_rewrite intLib combinTheory;

val _ = new_theory "gol_in_gol_circuit2";

(* val metis_tac = Timeout.apply (Time.fromMilliseconds 2000) o metis_tac *)

fun suff_eqr_tac th: tactic = fn (g as (asl,w)) =>
 (SUFF_TAC(mk_eq(concl th, w))
  >- (disch_then (irule o iffLR) \\ ACCEPT_TAC th))
 g

fun suff_eq_tac th: tactic = fn (g as (asl,w)) =>
 (SUFF_TAC(mk_eq(w, concl th))
  >- (disch_then (irule o iffRL) \\ ACCEPT_TAC th))
 g

fun cong_tac n = ntac n $ FIRST [AP_THM_TAC, AP_TERM_TAC, ABS_TAC, BINOP_TAC, MK_COMB_TAC]

Definition circuit_gen_def:
  circuit_gen area ins outs init ⇔
  ∀ s0. LENGTH s0 = LENGTH ins ⇒ ∃ s1.
  circuit area
    (MAP2 (λv (p,d,_). (p,d,v)) s0 ins)
    (MAP2 (λv (_,p,d,_). (p,d,v)) s1 outs)
    [] init ∧
  LIST_REL (λv (is,p,d,Q).
    (∀ i. MEM i is ⇒ EL i (MAP2 (λv (_,_,P). P v) s0 ins)) ⇒ Q v) s1 outs
End

Datatype:
  rvalue = Cell (int # int) | RNot rvalue
    | RAnd rvalue rvalue | ROr rvalue rvalue | RXor rvalue rvalue;
  evalue = Clock | NotClock | ThisCell | ThisCellClock | ThisCellNotClock;
  value = Reg num rvalue | Exact int evalue | Fail
End

val period = ``586:num``
val pulse = ``22:num``

Definition base_def:
  (base:num) = 0
End

Definition r_eval_def[simp]:
  (r_eval env (Cell p) ⇔ env p) ∧
  (r_eval env (RNot v) ⇔ ¬r_eval env v) ∧
  (r_eval env (RAnd v1 v2) ⇔ r_eval env v1 ∧ r_eval env v2) ∧
  (r_eval env (ROr v1 v2) ⇔ r_eval env v1 ∨ r_eval env v2) ∧
  (r_eval env (RXor v1 v2) ⇔ r_eval env v1 ≠ r_eval env v2)
End

Definition e_clock_def:
  e_clock (n:int) ⇔ n % &^period < &^pulse
End

Definition e_cell_def:
  e_cell env (n:int) ⇔ 0 ≤ n ∧ env (Num n DIV ^period)
End

Definition e_eval_def[simp]:
  e_eval env Clock = e_clock ∧
  e_eval env NotClock = (λn. ¬e_clock n) ∧
  e_eval env ThisCell = e_cell env ∧
  e_eval env ThisCellClock = (λn. e_clock n ∧ e_cell env n) ∧
  e_eval env ThisCellNotClock = (λn. e_cell env n ∧ ¬e_clock n)
End

Definition v_eval'_def[simp]:
  (v_eval' env (Reg d rv) s ⇔
    ∀ n. d ≤ (n + base) MOD ^period ⇒ s n = r_eval (env ((n + base) DIV ^period)) rv) ∧
  (v_eval' env (Exact d ev) s ⇔ s = (λn. e_eval (λi. env i (0, 0)) ev (&(n + base) - d))) ∧
  (v_eval' env Fail s ⇔ T)
End

Definition v_eval_def:
  v_eval env v s ⇔
    ∀x. v_eval' (λi p. env i (add_pt x p)) v (s x)
End

Theorem v_eval_fail[simp]:
  v_eval env Fail s
Proof
  simp [v_eval_def]
QED

Definition v_delay_def[simp]:
  v_delay n (Reg i v) = Reg (n + i) v ∧
  v_delay n (Exact i v) = Exact (&n + i) v ∧
  v_delay n Fail = Fail
End

Theorem v_delay_0[simp]:
  v_delay 0 v = v
Proof
  Cases_on `v` \\ rw []
QED

Definition v_teleport_def:
  v_teleport p (Reg i (Cell a)) = Reg i (Cell (add_pt a p)) ∧
  v_teleport _ _ = Fail
End

Definition nextCell_def[compute]:
  nextCell = let
    e1 = RXor (Cell (0, 1)) (Cell (~1, 1));
    e2 = RXor (Cell (1, 0)) (Cell (1, 1));
    e3 = RXor (Cell (0, ~1)) (Cell (1, ~1));
    e4 = RXor (Cell (~1, 0)) (Cell (~1, ~1));
    e5 = RAnd (Cell (0, 1)) (Cell (~1, 1));
    e6 = RAnd (Cell (0, ~1)) (Cell (1, ~1));
    e7 = RAnd (Cell (~1, 0)) (Cell (~1, ~1));
    e8 = RAnd (Cell (1, 0)) (Cell (1, 1));
    e9 = RXor e2 (RXor e3 e4);
    e10 = ROr (RAnd e2 (RXor e3 e4)) e8;
    e11 = ROr (RAnd e1 e9) e5;
    e12 = ROr (RAnd e3 e4) e6;
    e13 = RXor e10 (RXor e12 e7);
  in
    RAnd (ROr (Cell (0, 0)) (RXor e1 e9))
      (RAnd (RXor e11 e13) (RNot (ROr (RAnd e11 e13)
        (ROr (RAnd e10 (RXor e12 e7)) (RAnd e12 e7)))))
End

Definition v_and_def[simp,compute]:
  (v_and (Reg d1 rv1) (Reg d2 rv2) = Reg (MAX d1 d2) (RAnd rv1 rv2)) ∧
  (v_and (Exact d1 ThisCell) (Exact d2 NotClock) =
    if d2 ≤ d1 ∧ d1 ≤ d2 + &^pulse then
      Exact d2 ThisCellNotClock
    else Fail) ∧
  (v_and (Exact d1 Clock) (Reg d2 v2) =
    if v2 = nextCell ∧ &d2 ≤ d1 + &^period ∧ d1 ≤ -&^pulse then
      Exact d1 ThisCellClock
    else Fail) ∧
  (v_and _ _ = Fail)
End

Theorem v_and_fail[simp]:
  v_and v Fail = Fail
Proof
  Cases_on `v` \\ simp [] \\ Cases_on `e` \\ simp [] \\ rpt CASE_TAC \\ simp []
QED

Definition v_or_def[simp]:
  (v_or (Reg d1 rv1) (Reg d2 rv2) = Reg (MAX d1 d2) (ROr rv1 rv2)) ∧
  (v_or (Exact d1 ThisCellClock) (Exact d2 ThisCellNotClock) =
    if d1 = d2 then Exact d1 ThisCell else Fail) ∧
  (v_or _ _ = Fail)
End

Theorem v_or_fail[simp]:
  v_or v Fail = Fail
Proof
  Cases_on `v` \\ simp [] \\ Cases_on `e` \\ simp [] \\ rpt CASE_TAC \\ simp []
QED

Definition v_not_def[simp]:
  v_not (Exact d1 Clock) = Exact d1 NotClock ∧
  v_not (Reg d1 v1) = Reg d1 (RNot v1) ∧
  v_not _ = Fail
End

Definition v_xor_def[simp]:
  v_xor (Reg d1 v1) (Reg d2 v2) = Reg (MAX d1 d2) (RXor v1 v2) ∧
  v_xor _ _ = Fail
End

Theorem v_xor_fail[simp]:
  v_or v Fail = Fail
Proof
  Cases_on `v` \\ simp [] \\ rpt CASE_TAC \\ simp []
QED

Definition v_subset_def:
  v_subset v1 v2 ⇔ ∀env s. v_eval env v1 s ⇒ v_eval env v2 s
End
val _ = set_fixity "⊑" (Infix(NONASSOC, 450))
Overload "⊑" = “v_subset”;

Theorem v_subset_refl[simp]:
  v ⊑ v
Proof
  simp [v_subset_def]
QED

Theorem v_subset_fail[simp]:
  v ⊑ Fail
Proof
  simp [v_subset_def]
QED

Theorem v_subset_trans:
  v1 ⊑ v2 ∧ v2 ⊑ v3 ⇒ v1 ⊑ v3
Proof
  simp [v_subset_def]
QED

Theorem Reg_mono:
  na ≤ nb ∧ (∀env. r_eval env va ⇔ r_eval env vb) ⇒ Reg na va ⊑ Reg nb vb
Proof
  simp [v_subset_def, v_eval_def] \\ metis_tac [LE_TRANS]
QED

Definition is_exact_def:
  is_exact v ⇔ (∀env s s'. v_eval env v s ∧ v_eval env v s' ⇒ s = s') ∧ (∀v'. v' ⊑ v ⇒ v ⊑ v')
End

Theorem is_exact_unique:
  is_exact v ∧ v_eval env v s ∧ v_eval env v t ⇒ s = t
Proof
  metis_tac [is_exact_def]
QED

Theorem is_exact_minimal:
  is_exact v ∧ v' ⊑ v ⇒ v ⊑ v'
Proof
  metis_tac [is_exact_def]
QED

Theorem is_exact_exact[simp]:
  is_exact (Exact i v)
Proof
  simp [FUN_EQ_THM, is_exact_def, FORALL_PROD] \\ rpt strip_tac
  >- fs [v_eval_def, v_eval'_def]
  \\ fs [v_subset_def, v_eval_def] \\ fs [GSYM FORALL_PROD, GSYM FUN_EQ_THM] \\ rw []
  \\ `∀x. ∃s'. v_eval' (λi a. env i (add_pt x a)) v' s'` by (
    pop_assum kall_tac \\ Cases_on `v'` \\ rw [v_eval'_def]
    \\ qexists_tac `λn'. r_eval (λa. env ((n' + base) DIV 586) (add_pt x a)) r`
    \\ simp [])
  \\ fs [SKOLEM_THM]
  \\ last_x_assum (qspecl_then [`env`,`f`] mp_tac) \\ rw [] \\ gvs []
QED

Theorem is_exact_mono:
  v ⊑ v' ∧ is_exact v' ⇒ is_exact v
Proof
  simp [is_exact_def, v_subset_def] \\ metis_tac []
QED

Definition env_wf_def:
  env_wf (env:num->state) ⇔
    ∀t x. env (t + 1) x = r_eval (env t ∘ add_pt x) nextCell
End

val tile = ``21:num``;
val tile2 = ``42:num``;

Definition mul_pt_def[simp]:
  mul_pt (n:int) (a, b) ⇔ (n * a, n * b)
End

Definition mk_pt_def[compute]:
  mk_pt a z ⇔ add_pt a (mul_pt (&^tile2) z)
End

Theorem mk_pt_0[simp]:
  mk_pt p (0,0) = p
Proof
  Cases_on `p` \\ simp [mk_pt_def]
QED

Definition mk_dpt_def[compute]:
  mk_dpt (a, d:dir) z ⇔ (mk_pt a z, d)
End

Theorem mk_dpt_0[simp]:
  mk_dpt p (0,0) = p
Proof
  Cases_on `p` \\ simp [mk_dpt_def]
QED

Definition span_def:
  span s = {mk_dpt p z | z,p | p ∈ s}
End

Theorem span_mono[simp]:
  s ⊆ t ⇒ span s ⊆ span t
Proof
  simp [span_def, SUBSET_DEF] \\ metis_tac []
QED

Theorem span_subset[simp]:
  s ⊆ span s
Proof
  simp [span_def, SUBSET_DEF] \\ metis_tac [mk_dpt_0]
QED

Theorem mem_span_self[simp] = ONCE_REWRITE_RULE [SUBSET_DEF] span_subset;

Theorem mk_dpt_in_span[simp]:
  mk_dpt p z ∈ span s ⇔ p ∈ span s
Proof
  PairCases_on `p` \\ PairCases_on `z`
  \\ simp [span_def, EXISTS_PROD, mk_dpt_def, mk_pt_def] \\ eq_tac \\ strip_tac
  \\ first_assum $ irule_at (Pos last) \\ ARITH_TAC
QED

Theorem span_subset_iff:
  span s ⊆ span t ⇔ s ⊆ span t
Proof
  eq_tac >- metis_tac [SUBSET_TRANS, span_subset]
  \\ CONV_TAC (PATH_CONV "rlr" (SCONV [span_def]))
  \\ simp [SUBSET_DEF, PULL_EXISTS]
QED

Definition assign_ext_def:
  assign_ext (s, dom) (s', dom') ⇔
    span dom ⊆ span dom' ∧ (∀x. x ∈ span dom ⇒ s x = s' x)
End

Definition assign_sat_def:
  assign_sat env (s, dom) (p, v) ⇔
    p ∈ span dom ∧ v_eval env v (s ∘ mk_dpt p)
End

Theorem assign_sat_mono:
  v ⊑ v' ∧ assign_sat env s (p, v) ⇒ assign_sat env s (p, v')
Proof
  Cases_on `s` \\ simp [v_subset_def, assign_sat_def]
QED

Definition assign_tr_def:
  assign_tr x (s, dom) =
    ((λ(a,d). s (sub_pt a x, d)), λ(a,d). dom (sub_pt a x, d))
End

Definition vb_eval_def[simp,compute]:
  (vb_eval ((da, a), _) (Var A d) = v_delay (da - d) a) ∧
  (vb_eval (_, (db, b)) (Var B d) = v_delay (db - d) b) ∧
  (vb_eval env (Not x)   = v_not (vb_eval env x)) ∧
  (vb_eval env (And x y) = v_and (vb_eval env x) (vb_eval env y)) ∧
  (vb_eval env (Or x y)  = v_or  (vb_eval env x) (vb_eval env y)) ∧
  (vb_eval _ _ = Fail)
End

(*
Definition to_env'_def:
  to_env' (f, t) (a, da) p n = ARB
    (* (* to_env' (f,t) (Exact n' e,da) (x,y) n ⇔
        e_eval (λi. f i (x,y)) (n − (da + n') - t) e *)
  (v_eval' ((λi (a,b). f i (x + a,y + b)), t) (v_delay da (Exact n' e)) s ⇔
    λn. e_eval (λi. f i (x, y)) (n - (da + n') - t) e) ∧ *)
End

Definition to_env_def:
  to_env env (ea, eb) p (A, n) = to_env' env ea p n ∧
  to_env env (ea, eb) p (B, n) = to_env' env eb p n
End

Theorem v_eval'_v_delay:
  n ≤ da ⇒
  v_eval' ((λi (a,b). f i (x + a,y + b)),t) (v_delay (da − n) a)
    (λn'. to_env' (f, t) (a,da) (x,y) (n + n'))
Proof
  Cases_on `a` \\ rw [v_delay_def]

QED

Theorem v_eval_vb_eval:
  v_eval env (vb_eval ee v) (λp n. eval (age n (to_env env ee p)) v)
Proof
  Cases_on `env` \\ PairCases_on `ee`
  \\ rw [v_eval_def] \\ Induct_on `v` \\ rw []
  >- (
    Cases_on `v` \\ rw [to_env_def, vb_eval_def]
    THENL [Cases_on `ee0`, Cases_on `ee2`] \\ rw []

  )
QED *)

Definition classify_clock_def[compute]:
  (classify_clock da T d =
    if &da + d + &^pulse ≤ &^period ∧ -&^period ≤ d then
      if 0 ≤ d ∨ &da + d + &^pulse ≤ 0 then SOME Zeros else
        SOME (Pulse
          (if 0 ≤ &da + d then Num (&da + d) else 0)
          (MIN da (Num (&da + d + &^pulse))))
    else NONE) ∧
  (classify_clock da F d =
    if &da + d ≤ 0 ∧ -&^period ≤ d then
      SOME (Pulse
        (if 0 ≤ &da + d + &^pulse then Num (&da + d + &^pulse) else 0)
        (MIN da (Num (&da + d + &^period))))
    else NONE)
End

Definition classify_this_def[compute]:
  classify_this da d =
    if 0 < d then SOME Zeros else
    if 0 < d + &^period then
      SOME (Pulse (if 0 ≤ &da + d then Num (&da + d) else 0) da)
    else NONE
End

Definition classify_def[compute]:
  classify _ (Reg _ _) = SOME (Zeros, Zeros) ∧
  classify da (Exact d Clock) =
    OPTION_MAP (λx. (x, x)) (classify_clock da T (d - &base)) ∧
  classify da (Exact d NotClock) =
    OPTION_MAP (λx. (x, x)) (classify_clock da F (d - &base)) ∧
  classify da (Exact d ThisCell) =
    OPTION_MAP (λx. (Zeros, x)) (classify_this da (d - &base)) ∧
  classify da (Exact d ThisCellClock) =
    OPTION_MAP (λx. (Zeros, x)) (classify_clock da T (d - &base)) ∧
  classify da (Exact d ThisCellNotClock) =
    OPTION_MAP (λx. (Zeros, x)) (classify_clock da F (d - &base)) ∧
  classify _ Fail = NONE
End

Definition twice_def:
  twice x = (x, x)
End

Definition from_masks_def:
  from_masks env (initF, initT) =
    from_rows (-85,-85) (MAP from_mask (if env then initT else initF))
End

Definition gate_def:
  gate (width:num) (height:num)
    (ins: (((int # int) # dir) # value) list)
    (outs: (((int # int) # dir) # value) list)
    (init: mask list # mask list) ⇔
  (* ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧ *)
  ∀env. env_wf env ⇒
    ∀s. LIST_REL (λ(_,v). v_eval env v) ins s ⇒
      ∃s'. LIST_REL (λ(_,v). v_eval env v) outs s' ∧
        ∀z. circuit (make_area width height)
          (MAP2 (λ((p,d),_) v. (p,d,v z)) ins s)
          (MAP2 (λ((p,d),_) v. (p,d,v z)) outs s')
          [] (from_masks (env 0 z) init)
End

Theorem circuit_perm:
  PERM ins ins' ∧ PERM outs outs' ∧ PERM assrt assrt' ⇒
  (circuit area ins outs assrt init ⇔ circuit area ins' outs' assrt' init)
Proof
  rw [circuit_def] \\ BINOP_TAC
  >- metis_tac [PERM_LIST_TO_SET, PERM_MAP]
  \\ metis_tac [ALL_DISTINCT_PERM, PERM_MAP]
QED

Theorem gate_perm:
  PERM ins ins' ∧ PERM outs outs' ⇒
  (gate w h ins outs init ⇔ gate w h ins' outs' init)
Proof
  cheat
  (* rw [gate_def] \\ BINOP_TAC
  >- simp [ALL_DISTINCT_PERM, PERM_CONG, PERM_MAP]
  \\ AP_TERM_TAC \\ ABS_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC \\ ABS_TAC \\ BINOP_TAC
  >- (BINOP_TAC \\ simp [PERM_EVERY])
  \\ AP_TERM_TAC \\ ABS_TAC \\ AP_TERM_TAC \\ BINOP_TAC
  >- (AP_TERM_TAC \\ AP_TERM_TAC \\ simp [PERM_LIST_TO_SET, PERM_MAP])
  \\ BINOP_TAC >- simp [PERM_EVERY]
  \\ AP_TERM_TAC \\ ABS_TAC \\ irule circuit_perm \\ simp [PERM_MAP] *)
QED

Theorem env_wf_translate:
  env_wf f ⇒ env_wf (λi a. f i (add_pt x a))
Proof
  rw [env_wf_def, o_DEF, add_pt_assoc]
QED

Definition delay'_def:
  delay' (n,env) a i = if i < n then eval_env_kind env i else a (i - n:num)
End

Definition eval_pair_def:
  eval_pair b (rF,rT) = if b then rT else rF
End

Theorem eval_pair_var_CASE:
  eval_pair b (var_CASE x rF rT) = var_CASE x (eval_pair b rF) (eval_pair b rT)
Proof
  Cases_on `x` \\ rw []
QED

Theorem eval_classify_clock:
  classify_clock da b d = SOME ea ∧ n < da ⇒
  &n − (&da + d) < &^period ∧
  (eval_env_kind ea n ⇔ e_clock (&n − (&da + d)) = b) ∧
  (e_clock (&n − (&da + d)) ∨ ¬b ⇒ 0 ≤ &n − (&da + d))
Proof
  Cases_on `b` \\ rw [classify_clock_def, e_clock_def] \\ rw [eval_env_kind_def] \\ TRY ARITH_TAC
QED

Theorem eval_classify_this:
  classify_this da d = SOME ea ∧ n < da ⇒
  &n − (&da + d) < &^period ∧
  (eval_env_kind ea n ⇔ 0 ≤ &n − (&da + d))
Proof
  rw [classify_this_def] \\ rw [eval_env_kind_def, e_cell_def] \\ ARITH_TAC
QED

Theorem e_cell_init:
  i < &^period ⇒ (∀env. e_cell env i ⇔ 0 ≤ i ∧ env 0)
Proof
  rw [e_cell_def] \\ Cases_on `0 ≤ i` \\ rw [] \\ AP_TERM_TAC \\ ARITH_TAC
QED

Theorem v_eval'_v_delay':
  classify da a = SOME ea ∧ v_eval' env a s ∧ k ≤ da ⇒
  v_eval' env (v_delay (da - k) a) (λi. delay' (da,eval_pair (env 0 (0,0)) ea) s (k + i))
Proof
  gvs [oneline v_delay_def] \\ CASE_TAC \\ rw [FUN_EQ_THM]
  \\ gvs [v_eval_def, delay'_def, base_def]
  >- (`da ≤ i + k ∧ n ≤ (i + k - da) MOD ^period ∧
      (i + k − da) DIV ^period = i DIV ^period` by ARITH_TAC
    \\ simp [])
  \\ reverse (rw []) >- (AP_TERM_TAC \\ ARITH_TAC)
  \\ `&n − (&(da − k) + i) = &(k + n) − (&da + i)` by ARITH_TAC
  \\ Cases_on `e` \\ gvs [classify_def, base_def, eval_pair_def]
  \\ FIRST (map (drule_then drule) [eval_classify_clock, eval_classify_this]) \\ strip_tac
  \\ drule e_cell_init \\ strip_tac \\ fs []
  \\ rw [eval_env_kind_def] \\ metis_tac []
QED

Theorem v_eval_v_delay':
  classify da a = SOME ea ∧ v_eval env a s ∧ k ≤ da ⇒
  v_eval env (v_delay (da - k) a) (λz i. delay' (da,eval_pair (env 0 z) ea) (s z) (k + i))
Proof
  rw [v_eval_def]
  \\ drule_then (drule_at_then Any $
    qspecl_then [`s z`, `λi a. env i (add_pt z a)`] mp_tac) v_eval'_v_delay'
  \\ rw []
QED

Theorem v_eval'_v_not:
  v_eval' env v1 a1 ⇒
  v_eval' env (v_not v1) (λn. ¬a1 n)
Proof
  gvs [oneline v_not_def] \\ rpt (CASE_TAC \\ gvs [])
  \\ rw [e_cell_def]
  \\ `∃k. i = &k` by rw [NUM_POSINT_EXISTS] \\ gvs []
  \\ `k ≤ n + base ∧ (n + base − k) DIV 586 = (n + base) DIV 586` by ARITH_TAC
  \\ simp [INT_SUB]
QED

Theorem v_eval_v_not:
  v_eval env v1 a1 ⇒
  v_eval env (v_not v1) (λz n. ¬a1 z n)
Proof
  rw [v_eval_def] \\ metis_tac [v_eval'_v_not]
QED

Theorem v_eval'_v_and:
  env_wf env ∧ v_eval' env v1 a1 ∧ v_eval' env v2 a2 ⇒
  v_eval' env (v_and v1 v2) (λn. a1 n ∧ a2 n)
Proof
  gvs [oneline v_and_def] \\ rpt (CASE_TAC \\ rw []) \\ gvs [v_eval'_def]
  (* v_and (Exact i Clock) (Reg n nextCell) = Exact i ThisCellClock *)
  >- (rw [FUN_EQ_THM] \\ Cases_on `e_clock (&(n' + base) − i)` \\ rw []
    \\ DEP_ASM_REWRITE_TAC [] \\ gvs [e_clock_def, e_cell_def] \\ rw []
    >- ARITH_TAC
    \\ `∃k. i = -&k` by ARITH_TAC \\ gvs [INT_ADD]
    \\ `(k + (n' + base)) DIV &^period = (n' + base) DIV &^period + 1` by ARITH_TAC
    \\ fs [env_wf_def]
    \\ cong_tac 2 \\ simp [FUN_EQ_THM, FORALL_PROD])
  (* v_and (Exact i' ThisCell) (Exact i NotClock) = Exact d2 ThisCellNotClock *)
  >- (rw [FUN_EQ_THM] \\ Cases_on `e_clock (&(n + base) − i)` \\ rw []
    \\ gvs [e_cell_def, e_clock_def] \\ reverse (Cases_on `0 ≤ i`)
    >- (`22 ≤ &(n + base) - i` by ARITH_TAC
      \\ `∃k. i = -&k ∧ ∃j. &(n + base) − i' = &j` by ARITH_TAC \\ gvs [INT_ADD]
      \\ cong_tac 2 \\ ARITH_TAC)
    \\ `(∃k. i = &k) ∧ ∃k'. i' = &k'` by ARITH_TAC \\ gvs [INT_SUB, INT_SUB_LE]
    \\ `∀m:int. &^period * m ≤ &(n + base) − &k ⇔ &^period * m ≤ &(n + base) − &k'` by ARITH_TAC
    \\ pop_assum (qspec_then `&(m:num)` (assume_tac o GEN ``m:num`` o SRULE []))
    \\ first_assum (qspec_then `0` mp_tac) \\ simp [NoAsms] \\ rw []
    \\ gvs [INT_SUB, INT_SUB_LE] \\ Cases_on `k' ≤ n + base` \\ gvs [INT_SUB, INT_SUB_LE]
    \\ assume_tac (GSYM $ MATCH_MP X_LE_DIV (DECIDE ``0 < 586n``)) \\ gvs []
    \\ cong_tac 2 \\ irule LESS_EQUAL_ANTISYM \\ simp []
    \\ pop_assum $ K $ qpat_x_assum `$! _` (rw o single o GSYM))
QED

Theorem v_eval_v_and:
  env_wf env ∧ v_eval env v1 a1 ∧ v_eval env v2 a2 ⇒
  v_eval env (v_and v1 v2) (λz n. a1 z n ∧ a2 z n)
Proof
  rw [v_eval_def] \\ metis_tac [v_eval'_v_and, env_wf_translate]
QED

Theorem v_eval'_v_or:
  v_eval' env v1 a1 ∧ v_eval' env v2 a2 ⇒
  v_eval' env (v_or v1 v2) (λn. a1 n ∨ a2 n)
Proof
  gvs [oneline v_or_def] \\ rpt (CASE_TAC \\ rw []) \\ gvs [v_eval'_def]
  (* v_or (Exact i ThisCellClock) (Exact i ThisCellNotClock) = Exact i ThisCell *)
  >- (rw [FUN_EQ_THM] \\ Cases_on `e_clock (&(n + base) − i)` \\ rw [])
QED

Theorem v_eval_v_or:
  v_eval env v1 a1 ∧ v_eval env v2 a2 ⇒
  v_eval env (v_or v1 v2) (λz n. a1 z n ∨ a2 z n)
Proof
  rw [v_eval_def] \\ metis_tac [v_eval'_v_or]
QED

(*
Theorem circuit_conj_imp_gate:
  (∀a1 a2 env.
    circuit (make_area w h)
      [(xy1,d1,a1);(xy2,d2,a2)] [(xy3,d3,conj (delay 5 a1) (delay 5 a2))] []
         (from_masks env init))
  ⇒
  ALL_DISTINCT [(xy1,d1);(xy2,d2);(xy3,d3)]
  ⇒
  gate w h
    [((xy1,d1),v1); ((xy2,d2),v2)]
    [((xy3,d3), v_and (v_delay 5 v1) (v_delay 5 v2))] init
Proof
  gvs [gate_def] \\ rpt strip_tac
  \\ gvs [SF DNF_ss]
  \\ PairCases_on ‘s’ \\ gvs [EXISTS_PROD]
  \\ gvs [assign_sat_def,assign_ext_def]
  \\ qexists_tac ‘λxyd. if xyd = (xy3,d3) then
    λp. conj (delay 5 (s0 (xy1,d1) p)) (delay 5 (s0 (xy2,d2) p)) else s0 xyd’
  \\ `v_eval env (v_and (v_delay 5 v1) (v_delay 5 v2))
      (λp. conj (delay 5 (s0 (xy1,d1) p)) (delay 5 (s0 (xy2,d2) p)))` by (
    rw [conj_def] \\ HO_BACKCHAIN_TAC v_eval_v_and \\ rw []
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ irule v_eval_v_delay \\ rw [])
  \\ gvs [] \\ rw [] \\ gvs [] \\ imp_res_tac is_exact_unique
QED *)

Definition find_in_def:
  (* find_in: (α # β # bexp) list -> var -> α *)
  find_in ins a =
    let (p,d,_) = THE (FIND (λ(_,_,v). case v of Var a' _ => a = a' | _ => F) ins) in
    (p,d)
End

Definition out_lookup_def:
  out_lookup outs x = some (z, v). ∃p. MEM (p, v) outs ∧ x = mk_dpt p z
End

Definition instantiate2_def:
  instantiate2 ((eaF, eaT), (ebF, ebT)) init =
    (instantiate (eaF, ebF) init, instantiate (eaT, ebT) init)
End

Theorem instantiate_twice:
  instantiate (ea, eb) init = res ⇒
  instantiate2 ((ea, ea), (eb, eb)) init = twice res
Proof
  simp [instantiate2_def, twice_def]
QED

Theorem dir_to_xy_bounded:
  dir_to_xy d = (x,y) ⇒ -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1
Proof
  Cases_on `d` \\ simp []
QED

Theorem blist_simulation_ok_ALL_DISTINCT:
  blist_simulation_ok w h ins outs init ⇒
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs)
Proof
  REWRITE_TAC [blist_simulation_ok_def]
  \\ disch_then (mp_tac o CONJUNCT1) \\ simp [blist_simple_checks_def]
QED

Theorem blist_simulation_ok_injective:
  blist_simulation_ok w h ins outs init ∧ w < ^tile ∧ h < ^tile ⇒
  MEM (p,d,v) outs ∧ (MEM (p',d,v') ins ∨ MEM (p',d,v') outs) ∧
  mk_pt p z = mk_pt p' z' ⇒ (p,z) = (p',z') ∧ v = v' ∧ ¬MEM (p',d,v') ins
Proof
  strip_tac
  \\ `∀x y d v. MEM ((x,y),d,v) (ins ++ outs) ⇒
      -1 ≤ x ∧ x < &^tile2 - 1 ∧ -1 ≤ y ∧ y < &^tile2 - 1` by (
    simp []
    \\ last_x_assum mp_tac \\ REWRITE_TAC [blist_simulation_ok_def]
    \\ disch_then (mp_tac o CONJUNCT1) \\ simp [blist_simple_checks_def]
    \\ disch_then (mp_tac o SRULE [EVERY_MEM] o funpow 7 CONJUNCT2)
    \\ ntac 5 strip_tac \\ Cases_on `dir_to_xy d`
    \\ drule_then strip_assume_tac dir_to_xy_bounded
    \\ strip_tac \\ first_x_assum drule
    \\ simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS]
    \\ ARITH_TAC)
  \\ ONCE_REWRITE_TAC [GSYM MEM_APPEND] \\ strip_tac
  \\ MAP_EVERY Cases_on [`p`, `p'`, `z`, `z'`] \\ first_assum drule
  \\ qpat_x_assum `MEM _ _` (fn h =>
    fs [DISJ_IMP_THM, FORALL_AND_THM, mk_pt_def]
    \\ first_x_assum drule \\ ntac 2 strip_tac
    \\ conj_asm1_tac >- ARITH_TAC
    \\ mp_tac h \\ gvs [])
  \\ dxrule blist_simulation_ok_ALL_DISTINCT
  \\ fs [ALL_DISTINCT_APPEND, MEM_MAP, EXISTS_PROD, FORALL_PROD]
  \\ ntac 2 strip_tac >- `F` by metis_tac []
  \\ reverse conj_tac >- metis_tac []
  \\ drule_then assume_tac ALOOKUP_ALL_DISTINCT_MEM \\ res_tac \\ fs []
QED

Theorem blist_simulation_ok_injective_oo:
  blist_simulation_ok w h ins outs init ∧ w < ^tile ∧ h < ^tile ⇒
  MEM (p,d,v) outs ∧ MEM (p',d,v') outs ∧
  mk_pt p z = mk_pt p' z' ⇒ (p,z) = (p',z') ∧ v = v'
Proof
  metis_tac [blist_simulation_ok_injective, MEM_APPEND]
QED

Theorem blist_simulation_ok_injective_io:
  blist_simulation_ok w h ins outs init ∧ w < ^tile ∧ h < ^tile ⇒
  MEM (p,d,v) ins ∧ MEM (p',d,v') outs ∧ mk_pt p z = mk_pt p' z' ⇒ F
Proof
  metis_tac [blist_simulation_ok_injective]
QED

Theorem LIST_REL_MAP2 = CONV_RULE (DEPTH_CONV ETA_CONV) LIST_REL_MAP2;

Theorem MAP2_MAP_LR:
  MAP2 f (MAP g1 ls1) (MAP g2 ls2) = MAP2 (λx y. f (g1 x) (g2 y)) ls1 ls2
Proof
  qspec_tac (`ls2`,`ls2`) \\ Induct_on `ls1` \\ Cases_on `ls2` \\ simp []
QED

Theorem MAP2_MAP_L = SRULE [] $
  INST_TY_TERM ([``g2:γ->γ`` |-> ``I:γ->γ``], [``:ε`` |-> ``:γ``]) MAP2_MAP_LR;
Theorem MAP2_MAP_R = SRULE [] $
  INST_TY_TERM ([``g1:β->β`` |-> ``I:β->β``], [``:δ`` |-> ``:β``]) MAP2_MAP_LR;

Theorem MAP2_self:
  MAP2 f l l = MAP (λx. f x x) l
Proof
  Induct_on `l` \\ simp []
QED

Theorem MAP_eq_MAP2_l:
  LENGTH l1 = LENGTH l2 ⇒ MAP f l1 = MAP2 (λx _. f x) l1 l2
Proof
  qspec_tac (`l2`,`l2`) \\ Induct_on `l1` \\ Cases_on `l2` \\ simp []
QED

Theorem MAP_eq_MAP2_r:
  LENGTH l1 = LENGTH l2 ⇒ MAP f l2 = MAP2 (λ_. f) l1 l2
Proof
  qspec_tac (`l2`,`l2`) \\ Induct_on `l1` \\ Cases_on `l2` \\ simp []
QED

Theorem MAP2_CONG_LIST_REL:
  LIST_REL (λx y. f x y = g x y) l1 l2 ⇒ MAP2 f l1 l2 = MAP2 g l1 l2
Proof
  qspec_tac (`l2`,`l2`) \\ Induct_on `l1` \\ Cases_on `l2` \\ simp []
QED

Theorem EVERY2_sym_fwd = SRULE [] $
  Q.ISPECL [`R:α->β->bool`,`flip R:β->α->bool`] $ Q.GENL [`R1`, `R2`] EVERY2_sym;

Theorem EVERY2_trans':
  (∀x y z. R1 x y ∧ R2 y z ⇒ R3 x z) ⇒
  ∀x y z. LIST_REL R1 x y ∧ LIST_REL R2 y z ⇒ LIST_REL R3 x z
Proof
  strip_tac \\ Induct_on `x` \\ Cases_on `y` \\ Cases_on `z` \\ simp [] \\ metis_tac []
QED

Theorem blist_simulation_ok_imp_gate:
  blist_simulation_ok w h ins outs init ∧
  admissible_ins ins = SOME (da, db') ∧
  (∀x. db' = SOME x ⇒ x = db) ∧
  w < ^tile ∧ h < ^tile ∧
  classify da a = SOME ea ∧
  classify db b = SOME eb ⇒
  gate w h
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) ins)
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) outs)
    (instantiate2 (ea, eb) init)
Proof
  simp [gate_def] \\ strip_tac
  \\ qpat_abbrev_tac `f = λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)`
  \\ gvs [] \\ rpt strip_tac
  \\ qabbrev_tac `ee = λx z. eval_pair (env 0 z) (var_CASE x ea eb)`
  \\ qabbrev_tac `env2 = λz (x,n).
    delay' (var_CASE x da db,ee x z) (EL (var_CASE x 0 1) s z) n`
  \\ qabbrev_tac `s1 = λv z n. eval (age n (env2 z)) v`
  \\ `∀p d v. MEM (p,d,v) outs ⇒ v_eval env (vb_eval ((da,a),(db,b)) v) (s1 v)` by (
    `∀v. admissible_bexpr (da, db') v ⇒
      v_eval env (vb_eval ((da,a),(db,b)) v) (s1 v)` suffices_by (
      rw [] \\ last_x_assum mp_tac \\ REWRITE_TAC [blist_simulation_ok_def]
      \\ disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) \\ simp [EVERY_MEM]
      \\ disch_then (drule o CONJUNCT1) \\ simp [])
    \\ simp [Abbr`s1`] \\ Induct \\ rw [admissible_bexpr_def]
    >- (
      `v_eval env a (HD s) ∧
        (db' = SOME db ⇒ v_eval env b (EL 1 s))` by (
        MAP_EVERY (C qpat_x_assum mp_tac) [`LIST_REL _ _ _`, `admissible_ins _ = _`]
        \\ fs [oneline admissible_ins_def] \\ rpt CASE_TAC
        \\ rw [] \\ fs [assign_sat_def, Abbr`f`])
      \\ Cases_on `v`
      \\ fs [Abbr`env2`, oneline admissible_bexpr_def, Abbr`ee`]
      THENL [ALL_TAC, Cases_on `db'` \\ gvs []]
      \\ dxrule_then assume_tac LT_IMP_LE
      \\ drule_at_then (Pos (el 1))
        (drule_then $ drule_then $ ACCEPT_TAC o SRULE []) v_eval_v_delay')
    >- (HO_BACKCHAIN_TAC v_eval_v_not \\ rw [])
    >- (HO_BACKCHAIN_TAC v_eval_v_and \\ rw [])
    >- (HO_BACKCHAIN_TAC v_eval_v_or \\ rw []))
  \\ qexists_tac `MAP (λ(_,_,v). s1 v) outs` \\ rw []
  >- (
    simp [LIST_REL_MAP1, LIST_REL_MAP2] \\ irule EVERY2_refl
    \\ simp [FORALL_PROD, Abbr`f`] \\ metis_tac [])
  \\ drule_then (qspec_then `env2 z` suff_eq_tac o
      MATCH_MP simulation_ok_IMP_circuit) blist_simulation_ok_thm
  \\ simp [MAP2_MAP_L, MAP2_MAP_R, MAP2_self]
  \\ cong_tac 1 THENL [cong_tac 2, all_tac]
  >- (
    fs [eval_io_def, Abbr`f`, MAP2_MAP_L, LIST_REL_MAP1]
    \\ MAP_EVERY (C qpat_x_assum mp_tac) [`LIST_REL _ _ _`, `admissible_ins _ = _`]
    \\ fs [oneline admissible_ins_def] \\ rpt CASE_TAC
    \\ rw [] \\ rw [Abbr`s1`] \\ pairarg_tac
    \\ gvs [FUN_EQ_THM, Abbr`env2`, delay'_def])
  >- (
    fs [eval_io_def, Abbr`f`, MAP2_MAP_L, MAP2_MAP_R, MAP2_self]
    \\ irule MAP_CONG \\ simp [FORALL_PROD] \\ rw [FUN_EQ_THM])
  \\ Cases_on `ea` \\ Cases_on `eb` \\ rename [`((eaF,eaT),(ebF,ebT))`]
  \\ simp [instantiate2_def, from_masks_def, MAP_COMPOSE]
  \\ AP_TERM_TAC \\ simp [Abbr`env2`, Abbr`ee`, eval_pair_var_CASE]
  \\ `∀ea eb.
        MAP from_mask (instantiate (ea,eb) init) =
        MAP (MAP (eval (λ(x,n). delay'
          (var_CASE x da db, var_CASE x ea eb)
          (EL (var_CASE x 0 1) s z) n)) ∘ from_blist) init` suffices_by (
    CASE_TAC \\ simp [eval_pair_def])
  \\ rw [MAP_COMPOSE, instantiate_def]
  \\ qmatch_goalsub_abbrev_tac `eval env3`
  \\ irule MAP_CONG \\ rw []
  \\ last_x_assum mp_tac \\ REWRITE_TAC [blist_simulation_ok_def]
  \\ disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) \\ simp [EVERY_MEM]
  \\ disch_then (dxrule o CONJUNCT2)
  \\ `∀v. admissible_bexpr (da,db') v ⇒
    eval (instantiate_var (ea,eb)) v = eval env3 v` suffices_by (
    Induct_on `x` \\ simp [admissible_row_def, instantiate_row_def,
      from_blist_def, from_mask_def, from_mask_mk]
    \\ rw [from_mask_mk] \\ EVAL_TAC)
  \\ Induct_on `v` \\ simp [admissible_bexpr_def, instantiate_var_def]
  \\ Cases \\ simp [admissible_bexpr_def, instantiate_var_def,
    Abbr`env3`, delay'_def]
  \\ Cases_on `db'` \\ rw []
QED

Theorem blist_simulation_ok_imp_gate_1:
  blist_simulation_ok w h [(p1,d1,Var A da)] outs init ⇒
  w < ^tile ∧ h < ^tile ⇒
  classify da a = SOME ea ⇒
  gate w h [((p1,d1),a)]
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(da,a)) v)) outs)
    (instantiate2 (ea, ea) init)
Proof
  rpt strip_tac
  \\ dxrule_then (drule_at_then Any $ dxrule_at_then Any $
      qspec_then `NONE` (irule o SRULE [])) blist_simulation_ok_imp_gate
  \\ simp [admissible_ins_def]
QED

Theorem blist_simulation_ok_imp_gate_2:
  blist_simulation_ok w h [(p1,d1,Var A da); (p2,d2,Var B db)] outs init ⇒
  w < ^tile ∧ h < ^tile ⇒
  classify da a = SOME ea ∧
  classify db b = SOME eb ⇒
  gate w h [((p1,d1),a); ((p2,d2),b)]
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) outs)
    (instantiate2 (ea, eb) init)
Proof
  rpt strip_tac
  \\ dxrule_then (dxrule_at_then (Pos (el 6)) $ dxrule_at_then Any $
      qspec_then `SOME db` (irule o SRULE [])) blist_simulation_ok_imp_gate
  \\ simp [admissible_ins_def]
QED

Theorem gate_weaken:
  LIST_REL (λ(pd,v) (pd',v'). pd = pd' ∧ v ⊑ v') outs outs' ∧
  gate w h ins outs init ⇒ gate w h ins outs' init
Proof
  simp [gate_def] \\ strip_tac
  \\ fs [] \\ rpt strip_tac
  \\ last_x_assum (dxrule_then dxrule) \\ strip_tac
  \\ qexists_tac `s'` \\ conj_tac
  >- (
    last_x_assum (fn h1 => last_x_assum (fn h2 =>
      mp_tac (CONJ (MATCH_MP EVERY2_sym_fwd h1) h2)))
    \\ prim_irule $ SPEC_ALL $ UNDISCH EVERY2_trans'
    \\ simp [FORALL_PROD, v_subset_def])
  \\ pop_assum suff_eqr_tac \\ cong_tac 5
  \\ `MAP2 (λ(p,d) v. (p,d,v z)) (MAP FST outs) s' =
      MAP2 (λ(p,d) v. (p,d,v z)) (MAP FST outs') s'` by (
    cong_tac 2
    \\ CONV_TAC $ PATH_CONV "ll" $ REWR_CONV $ SYM LIST_REL_eq
    \\ simp [EVERY2_MAP] \\ drule_at_then Any irule EVERY2_mono
    \\ simp [FORALL_PROD])
  \\ pop_assum suff_eq_tac \\ cong_tac 1 \\ simp [MAP2_MAP_L]
  \\ cong_tac 3 \\ simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem half_adder_weaken:
  (p ⇒ gate w h ins [(pd,v_or
    (v_and (v_delay 15 a) (v_or (v_and (v_delay 12 a) (v_not (v_delay 18 b)))
      (v_and (v_not (v_delay 12 a)) (v_and (v_delay 15 b) (v_not (v_delay 18 b))))))
    (v_and (v_not (v_delay 15 a)) (v_or (v_delay 12 a) (v_delay 15 b)))); out] init) ⇒
  p ⇒ gate w h ins [(pd,v_xor (v_delay 15 a) (v_delay 18 b));out] init
Proof
  rpt strip_tac \\ first_x_assum dxrule
  \\ strip_tac \\ dxrule_at_then Any irule gate_weaken
  \\ PairCases_on `out` \\ simp []
  \\ Cases_on `a` \\ simp [] \\ Cases_on `b` \\ simp []
  \\ irule Reg_mono \\ simp [] \\ metis_tac []
QED

Definition gate_at'_def:
  gate_at' (x,y) (init:mask list # mask list) =
    from_rows (75*x-85, 75*y-85) ARB
End

Definition gate_at_def:
  gate_at p init =
    U {gate_at' (add_pt p (mul_pt (&^tile2) z)) init | z | T}
End

Definition iunion_def:
  iunion f = U {f z | z | T}
End

Theorem mem_iunion[simp]:
  x ∈ iunion f ⇔ ∃a. x ∈ f a
Proof
  simp [iunion_def, PULL_EXISTS]
QED

Theorem iunion_empty[simp]:
  iunion (λ_. ∅) = ∅
Proof
  simp [EXTENSION]
QED

Definition floodfill_mod_def:
  floodfill_mod (area: (int # int) list)
    (ins: (((int # int) # dir) # (int # int -> num -> bool)) list)
    (outs: (((int # int) # dir) # (int # int -> num -> bool)) list) =
  circ_mod
    (iunion (λz. set (MAP (λp. mk_pt p z) area)))
    (iunion (λz. set (MAP (λ((p,d),v). (mk_pt p z, d, v z)) ins)))
    (iunion (λz. set (MAP (λ((p,d),v). (mk_pt p z, d, v z)) outs)))
    {}
End

Definition in_range_def:
  in_range (x,y) ⇔
    (x % 2 = 0 ∧ 0 ≤ x ∧ x < &^tile2) ∧
    (y % 2 = 0 ∧ 0 ≤ y ∧ y < &^tile2)
End

Definition floodfill_def:
  floodfill (area: (int # int) list)
    (ins: (((int # int) # dir) # value) list)
    (outs: (((int # int) # dir) # value) list)
    (crosses: ((int # int) # (int # int) # dir) list)
    (init: (int # int) set) ⇔
  (∀p. MEM p area ⇒ in_range p) ∧
  ∀env. env_wf env ⇒
    ∃sin sout.
      LIST_REL (λ(_,v). v_eval env v) ins sin ∧
      LIST_REL (λ(_,v). v_eval env v) outs sout ∧
      (∀pd v. MEM (pd, v) ins ⇒ is_exact v) ∧
      ∀scross.
        LENGTH crosses = LENGTH scross ∧
        (∀s. MEM s scross ⇒ ∃v.
          classify 5 v = SOME (Zeros, Zeros) ∧
          v_eval env v s) ⇒
        run (floodfill_mod area
          (ZIP (MAP FST ins, sin) ++
            MAP2 (λ(p,_,d) v. ((p,d),v)) crosses scross)
          (ZIP (MAP FST outs, sout) ++
            MAP2 (λ(_,p,d) v. ((p,d), delay 5 ∘ v)) crosses scross))
          init
End

Theorem floodfill_start:
  floodfill [] [] [] [] ∅
Proof
  rw [floodfill_def, floodfill_mod_def, run_empty_mod]
QED

Theorem floodfill_add_ins:
  floodfill area ins outs [] init ∧
  gate 1 1 [((a,d),Exact dl v)] outs' init1 ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  ¬MEM (add_pt p a) (MAP (FST ∘ FST) (ins ++ outs)) ⇒
  floodfill (p :: area) (((add_pt p a,d),Exact dl v) :: ins)
    (MAP (λ((a',d'),Q). ((add_pt p a',d'),Q)) outs' ++ outs) []
    (gate_at p init1 ∪ init)
Proof
  strip_tac
  \\ gvs [floodfill_def]
  \\ rpt gen_tac
  \\ disch_tac
  \\ conj_tac >- (rw [] \\ res_tac \\ simp [in_range_def])
  \\ rpt strip_tac
  \\ gvs [gate_def]
  \\ first_x_assum drule
  \\ first_x_assum drule
  \\ rpt strip_tac
  \\ simp [SF DNF_ss,MEM_MAP,PULL_EXISTS,SF SFY_ss]
  \\ cheat (* todo *)
QED

Theorem floodfill_perm:
  floodfill area ins outs crosses init ∧
  PERM outs outs' ∧ PERM crosses crosses' ⇒
  floodfill area ins outs' crosses' init
Proof
  cheat
  (* simp [floodfill_def] \\ strip_tac
  \\ rw [] \\ first_x_assum dxrule \\ rw []
  \\ `set (MAP FST outs') = set (MAP FST outs)` by
    simp [PERM_LIST_TO_SET, PERM_MAP]
  \\ qexists_tac `s` \\ simp [] \\ rpt strip_tac
  >- metis_tac []
  >- metis_tac [MEM_PERM]
  >- metis_tac []
  \\ first_x_assum dxrule \\ impl_tac
  >- (rpt strip_tac \\ first_x_assum irule \\ drule_then (fs o single) MEM_PERM)
  \\ `(∀f. set (MAP f outs: ((int # int) # dir # (num -> bool)) list) = set (MAP f outs')) ∧
      ∀f. set (MAP f crosses: ((int # int) # dir # (num -> bool)) list) = set (MAP f crosses')` by
    simp [PERM_LIST_TO_SET, PERM_MAP]
  \\ simp [floodfill_mod_def, MAP_COMPOSE] *)
QED

Theorem floodfill_weaken_gen:
  floodfill area ins outs crosses init ∧
  LIST_REL (λ(pd,P) (pd',Q). pd = pd' ∧ P ⊑ Q) outs outs' ⇒
  floodfill area ins outs' crosses init
Proof
  cheat
  (* simp [floodfill_def] \\ strip_tac
  \\ rw [] \\ first_x_assum dxrule \\ rw []
  \\ `MAP FST outs = MAP FST outs'` by (
    CONV_TAC $ PATH_CONV "ll" $ REWR_CONV $ SYM LIST_REL_eq
    \\ simp [EVERY2_MAP] \\ drule_at_then Any irule EVERY2_mono
    \\ simp [FORALL_PROD])
  \\ qexists_tac `s` \\ fs []
  \\ reverse conj_tac >- first_assum ACCEPT_TAC
  \\ fs [SF DNF_ss] \\ rw []
  \\ drule_then drule LIST_REL_MEM_IMP_R \\ Cases_on `v` \\ rw [EXISTS_PROD]
  \\ metis_tac [assign_sat_mono] *)
QED

Theorem floodfill_weaken:
  floodfill area ins outs crosses init ∧
  PERM outs ((pd,Exact (&d) ThisCell) :: outs') ⇒
  floodfill area ins ((pd,Reg d (Cell (0, 0))) :: outs') crosses init
Proof
  cheat
  (* strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ POP_ASSUM_LIST (assume_tac o MATCH_MP floodfill_perm o LIST_CONJ o rev)
  \\ irule_at Any floodfill_weaken_gen \\ first_x_assum (irule_at Any)
  \\ simp [EVERY2_refl, FORALL_PROD]
  \\ `∃i. (&(n + base):int) − &d = &i` by ARITH_TAC \\ rw []
  \\ rw [v_subset_def, v_eval_def, e_cell_def]
  \\ cong_tac 2 \\ ARITH_TAC *)
QED

Theorem run_to_clear_mods:
  ∀k m s t.
    run_to k (clear_mods m) s t ⇒
    FUNPOW step k s = t ∧
    (k ≠ 0 ⇒  t ∩ (m (k-1)).assert_area = (m (k-1)).assert_content)
Proof
  gvs [run_to_def] \\ gen_tac
  \\ qsuff_tac ‘∀k n m s t.
       mod_steps k (clear_mods m) n s t ⇒
       FUNPOW step k s = t ∧
       (k ≠ 0 ⇒ t ∩ (m (n + k − 1)).assert_area = (m (n + k − 1)).assert_content)’
  >- (rw [] \\ res_tac \\ gvs [])
  \\ Induct \\ gvs [mod_steps_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [mod_step_def,clear_mods_def,clear_mod_def]
  \\ last_x_assum drule
  \\ gvs [FUNPOW] \\ strip_tac
  \\ gvs [ADD1] \\ Cases_on ‘k’ \\ gvs []
QED

Definition build_mega_cells_def:
  build_mega_cells init = ARB
End

Definition read_mega_cells_def:
  read_mega_cells s =
    { p | add_pt (mul_pt (150 * 21) p) (23 * 75 + 1, 8 * 75 - 1) ∈ s }
End

Theorem read_mega_cells_build_mega_cells_thm:
  read_mega_cells (build_mega_cells s) = s
Proof
  cheat (* todo *)
QED

Triviality in_if_set_empty:
  x ∈ (if b then t else {}) ⇔ b ∧ x ∈ t
Proof
  rw []
QED

Triviality in_lwss_lemma:
  dx < 10 ∧ n < 10 ⇒ (3150 * (k:int) + &n = & dx ⇔ k = 0 ∧ dx = n)
Proof
  Cases_on ‘k’ \\ gvs []
  \\ rename [‘m ≠ 0’]
  \\ Cases_on ‘m’ \\ gvs []
  \\ gvs [MULT_CLAUSES]
  \\ rw [] \\ gvs [INT_ADD]
  \\ gvs [integerTheory.INT_MUL_RNEG]
  \\ irule $ intLib.COOPER_PROVE “n + k < m ⇒ -& m + & n ≠ (& k):int”
  \\ gvs []
QED

Triviality in_lwss_as_set_E:
  (3150 * i + 1726, 3150 * j + 599) ∈
    lwss_as_set (1725 + 3150 * p1 - 5, 600 + 3150 * p2 -5) E
  ⇔
  i = p1 ∧ j = p2
Proof
  rewrite_tac [lwss_as_set_def]
  \\ once_rewrite_tac [GSYM $ SRULE [] $ Q.SPECL [`-i`, `-j`] from_rows_translate]
  \\ rewrite_tac [intLib.COOPER_PROVE
       “3150 * i + a + -(b + 3150 * j - c) = 3150 * (i - j) + (a - b + c):int”]
  \\ gvs [] \\ simp [IN_from_rows]
  \\ qspec_then ‘E’ assume_tac (gol_circuitTheory.io_gate_lenth |> GEN_ALL)
  \\ gvs [MEM_EL,PULL_EXISTS,oEL_THM, SF CONJ_ss]
  \\ simp [in_lwss_lemma,SF CONJ_ss]
  \\ eq_tac \\ rw [] \\ EVAL_TAC
QED

Triviality cv_LENGTH_thm:
  ∀cv. cv_LENGTH cv = cv$Num (cv_right_depth cv)
Proof
  gvs [cv_stdTheory.cv_LENGTH_def]
  \\ qsuff_tac ‘∀cv k. cv_LEN cv (cv$Num k) = cv$Num (cv_right_depth cv + k)’
  \\ gvs []
  \\ Induct \\ simp [cv_stdTheory.cv_right_depth_def,Once cv_stdTheory.cv_LEN_def]
QED

Theorem nextCell_correct:
  step s (x0,x1) ⇔ r_eval (s ∘ add_pt (x0,x1)) nextCell
Proof
  fn g as (_, thm_stmt) => let
    val lem = thm_stmt
      |> SCONV [nextCell_def,gol_rulesTheory.step_def,IN_DEF,LET_THM]
      |> SRULE [GSYM int_sub,gol_rulesTheory.live_adj_def]
    val tm = lem |> concl |> rand |> subst [
      “(s:state) (x0,x1)”     |-> “a00:bool”,
      “(s:state) (x0,x1-1)”   |-> “a01:bool”,
      “(s:state) (x0,x1+1)”   |-> “a02:bool”,
      “(s:state) (x0-1,x1)”   |-> “a10:bool”,
      “(s:state) (x0-1,x1-1)” |-> “a11:bool”,
      “(s:state) (x0-1,x1+1)” |-> “a12:bool”,
      “(s:state) (x0+1,x1)”   |-> “a20:bool”,
      “(s:state) (x0+1,x1-1)” |-> “a21:bool”,
      “(s:state) (x0+1,x1+1)” |-> “a22:bool”]
    val calc_def = Define ‘calc a00 a01 a02 a10 a11 a12 a20 a21 a22 = ^tm’
    val calc_all_def = tDefine "calc_all"
      ‘calc_all xs =
        if LENGTH xs < 9 then
          calc_all (F::xs) ∧ calc_all (T::xs)
        else calc (EL 0 xs) (EL 1 xs) (EL 2 xs)
                  (EL 3 xs) (EL 4 xs) (EL 5 xs)
                  (EL 6 xs) (EL 7 xs) (EL 8 xs)’
      (WF_REL_TAC ‘measure (λxs. 9 - LENGTH xs)’ \\ gvs [])
    val _ = cv_transLib.cv_trans calc_def
    val _ = cv_transLib.cv_trans_rec calc_all_def (
      WF_REL_TAC ‘measure (λxs. 9 - cv_right_depth xs)’ \\ rw []
      \\ gvs [cv_LENGTH_thm,cv_stdTheory.cv_right_depth_def,cvTheory.c2b_def])
    val lemma = prove(
      “calc_all (F::xs) ∧ calc_all (T::xs) ⇔  ∀b. calc_all (b::xs)”,
      eq_tac \\ gvs [] \\ strip_tac \\ Cases \\ gvs [])
    val calc_all_eq = REWRITE_RULE [lemma] calc_all_def
    val th = cv_transLib.cv_eval “calc_all []”
    val th1 = funpow 10 (SRULE [Once calc_all_eq]) th |> SRULE [calc_def]
  in
    ACCEPT_TAC (SRULE [th1] lem) g
  end
QED

Theorem floodfill_finish:
  floodfill area
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact (-77) Clock)]
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact 509 Clock)] [] init
  ⇒
  gol_in_gol build_mega_cells (^period * 60) read_mega_cells
Proof
  cheat
  (* rw [gol_rulesTheory.gol_in_gol_def] \\ gvs [floodfill_def, SF DNF_ss]
  \\ gvs [FUN_EQ_THM,FORALL_PROD] \\ rw []
  \\ rename [‘FUNPOW step n s_init (x,y) = _’]
  \\ qabbrev_tac ‘env = λn. FUNPOW step n s_init’
  \\ ‘env_wf env’ by
   (gvs [env_wf_def,Abbr‘env’] \\ gen_tac \\ PairCases
    \\ simp [GSYM ADD1,FUNPOW_SUC] \\ gvs [nextCell_correct])
  \\ first_x_assum drule \\ strip_tac
  \\ PairCases_on ‘s’ \\ gvs [assign_sat_def]
  \\ gvs [v_eval_def]
  \\ pop_assum mp_tac
  \\ gvs [floodfill_mod_def]
  \\ disch_then $ qspecl_then [‘s0’,‘s1’] mp_tac
  \\ impl_tac >- simp [assign_ext_def]
  \\ strip_tac
  \\ dxrule run_clear_mods
  \\ impl_tac
  >-
   (simp [can_clear_def,join_all_def]
    \\ gvs [translate_mods_def,EXTENSION,EXISTS_PROD,translate_mod_def,
            circ_mod_def])
  \\ rw []
  \\ gvs [run_def]
  \\ pop_assum $ qspec_then ‘^period * 60 * n’ mp_tac
  \\ strip_tac
  \\ ‘build_mega_cells s_init = init’ by cheat
  \\ gvs []
  \\ dxrule run_to_clear_mods
  \\ strip_tac
  \\ Cases_on ‘n = 0’
  >- gvs [read_mega_cells_build_mega_cells_thm, Abbr`env`]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ gvs [] \\ rpt strip_tac \\ gvs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [join_all_def]
  \\ once_rewrite_tac [EXTENSION]
  \\ simp [PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
  \\ disch_then $ qspecl_then [‘21 * 150 * x + 23 * 75 + 1’,
                               ‘21 * 150 * y + 8 * 75 - 1’] mp_tac
  \\ simp [GSYM PULL_EXISTS]
  \\ strip_tac
  \\ dxrule (METIS_PROVE [] “(x1 ∧ x2 ⇔ y) ⇒ x2 ⇒ (x1 = y)”)
  \\ Cases_on ‘n = 0’ \\ gvs []
  \\ ‘(60 * ^period * n − 1) MOD 60 = 59’ by
   (rewrite_tac [GSYM MULT_ASSOC]
    \\ Cases_on ‘^period * n’ \\ gvs []
    \\ gvs [MULT_CLAUSES])
  \\ impl_tac
  >-
   (gvs [iunion_def,circ_mod_def,circ_output_area_def]
    \\ gvs [circ_io_area_def]
    \\ simp [IN_DEF]
    \\ gvs [translate_set_def,PULL_EXISTS]
    \\ simp [SF DNF_ss,is_ew_def,io_box_def,box_def,EXISTS_PROD,mk_pt_def]
    \\ disj1_tac \\ intLib.COOPER_TAC)
  \\ gvs [read_mega_cells_def]
  \\ simp [IN_DEF]
  \\ gvs [translate_set_def,PULL_EXISTS]
  \\ simp [SF DNF_ss,circ_mod_def,circ_io_lwss_def,lwss_at_def,EXISTS_PROD,mk_pt_def]
  \\ simp [in_if_set_empty]
  \\ ‘(3150 * x + 1725 + 1,3150 * y + 600 − 1) =
      (3150 * x + 1726,3150 * y + 599)’ by (gvs [] \\ intLib.COOPER_TAC)
  \\ gvs [] \\ disch_then kall_tac
  \\ irule (METIS_PROVE [] “~y2 ∧ (x = y1) ⇒ (x ⇔ y1 ∨ y2)”)
  \\ conj_tac
  >- (CCONTR_TAC \\ gvs []
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ gvs [lwss_as_set_def,IN_from_rows]
      \\ CCONTR_TAC \\ gvs []
      \\ gvs [oEL_THM]
      \\ gvs [oEL_THM,gol_circuitTheory.io_gate_lenth,lwss_as_set_def,IN_from_rows]
      \\ qspec_then ‘E’ mp_tac (gol_circuitTheory.io_gate_lenth |> GEN_ALL)
      \\ strip_tac
      \\ gvs [MEM_EL,PULL_EXISTS]
      \\ ntac 3 $ pop_assum kall_tac
      \\ ntac 4 $ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ intLib.COOPER_TAC)
  \\ gvs [integerTheory.INT_LDISTRIB,INT_MUL_ASSOC]
  \\ rewrite_tac [in_lwss_as_set_E] \\ gvs []
  \\ gvs [FORALL_PROD,mk_dpt_def,mk_pt_def,base_def]
  \\ simp [e_cell_def]
  \\ gvs [IN_DEF,is_ew_def]
  \\ cong_tac 2
  \\ simp [base_def,INT_ADD]
  \\ once_rewrite_tac [ADD_COMM]
  \\ ‘0 < 60:num’ by gvs []
  \\ drule ADD_DIV_ADD_DIV
  \\ disch_then $ rewrite_tac o single o GSYM
  \\ gvs [DIV_DIV_DIV_MULT] *)
QED

Theorem assign_ext_sat:
  assign_ext s1 s2 ∧ assign_sat env s1 v ⇒ assign_sat env s2 v
Proof
  MAP_EVERY PairCases_on [‘s1’, ‘s2’, ‘v’]
  \\ gvs [assign_ext_def,assign_sat_def,SUBSET_DEF,o_DEF]
  \\ strip_tac
  \\ `∀x. s10 (mk_dpt ((v0,v1),v2) x) = s20 (mk_dpt ((v0,v1),v2) x)` suffices_by gvs []
  \\ strip_tac \\ first_assum irule \\ simp []
QED

Theorem assign_ext_trans:
  assign_ext s1 s2 ∧ assign_ext s2 s3 ⇒ assign_ext s1 s3
Proof
  MAP_EVERY PairCases_on [‘s1’, ‘s2’, ‘s3’]
  \\ gvs [assign_ext_def, SUBSET_DEF]
QED

Theorem add_pt_simps[simp]:
  ∀a b.
    neg_pt (neg_pt a) = a ∧
    add_pt a (neg_pt b) = sub_pt a b ∧
    sub_pt a (neg_pt b) = add_pt a b ∧
    add_pt (sub_pt a b) b = a ∧
    sub_pt (add_pt a b) b = a ∧
    add_pt (neg_pt a) (add_pt a b) = b ∧
    add_pt a (add_pt (neg_pt a) b) = b
Proof
  simp [FORALL_PROD, int_sub] \\ ARITH_TAC
QED

Theorem span_imp_add_pt:
  (x,d) ∈ span s ⇒ (add_pt x delta, d) ∈ span (λ(a,d). s (sub_pt a delta,d))
Proof
  PairCases_on ‘x’ \\ PairCases_on ‘delta’
  \\ simp [span_def, mk_dpt_def, EXISTS_PROD, mk_pt_def, IN_DEF]
  \\ strip_tac
  \\ qexistsl_tac [`p_1`, `p_2`, `p_1'+delta0`,`p_2'+delta1`]
  \\ gvs [ARITH_PROVE ``a+b-b:int=a``] \\ ARITH_TAC
QED

Theorem assign_ext_tr_IMP:
  assign_ext (assign_tr delta s) s2 ⇒
  assign_ext s (assign_tr (neg_pt delta) s2)
Proof
  MAP_EVERY PairCases_on [‘s’, ‘s2’]
  \\ simp [assign_ext_def, assign_tr_def, SUBSET_DEF] \\ strip_tac
  \\ pop_assum (assume_tac o GSYM)
  \\ simp [GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM] \\ ntac 2 strip_tac
  \\ Cases_on `x` \\ DEP_ASM_REWRITE_TAC [] \\ simp []
  \\ drule_then (qspec_then `delta` assume_tac) span_imp_add_pt \\ rfs []
  \\ last_x_assum $ drule_then assume_tac
  \\ drule_then (qspec_then `neg_pt delta` assume_tac) span_imp_add_pt \\ rfs []
QED

Theorem assign_sat_tr_IMP:
  assign_sat env s ((p, d), v) ⇒
  assign_sat env (assign_tr delta s) ((add_pt p delta, d), v)
Proof
  PairCases_on ‘s’ \\ simp [assign_sat_def, assign_tr_def]
  \\ rw [assign_ext_def, assign_tr_def, SUBSET_DEF]
  >- (irule span_imp_add_pt \\ simp [])
  \\ pop_assum suff_eq_tac \\ AP_TERM_TAC
  \\ simp [FUN_EQ_THM, FORALL_PROD, mk_dpt_def, mk_pt_def]
  \\ Cases_on `p` \\ Cases_on `delta` \\ rw []
  \\ cong_tac 4 \\ simp [] \\ ARITH_TAC
QED

Theorem add_pt_comm:
  add_pt a b = add_pt b a
Proof
  MAP_EVERY Cases_on [`a`,`b`] \\ simp [INT_ADD_SYM]
QED

Theorem assign_sat_tr_IMP' =
  ONCE_REWRITE_RULE [add_pt_comm] assign_sat_tr_IMP;

Theorem floodfill_add_gate:
  floodfill area ins outs crosses init ∧
  gate w h ins1 outs1 init1 ∧
  PERM outs (del ++ outs') ⇒
  ∀p x' y'.
  (p = (&(2 * x'), &(2 * y')) ∧ x' + w ≤ ^tile ∧ y' + h ≤ ^tile ∧
  del = MAP (λ((a, d), P). ((add_pt p a, d), P)) ins1) ∧
  EVERY (λa. ¬MEM (add_pt p a) area) (make_area w h) ⇒
  floodfill
    (MAP (add_pt p) (make_area w h) ++ area) ins
    (MAP (λ((a, d), P). ((add_pt p a, d), P)) outs1 ++ outs') crosses
    (gate_at p init1 ∪ init)
Proof
  cheat
  (* rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm \\ gvs []
  \\ simp [floodfill_def] \\ strip_tac \\ fs [SF DNF_ss, MEM_MAP]
  \\ conj_tac >- (
    simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS, in_range_def]
    \\ ARITH_TAC)
  \\ qabbrev_tac `p = (&(2*x'):int, &(2*y'):int)`
  \\ rpt strip_tac \\ first_x_assum $ drule_then strip_assume_tac
  \\ rename [`SND s1`] \\ qabbrev_tac `s1' = assign_tr (neg_pt p) s1`
  \\ fs [gate_def, EVERY_MEM]
  \\ last_x_assum $ drule_then $ qspec_then `s1'` mp_tac
  \\ impl_tac >- (
    rw [] \\ PairCases_on `e` >- (
      first_x_assum dxrule \\ simp [] \\ strip_tac
      \\ dxrule_then (qspec_then `neg_pt p` assume_tac) assign_sat_tr_IMP'
      \\ fs [Abbr`s1'`])
    \\ simp [] \\ strip_tac
    \\ `(add_pt (e0,e1) p,e2) ∈ span (SND s1)` by (
      drule_then (qspec_then `p` suff_eq_tac) span_imp_add_pt
      \\ AP_TERM_TAC \\ AP_TERM_TAC \\ rw [FUN_EQ_THM, FORALL_PROD]
      \\ Cases_on `s1` \\ simp [Abbr`s1'`, assign_tr_def])
    \\ cheat)
  \\ strip_tac \\ rename [‘assign_ext s1' s2'’]
  \\ qabbrev_tac `s2 = assign_tr p s2'`
  \\ qexists_tac ‘s2’
  \\ `assign_ext s1 s2` by (
    qunabbrevl_tac [`s2`, `s1'`] \\ drule assign_ext_tr_IMP \\ gvs [])
  \\ conj_tac >- cheat
  \\ conj_tac >- cheat
  \\ conj_tac >- simp [SF SFY_ss]
  \\ rpt strip_tac
  \\ rename [‘assign_ext s2 s3’]
  \\ first_x_assum (drule_at (Pos (el 2)))
  \\ impl_tac >- simp [SF SFY_ss, assign_ext_trans]
  \\ strip_tac
  \\ cheat *)
QED

Theorem floodfill_add_small_gate:
  floodfill area ins outs crosses init ∧
  gate 1 1 ins1 outs1 init1 ∧
  PERM outs (del ++ outs') ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  del = MAP (λ((a,d),P). ((add_pt p a, d), P)) ins1 ⇒
  floodfill (p :: area) ins
    (MAP (λ((a,d),Q). ((add_pt p a,d),Q)) outs1 ++ outs') crosses
    (gate_at p init1 ∪ init)
Proof
  rw [] \\ dxrule_then (dxrule_then dxrule) floodfill_add_gate
  \\ simp [make_area_def]
QED

Theorem floodfill_add_crossover_gen:
  floodfill area ins outs crosses init ∧
  PERM outs (((p',d1),P) :: outs') ∧
  (∀Q. classify db Q = SOME (Zeros, Zeros) ⇒
    gate 1 1 [((p1,d1),P); ((p2,d2),Q)]
      [((a',d1),v_delay 5 P); ((b',d2),v_delay 5 Q)]
      init1) ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  p' = add_pt p a ⇒
  floodfill (p :: area) ins
    (((add_pt p a',d1),v_delay 5 P) :: outs')
    ((add_pt p b, add_pt p b', d2) :: crosses)
    (gate_at p init1 ∪ init)
Proof
  cheat (* todo *)
QED

Theorem floodfill_add_crossover_l:
  floodfill area ins outs crosses init ∧
  blist_simulation_ok 1 1
    [(a,d1,Var A 5); (b,d2,Var B 5)]
    [(a',d1,Var A 0); (b',d2,Var B 0)] init1 ∧
  PERM outs (((p',d1),P) :: outs') ⇒
  classify 5 P = SOME ea ⇒
  instantiate2 (ea, (Zeros, Zeros)) init1 = init2 ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  p' = add_pt p a ⇒
  floodfill (p :: area) ins
    (((add_pt p a',d1),v_delay 5 P) :: outs')
    ((add_pt p b, add_pt p b', d2) :: crosses)
    (gate_at p init2 ∪ init)
Proof
  rpt strip_tac \\ irule floodfill_add_crossover_gen
  \\ rpt $ last_x_assum $ irule_at Any
  \\ dxrule_then (dxrule_then assume_tac o SRULE []) blist_simulation_ok_imp_gate_2
  \\ qexistsl_tac [`b`,`a`,`5`] \\ rw []
QED

Theorem floodfill_add_crossover_r:
  floodfill area ins outs crosses init ∧
  blist_simulation_ok 1 1
    [(a,d1,Var A 5); (b,d2,Var B 5)]
    [(a',d1,Var A 0); (b',d2,Var B 0)] init1 ∧
  PERM outs (((p',d2),P) :: outs') ⇒
  classify 5 P = SOME eb ⇒
  instantiate2 ((Zeros, Zeros), eb) init1 = init2 ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  p' = add_pt p b ⇒
  floodfill (p :: area) ins
    (((add_pt p b',d2),v_delay 5 P) :: outs')
    ((add_pt p a, add_pt p a', d1) :: crosses)
    (gate_at p init2 ∪ init)
Proof
  rpt strip_tac \\ irule floodfill_add_crossover_gen
  \\ rpt $ last_x_assum $ irule_at Any
  \\ dxrule_then (dxrule_at_then (Pos (el 2)) assume_tac o SRULE []) blist_simulation_ok_imp_gate_2
  \\ qexistsl_tac [`a`,`b`,`5`] \\ rw []
  \\ first_x_assum dxrule \\ simp []
  \\ disch_then suff_eq_tac
  \\ irule gate_perm \\ simp [PERM_SWAP_AT_FRONT]
QED

Theorem floodfill_finish_crossover:
  floodfill area ins outs crosses init ∧
  PERM outs (((p,d),P) :: outs') ∧
  PERM crosses ((p,q,d) :: crosses') ⇒
  classify 5 P = SOME (Zeros, Zeros) ⇒
  floodfill area ins (((q,d),v_delay 5 P) :: outs') crosses' init
Proof
  (* rpt strip_tac \\ dxrule_then (dxrule_then dxrule) floodfill_perm
  \\ simp [floodfill_def]
  \\ rpt strip_tac \\ first_x_assum dxrule \\ strip_tac
  \\ qexists_tac `s`
  \\ conj_tac >- first_assum ACCEPT_TAC *)
  cheat (* todo *)
QED

Theorem floodfill_teleport:
  floodfill area ins outs crosses init ∧
  PERM outs ((ad,P) :: outs') ⇒
  ∀z.
  floodfill area ins ((mk_dpt ad z, v_teleport z P) :: outs') crosses init
Proof
  cheat
  (* rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm
  \\ simp [floodfill_def]
  \\ rpt strip_tac \\ first_x_assum dxrule \\ strip_tac
  \\ Cases_on `s` \\ rename [`SND (s, dom)`] \\ fs [Once EXISTS_PROD]
  \\ qexists_tac `s` \\ qmatch_goalsub_abbrev_tac `(s, dom')`
  \\ conj_tac >- (
    Cases \\ disch_then assume_tac \\ rename [`assign_sat _ _ (pd,v)`]
    \\ `pd ∈ dom'` by (
      simp [Abbr`dom'`, MEM_MAP, Once EXISTS_PROD]
      \\ CONV_TAC (RAND_CONV $ SCONV [Once EXISTS_PROD])
      \\ fs [] \\ metis_tac [])
    \\ fs [SF DNF_ss] \\ res_tac \\ fs [assign_sat_def]
    \\ `mk_dpt ad z ∈ span dom'` by (irule mem_span_self \\ simp [Abbr`dom'`])
    \\ fs [v_eval_def] \\ strip_tac
    \\ qpat_x_assum `!x. v_eval' _ _ _` $ qspec_then `add_pt z x` assume_tac
    \\ Cases_on `P` \\ fs [v_eval'_def, v_teleport_def]
    \\ Cases_on `r` \\ fs [v_teleport_def]
    \\ Cases_on `ad` \\ fs [mk_dpt_def]
    \\ `∀z x p. add_pt x (add_pt p z) = add_pt (add_pt z x) p ∧
        mk_pt (mk_pt p z) x = mk_pt p (add_pt z x)` by
      (simp [FORALL_PROD, add_pt_def, mk_pt_def] \\ ARITH_TAC)
    \\ simp [])
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rpt strip_tac
  \\ first_x_assum $ drule_at Any \\ impl_tac
  >- (
    irule assign_ext_trans \\ first_x_assum $ irule_at Any
    \\ simp [assign_ext_def, span_subset_iff]
    \\ gvs [SUBSET_DEF, MEM_MAP, PULL_EXISTS]
    \\ rw [] >>> C NTH_GOAL 2 (
      `mk_dpt ad z ∈ dom'` by simp [Abbr`dom'`]
      \\ metis_tac [mk_dpt_in_span, mem_span_self])
    \\ irule mem_span_self \\ simp [Abbr`dom'`, MEM_MAP] \\ metis_tac [])
  \\ disch_then suff_eq_tac \\ cong_tac 2
  \\ Cases_on `ad` \\ simp [floodfill_mod_def, mk_dpt_def]
  \\ cong_tac 2 \\ simp [Once EXTENSION]
  \\ simp [SF DNF_ss] \\ strip_tac \\ cong_tac 2
  \\ Cases_on `q` \\ Cases_on `z` \\ simp [EXISTS_PROD, mk_pt_def]
  \\ eq_tac \\ strip_tac \\ gvs []
  THENL (map qexistsl_tac [[`p_1+q`,`p_2+r''`], [`p_1-q`,`p_2-r''`]])
  \\ (conj_tac >- ARITH_TAC \\ cong_tac 3 \\ simp [] \\ ARITH_TAC) *)
QED

Theorem make_area_2_2 = EVAL ``EVERY (λa. ¬MEM (add_pt (x,y) a) area) (make_area 2 2)``

Theorem pull_perm1_tl:
  PERM ls (a :: ls') ⇒ ∀b. PERM (b :: ls) (a :: b :: ls')
Proof
  metis_tac [PERM_MONO, PERM_SWAP_AT_FRONT, PERM_REFL, PERM_TRANS]
QED

Theorem pull_perm_nil:
  ∀ls. PERM ls ([] ++ ls)
Proof
  simp []
QED

Theorem pull_perm_cons:
  PERM ls (a :: ls') ∧ PERM ls' (ls1 ++ ls2) ⇒ PERM ls ((a :: ls1) ++ ls2)
Proof
  rw [] \\ metis_tac [PERM_MONO, PERM_TRANS]
QED

val _ = export_theory();
