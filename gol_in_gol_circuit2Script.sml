open HolKernel bossLib boolLib Parse;
open gol_simTheory listTheory gol_circuitTheory pred_setTheory
     pairTheory alistTheory arithmeticTheory sortingTheory integerTheory numLib
     dep_rewrite intLib combinTheory rich_listTheory quantHeuristicsTheory;

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

Datatype:
  gate = <| width: num; height: num; lo: mask list; hi: mask list |>
End

Definition gate_wf_def:
  gate_wf (g:gate) ⇔
    g.width ≠ 0 ∧ g.height ≠ 0 ∧
    rectangle g.width g.height (MAP from_mask g.lo) ∧
    rectangle g.width g.height (MAP from_mask g.hi)
End

Definition is_gate_def:
  is_gate (g:gate)
    (ins: (((int # int) # dir) # value) list)
    (outs: (((int # int) # dir) # value) list) ⇔
  (* ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧ *)
  gate_wf g ∧
  ∀env. env_wf env ⇒
    ∀s. LIST_REL (λ(_,v). v_eval env v) ins s ⇒
      ∃s'. LIST_REL (λ(_,v). v_eval env v) outs s' ∧
        ∀z. circuit (make_area g.width g.height)
          (MAP2 (λ((p,d),_) v. (p,d,v z)) ins s)
          (MAP2 (λ((p,d),_) v. (p,d,v z)) outs s')
          [] (from_masks (env 0 z) (g.lo, g.hi))
End

Theorem circuit_perm:
  PERM ins ins' ∧ PERM outs outs' ∧ PERM assrt assrt' ⇒
  (circuit area ins outs assrt init ⇔ circuit area ins' outs' assrt' init)
Proof
  rw [circuit_def] \\ BINOP_TAC
  >- metis_tac [PERM_LIST_TO_SET, PERM_MAP]
  \\ metis_tac [ALL_DISTINCT_PERM, PERM_MAP]
QED

Theorem EVERY2_sym_fwd = SRULE [] $
  Q.ISPECL [`R:α->β->bool`,`flip R:β->α->bool`] $ Q.GENL [`R1`, `R2`] EVERY2_sym;

Theorem EVERY2_trans':
  (∀x y z. R1 x y ∧ R2 y z ⇒ R3 x z) ⇒
  ∀x y z. LIST_REL R1 x y ∧ LIST_REL R2 y z ⇒ LIST_REL R3 x z
Proof
  strip_tac \\ Induct_on `x` \\ Cases_on `y` \\ Cases_on `z` \\ simp [] \\ metis_tac []
QED

Theorem PERM_ZIP_R:
  PERM l1 l2 ∧ LENGTH l2 = LENGTH l3 ⇒
  ∃l4. LENGTH l3 = LENGTH l4 ∧ PERM (ZIP (l1, l3)) (ZIP (l2, l4))
Proof
  `∀l1 l2. PERM l1 l2 ⇒ LENGTH l1 = LENGTH l2 ∧ ∀l3. LENGTH l3 = LENGTH l2 ⇒
      ∃l4. LENGTH l3 = LENGTH l4 ∧ PERM (ZIP (l1, l3)) (ZIP (l2, l4))`
    suffices_by metis_tac []
  \\ HO_MATCH_MP_TAC PERM_IND \\ rw []
  >- (
    Cases_on `l3` \\ gvs []
    \\ first_x_assum drule \\ rw []
    \\ qexists_tac `h::l4` \\ simp [ZIP_def])
  >- (
    Cases_on `l3` \\ gvs []
    \\ Cases_on `t` \\ gvs []
    \\ first_x_assum drule \\ rw []
    \\ qexists_tac `h'::h::l4` \\ simp [ZIP_def, PERM_SWAP_AT_FRONT])
  \\ last_x_assum (qspec_then `l3` mp_tac) \\ rw []
  \\ first_x_assum (qspec_then `l4` mp_tac) \\ rw []
  \\ qexists_tac `l4'` \\ metis_tac [PERM_TRANS]
QED

Theorem PERM_ZIP_R':
  PERM l1 l2 ∧ LENGTH l2 = LENGTH l3 ⇒
  ∃l4. PERM l3 l4 ∧ PERM (ZIP (l1, l3)) (ZIP (l2, l4))
Proof
  strip_tac \\ drule_then drule PERM_ZIP_R \\ rw []
  \\ first_assum $ irule_at Any
  \\ first_assum $ mp_tac o MATCH_MP (Q.ISPEC `SND` PERM_MAP)
  \\ imp_res_tac PERM_LENGTH
  \\ simp [PERM_LENGTH, MAP_ZIP]
QED

Theorem is_gate_perm:
  is_gate g ins outs ∧ PERM ins ins' ∧ PERM outs outs' ⇒
  is_gate g ins' outs'
Proof
  simp [is_gate_def] \\ rw []
  \\ rename [`_ ins' sin'`]
  \\ imp_res_tac PERM_LENGTH
  \\ imp_res_tac LIST_REL_LENGTH
  \\ last_assum $ mp_then (Pos hd) (qspec_then `sin'` mp_tac) PERM_ZIP_R'
    o MATCH_MP (iffLR PERM_SYM)
  \\ rw [] \\ rename [`PERM _ (ZIP (_, sin))`]
  \\ imp_res_tac PERM_LENGTH
  \\ fs [LIST_REL_EVERY_ZIP]
  \\ first_x_assum $ drule_then $ qspec_then `sin` mp_tac
  \\ impl_tac >- (simp [] \\ metis_tac [PERM_EVERY])
  \\ strip_tac \\ rename [`_ (ZIP (_, sout))`]
  \\ qpat_assum `PERM outs _` $ mp_then (Pos hd) drule PERM_ZIP_R'
  \\ strip_tac \\ rename [`_ (ZIP (_, sout'))`]
  \\ imp_res_tac PERM_LENGTH
  \\ qexists_tac `sout'` \\ conj_tac >- metis_tac [PERM_EVERY]
  \\ strip_tac \\ first_x_assum $ qspec_then `z` suff_eqr_tac
  \\ irule circuit_perm \\ simp [ZIP_MAP, MAP2_ZIP]
  \\ metis_tac [PERM_MAP, PERM_SYM]
QED

Theorem env_wf_translate:
  env_wf f ⇒ env_wf (λi a. f i (add_pt x a))
Proof
  rw [env_wf_def, o_DEF, add_pt_assoc]
QED

Definition delay_def:
  delay n a i = if i < n then F else a (i - n:num)
End

Theorem delay_simp:
  (λn. delay k a (k + n)) = a ∧
  (λn. delay k a (n + k)) = a
Proof
  gvs [FUN_EQ_THM,delay_def]
QED

Definition delay'_def:
  delay' (n,env) a i = if i < n then eval_env_kind env i else a (i - n:num)
End

Theorem delay'_eq_delay[simp]:
  delay' (n,Zeros) = delay n
Proof
  rw [FUN_EQ_THM, delay'_def, delay_def, eval_env_kind_def]
QED

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
  is_gate w h
    [((xy1,d1),v1); ((xy2,d2),v2)]
    [((xy3,d3), v_and (v_delay 5 v1) (v_delay 5 v2))] init
Proof
  gvs [is_gate_def] \\ rpt strip_tac
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

Definition instantiate_gate_def:
  instantiate_gate w h ((eaF, eaT), (ebF, ebT)) init =
    <|width := w; height := h;
      lo := instantiate (eaF, ebF) init;
      hi := instantiate (eaT, ebT) init|>
End

Theorem instantiate_gate_simps[simp]:
  (instantiate_gate w h ee init).width = w ∧
  (instantiate_gate w h ee init).height = h
Proof
  PairCases_on `ee` \\ simp [instantiate_gate_def]
QED

Definition simple_gate_def:
  simple_gate w h init =
    <|width := w; height := h; lo := init; hi := init|>
End

Theorem simple_gate_simps[simp]:
  (simple_gate w h init).width = w ∧
  (simple_gate w h init).height = h ∧
  (simple_gate w h init).lo = init ∧
  (simple_gate w h init).hi = init
Proof
  simp [simple_gate_def]
QED

Theorem instantiate_simple:
  instantiate (ea, eb) init = res ⇒
  instantiate_gate w h ((ea, ea), (eb, eb)) init = simple_gate w h res
Proof
  simp [instantiate_gate_def, simple_gate_def]
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

Theorem MAP2_ZIP:
  MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1, l2))
Proof
  qspec_tac (`l2`,`l2`) \\ Induct_on `l1` \\ Cases_on `l2` \\ simp [ZIP_def]
QED

Theorem MAP_ZIP':
  MAP f (ZIP (l1, l2)) = MAP2 (λx y. f (x, y)) l1 l2
Proof
  simp [MAP2_ZIP] \\ cong_tac 2 \\ simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem MAP_MAP2:
  MAP f (MAP2 g l1 l2) = MAP2 (λx y. f (g x y)) l1 l2
Proof
  simp [MAP2_ZIP, MAP_COMPOSE] \\ cong_tac 2 \\ simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem MAP2_CONG_LIST_REL:
  LIST_REL (λx y. f x y = g x y) l1 l2 ⇒ MAP2 f l1 l2 = MAP2 g l1 l2
Proof
  qspec_tac (`l2`,`l2`) \\ Induct_on `l1` \\ Cases_on `l2` \\ simp []
QED

Definition mk_output_env_def:
  mk_output_env env s (da,db) (ea,eb) z = λ(x,n).
    delay' (var_CASE x da db, eval_pair (env 0n z) (var_CASE x ea eb))
      (EL (var_CASE x 0 1) s z) n
End

Theorem v_eval_mk_output_env:
  admissible_ins ins = SOME (da,db') ∧
  (∀x. db' = SOME x ⇒ x = db) ∧
  classify da a = SOME ea ∧
  classify db b = SOME eb ∧
  env_wf env ∧
  LIST_REL (λ(_,_,v). v_eval env (vb_eval ((da,a),db,b) v)) ins s ⇒
  ∀v. admissible_bexpr (da, db') v ⇒
    v_eval env (vb_eval ((da,a),(db,b)) v)
      (λz n. eval (age n (mk_output_env env s (da,db) (ea,eb) z)) v)
Proof
  strip_tac \\ Induct \\ rw [admissible_bexpr_def]
  >- (
    `v_eval env a (HD s) ∧
      (db' = SOME db ⇒ v_eval env b (EL 1 s))` by (
      MAP_EVERY (C qpat_x_assum mp_tac) [`LIST_REL _ _ _`, `admissible_ins _ = _`]
      \\ fs [oneline admissible_ins_def] \\ rpt CASE_TAC \\ rw [] \\ fs [])
    \\ Cases_on `v`
    \\ fs [oneline admissible_bexpr_def, mk_output_env_def]
    THENL [ALL_TAC, Cases_on `db'` \\ gvs []]
    \\ irule v_eval_v_delay' \\ simp [])
  >- (HO_BACKCHAIN_TAC v_eval_v_not \\ rw [])
  >- (HO_BACKCHAIN_TAC v_eval_v_and \\ rw [])
  >- (HO_BACKCHAIN_TAC v_eval_v_or \\ rw [])
QED

Theorem blist_simulation_ok_gate_wf:
  blist_simulation_ok w h ins outs init ⇒
  gate_wf (instantiate_gate w h ee init)
Proof
  strip_tac
  \\ `w ≠ 0 ∧ h ≠ 0 ∧ ∀ee. rectangle w h (MAP from_mask (instantiate ee init))`
    suffices_by (PairCases_on `ee` \\ simp [gate_wf_def, instantiate_gate_def])
  \\ pop_assum mp_tac \\ REWRITE_TAC [blist_simulation_ok_def]
  \\ disch_then (mp_tac o CONJUNCT1) \\ REWRITE_TAC [blist_simple_checks_def]
  \\ simp [rectangle_def, instantiate_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
  \\ rw [] \\ first_x_assum $ dxrule_then (rw o single o SYM)
  \\ POP_ASSUM_LIST kall_tac
  \\ Induct_on `y'`
  \\ simp [blist_length_def, instantiate_row_def, from_mask_def, from_mask_mk]
  \\ rw [] \\ simp [from_mask_mk]
QED

Theorem blist_simulation_ok_imp_circuit:
  blist_simulation_ok w h ins outs init ∧
  admissible_ins ins = SOME (da, db') ∧
  LIST_REL (λ(_,_,v). v_eval env (vb_eval ((da,a),db,b) v)) ins sin ∧
  (∀x. db' = SOME x ⇒ x = db) ∧
  g = instantiate_gate w h (ea,eb) init ⇒
  circuit (make_area w h)
    (MAP2 (λ(p,d,_) v. (p,d,v z)) ins sin)
    (MAP (λ(p,d,v). (p,d, λn.
      eval (age n (mk_output_env env sin (da,db) (ea,eb) z)) v)) outs) []
    (from_masks (env 0 z) (g.lo,g.hi))
Proof
  strip_tac
  \\ qmatch_goalsub_abbrev_tac `age _ env2`
  \\ drule_then (qspec_then `env2` suff_eq_tac o
      MATCH_MP simulation_ok_IMP_circuit) blist_simulation_ok_thm
  \\ cong_tac 1 THENL [cong_tac 2, all_tac]
  >- (
    fs [eval_io_def]
    \\ MAP_EVERY (C qpat_x_assum mp_tac) [`LIST_REL _ ins _`, `admissible_ins _ = _`]
    \\ fs [oneline admissible_ins_def] \\ rpt CASE_TAC
    \\ rw [] \\ rw [] \\ pairarg_tac \\ rw []
    \\ gvs [FUN_EQ_THM, Abbr`env2`, delay'_def, mk_output_env_def])
  >- (
    fs [eval_io_def, MAP2_self] \\ cong_tac 2
    \\ simp [FUN_EQ_THM, FORALL_PROD])
  \\ Cases_on `ea` \\ Cases_on `eb` \\ rename [`((eaF,eaT),(ebF,ebT))`]
  \\ simp [instantiate_gate_def, from_masks_def, MAP_COMPOSE]
  \\ simp [Abbr`env2`, mk_output_env_def, eval_pair_var_CASE]
  \\ `∀ea eb.
        MAP from_mask (instantiate (ea,eb) init) =
        MAP (MAP (eval (λ(x,n). delay'
          (var_CASE x da db, var_CASE x ea eb)
          (EL (var_CASE x 0 1) sin z) n)) ∘ from_blist) init` suffices_by (
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

Theorem blist_simulation_ok_imp_gate:
  blist_simulation_ok w h ins outs init ∧
  admissible_ins ins = SOME (da, db') ∧
  (∀x. db' = SOME x ⇒ x = db) ∧
  w < ^tile ∧ h < ^tile ∧
  classify da a = SOME ea ∧
  classify db b = SOME eb ⇒
  is_gate (instantiate_gate w h (ea, eb) init)
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) ins)
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) outs)
Proof
  rw [is_gate_def, LIST_REL_MAP1, LIST_REL_MAP2]
  >- drule_then irule blist_simulation_ok_gate_wf
  \\ qpat_abbrev_tac `f = λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)`
  \\ qabbrev_tac `s1 = λv z n. eval (age n (mk_output_env env s (da,db) (ea,eb) z)) v`
  \\ qexists_tac `MAP (λ(_,_,v). s1 v) outs` \\ rw [LIST_REL_MAP2]
  >- (
    irule EVERY2_refl \\ simp [FORALL_PROD, Abbr`f`, Abbr`s1`] \\ rw []
    \\ irule v_eval_mk_output_env \\ rpt $ first_assum $ irule_at Any
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ reverse conj_tac >- (
      qpat_x_assum `_ s` suff_eq_tac \\ cong_tac 3
      \\ simp [FUN_EQ_THM, FORALL_PROD])
    \\ last_x_assum mp_tac \\ REWRITE_TAC [blist_simulation_ok_def]
    \\ disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) \\ simp [EVERY_MEM]
    \\ disch_then (drule o CONJUNCT1) \\ simp [])
  \\ drule_then (drule_at_then Any $ drule_then $
      qspecl_then [`z`,`s`,`env`,`eb`,`ea`,`b`,`a`] mp_tac o SRULE [])
    blist_simulation_ok_imp_circuit
  \\ impl_tac >- (
    qpat_x_assum `_ s` suff_eq_tac \\ cong_tac 3
    \\ simp [Abbr`f`, FUN_EQ_THM, FORALL_PROD])
  \\ simp [Abbr`f`, MAP2_MAP_L, MAP2_MAP_R, MAP2_self]
  \\ disch_then suff_eq_tac \\ cong_tac 5 >>> HEADGOAL (cong_tac 1)
  \\ simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem blist_simulation_ok_imp_gate_1:
  blist_simulation_ok w h [(p1,d1,Var A da)] outs init ⇒
  w < ^tile ∧ h < ^tile ⇒
  classify da a = SOME ea ⇒
  is_gate (instantiate_gate w h (ea, ea) init)
    [((p1,d1),a)]
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(da,a)) v)) outs)
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
  is_gate (instantiate_gate w h (ea, eb) init)
    [((p1,d1),a); ((p2,d2),b)]
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) outs)
Proof
  rpt strip_tac
  \\ dxrule_then (dxrule_at_then (Pos (el 6)) $ dxrule_at_then Any $
      qspec_then `SOME db` (irule o SRULE [])) blist_simulation_ok_imp_gate
  \\ simp [admissible_ins_def]
QED

Theorem gate_weaken:
  LIST_REL (λ(pd,v) (pd',v'). pd = pd' ∧ v ⊑ v') outs outs' ∧
  is_gate g ins outs ⇒ is_gate g ins outs'
Proof
  simp [is_gate_def] \\ strip_tac
  \\ fs [] \\ rpt strip_tac
  \\ last_x_assum (dxrule_then dxrule) \\ strip_tac
  \\ qexists_tac `s'` \\ conj_tac
  >- (
    last_x_assum (fn h1 => qpat_x_assum `_ s'` (fn h2 =>
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
  (p ⇒ is_gate g ins [(pd,v_or
    (v_and (v_delay 15 a) (v_or (v_and (v_delay 12 a) (v_not (v_delay 18 b)))
      (v_and (v_not (v_delay 12 a)) (v_and (v_delay 15 b) (v_not (v_delay 18 b))))))
    (v_and (v_not (v_delay 15 a)) (v_or (v_delay 12 a) (v_delay 15 b)))); out]) ⇒
  p ⇒ is_gate g ins [(pd,v_xor (v_delay 15 a) (v_delay 18 b));out]
Proof
  rpt strip_tac \\ first_x_assum dxrule
  \\ strip_tac \\ dxrule_at_then Any irule gate_weaken
  \\ PairCases_on `out` \\ simp []
  \\ Cases_on `a` \\ simp [] \\ Cases_on `b` \\ simp []
  \\ irule Reg_mono \\ simp [] \\ metis_tac []
QED

(* Definition gate_at'_def:
  gate_at' (x,y) (init:mask list # mask list) =
    from_rows (75*x-85, 75*y-85) ARB
End

Definition gate_at_def:
  gate_at p init =
    U {gate_at' (add_pt p (mul_pt (&^tile2) z)) init | z | T}
End *)

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

Definition mega_cell_builder_def:
  mega_cell_builder (gates: ((int # int) # gate) list) env0 =
  iunion (λz:int#int. U (set (MAP (λ(p,g).
    translate_set (mul_pt 75 (mk_pt p z))
      (from_masks (z ∈ env0) (g.lo,g.hi))) gates)))
End

Definition floodfill_run_def:
  floodfill_run (area: (int # int) list) (init: state)
    (ins: (((int # int) # dir) # (int # int -> num -> bool)) set)
    (outs: (((int # int) # dir) # (int # int -> num -> bool)) set) =
  circuit_run
    (iunion (λz. set (MAP (λp. mk_pt p z) area)))
    (iunion (λz. IMAGE (λ((p,d),v). (mk_pt p z, d, v z)) ins))
    (iunion (λz. IMAGE (λ((p,d),v). (mk_pt p z, d, v z)) outs))
    {} init
End

Definition in_range_def:
  in_range (x,y) ⇔
    (x % 2 = 0 ∧ 0 ≤ x ∧ x < &^tile2) ∧
    (y % 2 = 0 ∧ 0 ≤ y ∧ y < &^tile2)
End

Definition gate_at_wf_def:
  gate_at_wf area (p, g) ⇔ gate_wf g ∧
    ∀x. MEM x (make_area g.width g.height) ⇒ MEM (add_pt p x) area
End

Definition floodfill_def:
  floodfill (area: (int # int) list)
    (ins: (((int # int) # dir) # value) list)
    (outs: (((int # int) # dir) # value) list)
    (crosses: ((int # int) # (int # int) # dir) list)
    (gates: ((int # int) # gate) list) ⇔
  EVERY (gate_at_wf area) gates ∧
  EVERY in_range area ∧
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
        floodfill_run area (mega_cell_builder gates (env 0))
          (set (ZIP (MAP FST ins, sin)) ∪
           set (MAP2 (λ(p,_,d) v. ((p,d),v)) crosses scross))
          (set (ZIP (MAP FST outs, sout)) ∪
           set (MAP2 (λ(_,p,d) v. ((p,d), delay 5 ∘ v)) crosses scross))
End

Theorem floodfill_start:
  floodfill [] [] [] [] []
Proof
  rw [floodfill_def, floodfill_run_def, mega_cell_builder_def, circuit_run_empty]
QED

Theorem every_gate_at_wf_mono:
  set l1 ⊆ set l2 ⇒
  EVERY (gate_at_wf l1) init ⇒ EVERY (gate_at_wf l2) init
Proof
  rw [EVERY_MEM] \\ first_x_assum dxrule
  \\ Cases_on `e` \\ fs [gate_at_wf_def, SUBSET_DEF]
QED

Theorem floodfill_add_ins:
  floodfill area ins outs [] init ∧
  is_gate g [((a,d),Exact dl v)] outs' ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  g.width = 1 ∧ g.height = 1 ∧ ¬MEM p area ∧
  ¬MEM (add_pt p a) (MAP (FST ∘ FST) (ins ++ outs)) ⇒
  floodfill (p :: area) (((add_pt p a,d),Exact dl v) :: ins)
    (MAP (λ((a',d'),Q). ((add_pt p a',d'),Q)) outs' ++ outs) []
    ((p, g) :: init)
Proof
  rw [] \\ gvs [floodfill_def]
  \\ simp [floodfill_def] \\ fs [SF DNF_ss]
  \\ conj_tac >- (
    fs [gate_at_wf_def, is_gate_def, make_area_def]
    \\ drule_at_then Any irule every_gate_at_wf_mono \\ simp [])
  \\ conj_tac >- simp [in_range_def]
  \\ qabbrev_tac `p = (&(2*x'):int, &(2*y'):int)`
  \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ simp [LIST_REL_SPLIT1, LIST_REL_MAP1]
  \\ ntac 2 $ first_assum $ irule_at Any
  \\ fs [is_gate_def]
  \\ first_x_assum drule
  \\ simp [PULL_EXISTS, v_eval_def, GSYM FUN_EQ_THM]
  \\ rw []
  \\ irule_at Any EVERY2_mono \\ first_assum $ irule_at Any
  \\ conj_tac >- simp [FORALL_PROD]
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ cheat (* todo *)
QED

Theorem floodfill_perm:
  floodfill area ins outs crosses init ∧
  PERM outs outs' ∧ PERM crosses crosses' ⇒
  floodfill area ins outs' crosses' init
Proof
  simp [floodfill_def] \\ strip_tac
  \\ rw [] \\ first_x_assum dxrule \\ rw []
  \\ first_assum $ irule_at Any
  \\ imp_res_tac PERM_LENGTH
  \\ imp_res_tac LIST_REL_LENGTH
  \\ last_assum $ mp_then (Pos hd) (qspec_then `sout` mp_tac) PERM_ZIP_R'
  \\ rw [] \\ rename [`PERM _ (ZIP (_, sout'))`] \\ qexists_tac `sout'`
  \\ imp_res_tac PERM_LENGTH
  \\ fs [LIST_REL_EVERY_ZIP]
  \\ conj_tac >- metis_tac [PERM_EVERY]
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rw []
  \\ qpat_assum `PERM crosses _` $ mp_then (Pos hd)
    (qspec_then `scross` mp_tac) PERM_ZIP_R' o MATCH_MP (iffLR PERM_SYM)
  \\ rw [] \\ rename [`PERM (ZIP (_, scross')) (ZIP (_, scross))`]
  \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [PERM_SYM])
  \\ imp_res_tac PERM_LENGTH
  \\ first_x_assum (qspec_then `scross` mp_tac) \\ impl_tac
  >- (conj_tac >- metis_tac [] \\ metis_tac [MEM_PERM])
  \\ simp [ZIP_MAP, MAP2_ZIP]
  \\ metis_tac [PERM_LIST_TO_SET, PERM_MAP]
QED

Theorem floodfill_weaken_gen:
  floodfill area ins outs crosses init ∧
  LIST_REL (λ(pd,P) (pd',Q). pd = pd' ∧ P ⊑ Q) outs outs' ⇒
  floodfill area ins outs' crosses init
Proof
  simp [floodfill_def] \\ strip_tac
  \\ rw [] \\ first_x_assum dxrule \\ rw []
  \\ `MAP FST outs = MAP FST outs'` by (
    CONV_TAC $ PATH_CONV "ll" $ REWR_CONV $ SYM LIST_REL_eq
    \\ simp [EVERY2_MAP] \\ drule_at_then Any irule EVERY2_mono
    \\ simp [FORALL_PROD])
  \\ qexistsl_tac [`sin`, `sout`] \\ fs []
  \\ reverse conj_tac >- first_assum ACCEPT_TAC
  \\ fs [SF DNF_ss] \\ rw []
  \\ qpat_x_assum `LIST_REL _ _ sout` (fn h1 =>
    qpat_x_assum `LIST_REL _ outs _` (fn h2 =>
      mp_tac $ CONJ (MATCH_MP EVERY2_sym_fwd h2) h1))
  \\ prim_irule $ SPEC_ALL $ UNDISCH EVERY2_trans'
  \\ simp [FORALL_PROD, v_subset_def]
QED

Theorem floodfill_weaken:
  floodfill area ins outs crosses init ∧
  PERM outs ((pd,Exact (&d) ThisCell) :: outs') ⇒
  floodfill area ins ((pd,Reg d (Cell (0, 0))) :: outs') crosses init
Proof
  strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ POP_ASSUM_LIST (assume_tac o MATCH_MP floodfill_perm o LIST_CONJ o rev)
  \\ irule_at Any floodfill_weaken_gen \\ first_x_assum (irule_at Any)
  \\ simp [EVERY2_refl, FORALL_PROD]
  \\ rw [v_subset_def, v_eval_def, e_cell_def]
  \\ `∃i. (&(n + base):int) − &d = &i` by ARITH_TAC \\ rw []
  \\ cong_tac 2 \\ ARITH_TAC
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

Theorem from_rows_translate_0 =
  GSYM $ SRULE [GSYM int_sub] $ Q.SPECL [`-i`, `-j`] from_rows_translate;

Definition read_mega_cells_def:
  read_mega_cells s =
    { p | add_pt (mul_pt (150 * 21) p) (23 * 75 + 1, 8 * 75 - 1) ∈ s }
End

Theorem from_rows_rectangle:
  rectangle w h rows ∧ (a,b) ∈ from_rows (x,y) rows ⇒
  x ≤ a ∧ a < x + &(150 * w + 20) ∧ y ≤ b ∧ b < y + &(150 * h + 20)
Proof
  simp [rectangle_def] \\ strip_tac
  \\ last_x_assum (simp o single o SYM)
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac `y` \\ Induct_on `rows` \\ simp [from_rows_def]
  \\ reverse (ntac 4 strip_tac)
  \\ `∀x:int. (∀a. x + 1 ≤ a ⇒ x ≤ a) ∧ x ≤ x ∧
    ∀n. x + 1 + &n = x + &SUC n ∧ x < x + &SUC n` by ARITH_TAC
  >- metis_tac []
  \\ last_x_assum (simp o single o SYM)
  \\ qpat_x_assum `_∈_` mp_tac
  \\ qid_spec_tac `x` \\ Induct_on `h` \\ simp [from_row_def]
  \\ Cases_on `h'` \\ simp [from_row_def] \\ metis_tac []
QED

Definition test_mask_def:
  test_mask i End = F ∧
  test_mask i (Allow n m) = (i < n ∨ test_mask (i - n) m) ∧
  test_mask i (Forbid n m) = (n ≤ i ∧ test_mask (i - n) m)
End

Definition majority_def:
  majority a b c = if a then b ∨ c else b ∧ c
End

(*
- lo <= hi  <  q   <  q+w   0          |
+ lo <= q   <= hi  <  q+w   q..hi      | lo
+ lo <= q   <  q+w <= hi    q..q+w-1   | lo
+ hi  <= lo <= q   <  q+w   q..q+w-1   | lo
- q   <  q+w <= lo <= hi    0          |
- hi  <  q   <  q+w <= lo   0          |
+ q   <  lo <= hi  <  q+w   lo..hi     | lo
+ q   <  lo <  q+w <= hi    lo..q+w-1  | lo
+ q   <= hi  <  q+w <= lo   q..hi      | lo+1
+ q   <  q+w <= hi  <= lo   q..q+w-1   | lo+1
+ hi  <= q   <  lo <  q+w   lo..q+w-1  | lo
*)
Definition test_pt_def:
  test_pt gates s (p1:int,p2:int) =
    let lo1 = (p1 + 65) / 150; lo2 = (p2 + 65) / 150 in
    let hi1 = (p1 + 85) / 150; hi2 = (p2 + 85) / 150 in
    let lo1r = lo1 % &^tile; lo2r = lo2 % &^tile in
    let hi1r = hi1 % &^tile; hi2r = hi2 % &^tile in
    EXISTS (λ((q1,q2),g).
      majority (q1 ≤ hi1r) (lo1r < q1 + &g.width) (hi1r < lo1r) ∧
      majority (q2 ≤ hi2r) (lo2r < q2 + &g.height) (hi2r < lo2r) ∧
      let q1d = lo1 / &^tile + (if lo1r < q1 + &g.width then 0 else 1) in
      let q2d = lo2 / &^tile + (if lo2r < q2 + &g.height then 0 else 1) in
      let masks = if s (q1d, q2d) then g.hi else g.lo in
      let row = Num (p1 - (150 * (q1d * &^tile + q1) - 85)) in
      let col = Num (p2 - (150 * (q2d * &^tile + q2) - 85)) in
      test_mask col (EL row masks)
    ) gates
End

Theorem read_mega_cells_build_mega_cells_thm:
  EVERY (gate_at_wf area) gates ∧ EVERY in_range area ⇒
  read_mega_cells (mega_cell_builder gates s) = s
Proof
  simp [EVERY_MEM, gate_at_wf_def, gate_wf_def, Once FORALL_PROD]
  \\ rw [read_mega_cells_def, mega_cell_builder_def, Once EXTENSION,
    MEM_MAP, PULL_EXISTS, Q.INST_TYPE [`:β`|->`:gate`] EXISTS_PROD,
    from_masks_def, translate_set_def]
  \\ qmatch_goalsub_abbrev_tac `sub_pt y`
  \\ HO_BACKCHAIN_TAC $ METIS_PROVE []
    ``(∀z q g. P z q g ⇒ z = x) ∧ ((∃q g. P x q g) ⇔ Q) ⇒
      ((∃z q g. P z q g) ⇔ Q)``
  \\ conj_tac >- (
    `∀z q w h pat.
      w ≠ 0 ∧ h ≠ 0 ∧ rectangle w h pat ∧
      (∀y. MEM y (make_area w h) ⇒ in_range (add_pt q y)) ∧
      sub_pt y (mul_pt 75 (mk_pt q z)) ∈ from_rows (-85,-85) pat ⇒
      z = x` suffices_by metis_tac []
    \\ rw [Abbr`y`] \\ MAP_EVERY PairCases_on [`x`,`q`,`z`] \\ fs [mk_pt_def]
    \\ `∃r0 r1. q0 = 2*r0 ∧ q1 = 2*r1 ∧ 0 ≤ r0 ∧ 0 ≤ r1 ∧
        r0 + &w ≤ &^tile ∧ r1 + &h ≤ &^tile` by (
      `MEM (0,0) (make_area w h) ∧ MEM (2 * &w - 2,2 * &h - 2) (make_area w h)` by
        (simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS] \\ ARITH_TAC)
      \\ res_tac \\ fs [in_range_def] \\ ARITH_TAC)
    \\ drule_then (drule_then strip_assume_tac) from_rows_rectangle \\ gvs []
    \\ ARITH_TAC)
  \\ `∀q. sub_pt y (mul_pt 75 (mk_pt q x)) = sub_pt (1726,599) (mul_pt 75 q)` by
    (rw [Abbr`y`] \\ MAP_EVERY PairCases_on [`x`,`q`] \\ fs [mk_pt_def] \\ ARITH_TAC)
  \\ pop_assum (rw o single)
  \\ CASE_TAC \\ simp []
  \\ cheat (* todo *)
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
  \\ once_rewrite_tac [from_rows_translate_0]
  \\ rewrite_tac [intLib.COOPER_PROVE
       “3150 * i + a - (b + 3150 * j - c) = 3150 * (i - j) + (a - b + c):int”]
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
    val _ = cv_transLib.cv_auto_trans gol_rulesTheory.b2n_def
    val _ = cv_transLib.cv_trans calc_def
    val _ = cv_transLib.cv_trans_rec calc_all_def (
      WF_REL_TAC ‘measure (λxs. 9 - cv_right_depth xs)’ \\ rw []
      \\ gvs [cv_LENGTH_thm,cv_stdTheory.cv_right_depth_def,cvTheory.c2b_def])
    val lemma = prove(
      “calc_all (F::xs) ∧ calc_all (T::xs) ⇔ ∀b. calc_all (b::xs)”,
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
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact 509 Clock)] [] gates
  ⇒
  gol_in_gol (mega_cell_builder gates) (^period * 60) read_mega_cells
Proof
  rw [gol_rulesTheory.gol_in_gol_def] \\ gvs [floodfill_def, SF DNF_ss]
  \\ gvs [FUN_EQ_THM,FORALL_PROD] \\ rw []
  \\ rename [‘FUNPOW step n init (x,y) = _’]
  \\ qabbrev_tac ‘env = λn. FUNPOW step n init’
  \\ ‘env_wf env’ by
   (gvs [env_wf_def,Abbr‘env’] \\ gen_tac \\ PairCases
    \\ simp [GSYM ADD1,FUNPOW_SUC] \\ gvs [nextCell_correct])
  \\ first_x_assum drule \\ strip_tac
  \\ gvs [v_eval_def]
  \\ qmatch_asmsub_rename_tac `floodfill_run _ _
    {(_,latch);(_,clock)} {(_,latch');(_,clock')}`
  \\ `latch = latch' ∧ clock = clock'` by
    (simp [FUN_EQ_THM, e_clock_def] \\ ARITH_TAC)
  \\ gvs [floodfill_run_def, circuit_run_def]
  \\ dxrule run_clear_mods
  \\ impl_tac
  >-
   (simp [can_clear_def]
    \\ gvs [translate_mods_def,EXTENSION,EXISTS_PROD,translate_mod_def,
            circ_mod_def])
  \\ rw []
  \\ gvs [run_def]
  \\ pop_assum $ qspec_then ‘^period * 60 * n’ mp_tac
  \\ strip_tac
  \\ gvs []
  \\ dxrule run_to_clear_mods
  \\ strip_tac
  \\ Cases_on ‘n = 0’
  >- (gvs [Abbr`env`]
    \\ DEP_REWRITE_TAC [read_mega_cells_build_mega_cells_thm] \\ rw [])
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
  \\ cheat
  (* \\ irule (METIS_PROVE [] “~y2 ∧ (x = y1) ⇒ (x ⇔ y1 ∨ y2)”)
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
  is_gate g ins1 outs1 ∧
  PERM outs (del ++ outs') ⇒
  ∀p x' y'.
  (p = (&(2 * x'), &(2 * y')) ∧
  x' + g.width ≤ ^tile ∧ y' + g.height ≤ ^tile ∧
  del = MAP (λ((a, d), P). ((add_pt p a, d), P)) ins1) ∧
  EVERY (λa. ¬MEM (add_pt p a) area) (make_area g.width g.height) ⇒
  floodfill
    (MAP (add_pt p) (make_area g.width g.height) ++ area) ins
    (MAP (λ((a, d), P). ((add_pt p a, d), P)) outs1 ++ outs') crosses
    ((p, g) :: init)
Proof
  rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm \\ gvs []
  \\ simp [floodfill_def] \\ strip_tac \\ fs [SF DNF_ss, MEM_MAP]
  \\ conj_tac >- cheat
  \\ conj_tac >- (
    fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, make_area_def, MEM_FLAT,
      MEM_GENLIST, in_range_def]
    \\ ARITH_TAC)
  \\ qabbrev_tac `p = (&(2*x'):int, &(2*y'):int)`
  \\ rpt strip_tac \\ first_x_assum $ drule_then strip_assume_tac
  \\ dxrule $ iffLR LIST_REL_SPLIT1 \\ rw [LIST_REL_MAP1]
  \\ rename [`_ outs' sout'`, `_ (_ ∘ _) ins1 sin1`]
  \\ first_x_assum $ irule_at Any
  \\ irule_at Any EVERY2_APPEND_suff \\ rw [LIST_REL_MAP1]
  \\ first_x_assum $ irule_at Any
  \\ fs [is_gate_def]
  \\ last_x_assum $ drule_then $ qspec_then `sin1` mp_tac
  \\ impl_tac >- (
    irule EVERY2_mono \\ pop_assum $ irule_at Any
    \\ simp [FORALL_PROD])
  \\ rw [] \\ rename [`_ outs1 sout1`]
  \\ irule_at Any EVERY2_mono \\ first_x_assum $ irule_at Any
  \\ conj_tac >- simp [FORALL_PROD]
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rw []
  \\ first_assum $ drule_all_then assume_tac
  \\ cheat (* todo *)
QED

Theorem floodfill_add_small_gate:
  floodfill area ins outs crosses init ∧
  is_gate g ins1 outs1 ∧
  PERM outs (del ++ outs') ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  g.width = 1 ∧ g.height = 1 ∧ ¬MEM p area ∧
  del = MAP (λ((a,d),P). ((add_pt p a, d), P)) ins1 ⇒
  floodfill (p :: area) ins
    (MAP (λ((a,d),Q). ((add_pt p a,d),Q)) outs1 ++ outs') crosses
    ((p, g) :: init)
Proof
  rw [] \\ dxrule_then (dxrule_then dxrule) floodfill_add_gate
  \\ simp [make_area_def]
QED

Theorem floodfill_add_crossover_gen:
  floodfill area ins outs crosses init ∧
  PERM outs (((p',d1),P) :: outs') ∧
  classify 5 P = SOME ea ∧
  g.width = 1 ∧ g.height = 1 ∧
  (∀env v1 Q v2 z. env_wf env ∧
    classify 5 Q = SOME (Zeros, Zeros) ∧
    v_eval env P v1 ∧ v_eval env Q v2 ⇒
    circuit (make_area 1 1) [(a,d1,v1 z); (b,d2,v2 z)]
      [(a',d1, delay' (5,eval_pair (env 0 z) ea) (v1 z));
       (b',d2, delay 5 (v2 z))] []
      (from_masks (env 0 z) (g.lo,g.hi))) ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  p' = add_pt p a ⇒
  floodfill (p :: area) ins
    (((add_pt p a',d1),v_delay 5 P) :: outs')
    ((add_pt p b, add_pt p b', d2) :: crosses)
    ((p, g) :: init)
Proof
  rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm \\ gvs []
  \\ simp [floodfill_def] \\ strip_tac \\ fs [SF DNF_ss, MEM_MAP]
  \\ conj_tac >- cheat
  \\ conj_tac >- (
    simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS, in_range_def]
    \\ ARITH_TAC)
  \\ qabbrev_tac `p = (&(2*x'):int, &(2*y'):int)`
  \\ rpt strip_tac \\ ntac 2 $ first_x_assum $ drule_then strip_assume_tac
  \\ rename [`_ outs' sout'`, `v_eval _ P v1`]
  \\ ntac 2 $ first_x_assum $ irule_at Any
  \\ dxrule_then (drule_then $ qspecl_then [`0`] mp_tac) v_eval_v_delay'
  \\ rw [] \\ pop_assum $ irule_at Any
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ simp [LIST_LENGTH_COMPARE_SUC, PULL_EXISTS, SF DNF_ss] \\ rw []
  \\ rename [`v_eval _ Q v2`]
  \\ first_x_assum $ dxrule_then $ dxrule_then dxrule
  \\ first_x_assum $ dxrule_at Any \\ rw [make_area_def]
  \\ cheat (* todo *)
QED

Theorem floodfill_add_crossover_l:
  floodfill area ins outs crosses init ∧
  blist_simulation_ok 1 1
    [(a,d1,Var A 5); (b,d2,Var B 5)]
    [(a',d1,Var A 0); (b',d2,Var B 0)] init1 ∧
  PERM outs (((p',d1),P) :: outs') ⇒
  classify 5 P = SOME ea ⇒
  instantiate_gate 1 1 (ea, (Zeros, Zeros)) init1 = g ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  p' = add_pt p a ⇒
  floodfill (p :: area) ins
    (((add_pt p a',d1),v_delay 5 P) :: outs')
    ((add_pt p b, add_pt p b', d2) :: crosses)
    ((p, g) :: init)
Proof
  rpt strip_tac \\ irule floodfill_add_crossover_gen
  \\ rpt $ last_assum $ irule_at Any \\ rw []
  \\ dxrule blist_simulation_ok_imp_circuit
  \\ simp [admissible_ins_def, PULL_EXISTS]
  \\ disch_then $ rev_drule_then $ drule_then $
    qspecl_then [`z`,`Zeros,Zeros`,`ea`] suff_eq_tac
  \\ cong_tac 6 >>> NTH_GOAL (cong_tac 2) 2
  \\ simp [FUN_EQ_THM, mk_output_env_def, eval_pair_def]
QED

Theorem floodfill_add_crossover_r:
  floodfill area ins outs crosses init ∧
  blist_simulation_ok 1 1
    [(a,d1,Var A 5); (b,d2,Var B 5)]
    [(a',d1,Var A 0); (b',d2,Var B 0)] init1 ∧
  PERM outs (((p',d2),P) :: outs') ⇒
  classify 5 P = SOME eb ⇒
  instantiate_gate 1 1 ((Zeros, Zeros), eb) init1 = g ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM p area ∧
  p' = add_pt p b ⇒
  floodfill (p :: area) ins
    (((add_pt p b',d2),v_delay 5 P) :: outs')
    ((add_pt p a, add_pt p a', d1) :: crosses)
    ((p, g) :: init)
Proof
  rpt strip_tac \\ irule floodfill_add_crossover_gen
  \\ rpt $ last_assum $ irule_at Any \\ rw []
  \\ dxrule blist_simulation_ok_imp_circuit
  \\ simp [admissible_ins_def, PULL_EXISTS]
  \\ disch_then $ dxrule_then $ drule_then $
    qspecl_then [`z`,`eb`,`Zeros,Zeros`] suff_eq_tac
  \\ irule circuit_perm \\ simp [PERM_SWAP_AT_FRONT]
  \\ irule $ METIS_PROVE [PERM_SWAP_AT_FRONT, PERM_REFL] ``[b;a] = c ⇒ PERM [a;b] c``
  \\ cong_tac 3 >>> NTH_GOAL (cong_tac 2) 2
  \\ simp [FUN_EQ_THM, mk_output_env_def, eval_pair_def]
QED

Theorem floodfill_finish_crossover:
  floodfill area ins outs crosses init ∧
  PERM outs (((p,d),P) :: outs') ∧
  PERM crosses ((p,q,d) :: crosses') ⇒
  classify 5 P = SOME (Zeros, Zeros) ⇒
  floodfill area ins (((q,d),v_delay 5 P) :: outs') crosses' init
Proof
  rpt strip_tac \\ dxrule_then (dxrule_then dxrule) floodfill_perm
  \\ simp [floodfill_def]
  \\ rpt strip_tac \\ first_x_assum dxrule \\ strip_tac
  \\ rename [`sout = v::sout'`] \\ gvs []
  \\ ntac 2 $ first_assum $ irule_at Any \\ simp []
  \\ qexists_tac `delay 5 ∘ v`
  \\ conj_tac >- (
    MAP_EVERY (C qpat_x_assum mp_tac) [`_ v`, `_ = _`]
    \\ POP_ASSUM_LIST kall_tac \\ rw []
    \\ dxrule_then (dxrule_then $ qspecl_then [`0`] mp_tac) v_eval_v_delay'
    \\ rw [] \\ pop_assum suff_eq_tac \\ cong_tac 1
    \\ simp [FUN_EQ_THM, delay_def, delay'_def,
      eval_pair_def, eval_env_kind_def])
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rw []
  \\ first_x_assum (qspec_then `v::scross` mp_tac)
  \\ simp [SF DNF_ss]
  \\ disch_then $ drule_then drule
  \\ cheat (* todo *)
QED

Theorem floodfill_teleport:
  floodfill area ins outs crosses init ∧
  PERM outs ((ad,P) :: outs') ⇒
  ∀z.
  floodfill area ins ((mk_dpt ad z, v_teleport z P) :: outs') crosses init
Proof
  rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm
  \\ simp [floodfill_def]
  \\ rpt strip_tac \\ first_x_assum dxrule \\ strip_tac
  \\ rename [`sout = v::sout'`] \\ gvs []
  \\ ntac 2 $ first_assum $ irule_at Any \\ simp []
  \\ qexists_tac `v ∘ add_pt z`
  \\ conj_tac >- (
    qpat_x_assum `_ v` mp_tac \\ POP_ASSUM_LIST kall_tac
    \\ Cases_on `P` \\ fs [v_eval_def, v_eval'_def, v_teleport_def]
    \\ Cases_on `r` \\ fs [v_teleport_def]
    \\ metis_tac [add_pt_comm, add_pt_assoc])
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rw [] \\ first_x_assum $ drule_all_then suff_eq_tac
  \\ Cases_on `ad` \\ simp [floodfill_run_def, mk_dpt_def]
  \\ cong_tac 3 \\ simp [Once EXTENSION]
  \\ simp [SF DNF_ss] \\ strip_tac \\ cong_tac 4
  \\ Cases_on `q` \\ Cases_on `z` \\ simp [EXISTS_PROD, mk_pt_def]
  \\ eq_tac \\ strip_tac \\ gvs []
  THENL (map qexistsl_tac [[`p_1+q`,`p_2+r''`], [`p_1-q`,`p_2-r''`]])
  \\ (conj_tac >- ARITH_TAC \\ cong_tac 1 \\ simp [] \\ ARITH_TAC)
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
