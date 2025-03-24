open HolKernel bossLib boolLib Parse;
open gol_simTheory gol_sim_okTheory listTheory gol_circuitTheory pred_setTheory
     pairTheory alistTheory arithmeticTheory sortingTheory integerTheory numLib
     dep_rewrite intLib combinTheory rich_listTheory quantHeuristicsTheory
     gol_in_gol_paramsLib gol_io_stepTheory;

val _ = new_theory "gol_in_gol_circuit2";

(* val metis_tac = Timeout.apply (Time.fromMilliseconds 2000) o metis_tac
val fs = Timeout.apply (Time.fromMilliseconds 2000) o fs
val simp = Timeout.apply (Time.fromMilliseconds 2000) o simp
val rw = Timeout.apply (Time.fromMilliseconds 2000) o rw *)

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
    (MAP2 (λv (_,p,d,_). (p,d,v)) s1 outs) init ∧
  LIST_REL (λv (is,p,d,Q).
    (∀ i. MEM i is ⇒ EL i (MAP2 (λv (_,_,P). P v) s0 ins)) ⇒ Q v) s1 outs
End

Datatype:
  avalue = Cell (int # int) | RNot avalue
    | RAnd avalue avalue | ROr avalue avalue | RXor avalue avalue;
  evalue = Clock | NotClock | ThisCell | ThisCellClock | ThisCellNotClock;
  value = Approx num avalue | Exact int evalue | Fail
End

Definition r_eval_def[simp]:
  (r_eval env (Cell p) ⇔ env p) ∧
  (r_eval env (RNot v) ⇔ ¬r_eval env v) ∧
  (r_eval env (RAnd v1 v2) ⇔ r_eval env v1 ∧ r_eval env v2) ∧
  (r_eval env (ROr v1 v2) ⇔ r_eval env v1 ∨ r_eval env v2) ∧
  (r_eval env (RXor v1 v2) ⇔ r_eval env v1 ≠ r_eval env v2)
End

Definition e_clock_def:
  e_clock (n:int) ⇔ n % ^periodZ < ^pulseZ
End

Definition e_cell_def:
  e_cell env (n:int) ⇔ 0 ≤ n ∧ env (Num n DIV ^periodN)
End

Definition e_eval_def[simp]:
  e_eval env Clock = e_clock ∧
  e_eval env NotClock = (λn. ¬e_clock n) ∧
  e_eval env ThisCell = e_cell env ∧
  e_eval env ThisCellClock = (λn. e_clock n ∧ e_cell env n) ∧
  e_eval env ThisCellNotClock = (λn. e_cell env n ∧ ¬e_clock n)
End

Definition v_eval'_def[simp]:
  (v_eval' env (Approx d rv) s ⇔
    ∀ n. d ≤ n MOD ^periodN ⇒ s n = r_eval (env (n DIV ^periodN)) rv) ∧
  (v_eval' env (Exact d ev) s ⇔ s = (λn. e_eval (λi. env i (0, 0)) ev (&n - d))) ∧
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
  v_delay n (Approx i v) = Approx (n + i) v ∧
  v_delay n (Exact i v) = Exact (&n + i) v ∧
  v_delay n Fail = Fail
End

Theorem v_delay_0[simp]:
  v_delay 0 v = v
Proof
  Cases_on `v` \\ rw []
QED

Definition v_teleport_def:
  v_teleport p (Approx i (Cell a)) = Approx i (Cell (add_pt a p)) ∧
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
  (v_and (Approx d1 rv1) (Approx d2 rv2) = Approx (MAX d1 d2) (RAnd rv1 rv2)) ∧
  (v_and (Exact d1 ThisCell) (Exact d2 NotClock) =
    if d2 ≤ d1 ∧ d1 ≤ d2 + ^pulseZ then
      Exact d2 ThisCellNotClock
    else Fail) ∧
  (v_and (Exact d1 Clock) (Approx d2 v2) =
    if v2 = nextCell ∧ &d2 ≤ d1 + ^periodZ ∧ d1 ≤ -^pulseZ then
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
  (v_or (Approx d1 rv1) (Approx d2 rv2) = Approx (MAX d1 d2) (ROr rv1 rv2)) ∧
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
  v_not (Approx d1 v1) = Approx d1 (RNot v1) ∧
  v_not _ = Fail
End

Definition v_xor_def[simp]:
  v_xor (Approx d1 v1) (Approx d2 v2) = Approx (MAX d1 d2) (RXor v1 v2) ∧
  v_xor _ _ = Fail
End

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

Theorem Reg_mono:
  na ≤ nb ∧ (∀env. r_eval env va ⇔ r_eval env vb) ⇒ Approx na va ⊑ Approx nb vb
Proof
  simp [v_subset_def, v_eval_def] \\ metis_tac [LE_TRANS]
QED

Definition env_wf_def:
  env_wf (env:num->state) ⇔
    ∀t x. env (t + 1) x = r_eval (env t ∘ add_pt x) nextCell
End

Definition mk_pt_def[compute]:
  mk_pt a z ⇔ add_pt a (mul_pt (^tile2Z) z)
End

val pt_arith_tac: tactic =
  POP_ASSUM_LIST kall_tac \\ rw []
  \\ (fn g as (asm, t) => (
    MAP_EVERY (C tmCases_on []) (
      filter (fn v => snd (dest_var v) = ``:int#int``) (free_varsl (t::asm)) @
      find_maximal_termsl (fn tm => rator tm ~~ ``dir_to_xy`` handle _ => false) t)
    \\ fs [mk_pt_def] \\ ARITH_TAC
  ) g);

Theorem mk_pt_0[simp]:
  mk_pt p (0,0) = p
Proof
  pt_arith_tac
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

Theorem span_sn_eq_span_sn:
  span {(a,d)} = span {(a',d')} ⇔ d = d' ∧ ∃z. a' = mk_pt a z
Proof
  simp [Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS, span_def, mk_dpt_def]
  \\ `∀z z'. mk_pt (mk_pt a z) z' = mk_pt a (add_pt z z') ∧
      mk_pt a z' = mk_pt (mk_pt a z) (sub_pt z' z)` by pt_arith_tac
  \\ metis_tac [mk_pt_0]
QED

Definition vb_eval_def[simp,compute]:
  (vb_eval ((da, a), _) (Var A d) = v_delay (da - d) a) ∧
  (vb_eval (_, (db, b)) (Var B d) = v_delay (db - d) b) ∧
  (vb_eval env (Not x)   = v_not (vb_eval env x)) ∧
  (vb_eval env (And x y) = v_and (vb_eval env x) (vb_eval env y)) ∧
  (vb_eval env (Or x y)  = v_or  (vb_eval env x) (vb_eval env y)) ∧
  (vb_eval _ _ = Fail)
End

Definition classify_clock_def[compute]:
  (classify_clock da T d =
    if &da + d + ^pulseZ ≤ ^periodZ ∧ -^periodZ ≤ d then
      if 0 ≤ d ∨ &da + d + ^pulseZ ≤ 0 then SOME Zeros else
        SOME (Pulse
          (if 0 ≤ &da + d then Num (&da + d) else 0)
          (MIN da (Num (&da + d + ^pulseZ))))
    else NONE) ∧
  (classify_clock da F d =
    if &da + d ≤ 0 ∧ -^periodZ ≤ d then
      SOME (Pulse
        (if 0 ≤ &da + d + ^pulseZ then Num (&da + d + ^pulseZ) else 0)
        (MIN da (Num (&da + d + ^periodZ))))
    else NONE)
End

Definition classify_this_def[compute]:
  classify_this da d =
    if 0 < d then SOME Zeros else
    if 0 < d + ^periodZ then
      SOME (Pulse (if 0 ≤ &da + d then Num (&da + d) else 0) da)
    else NONE
End

Definition and_this_def[compute]:
  and_this Zeros = Zeros ∧
  (and_this (Pulse a b) = PulseThis a b) ∧
  (and_this (PulseThis a b) = PulseThis a b)
End

Definition classify_def[compute]:
  classify _ (Approx _ _) = SOME Zeros ∧
  classify da (Exact d Clock) = classify_clock da T d ∧
  classify da (Exact d NotClock) = classify_clock da F d ∧
  classify da (Exact d ThisCell) =
    OPTION_MAP and_this (classify_this da d) ∧
  classify da (Exact d ThisCellClock) =
    OPTION_MAP and_this (classify_clock da T d) ∧
  classify da (Exact d ThisCellNotClock) =
    OPTION_MAP and_this (classify_clock da F d) ∧
  classify _ Fail = NONE
End

Definition from_init_def:
  from_init env init =
    from_rows (-85,-85) (MAP (MAP (eval (λ_. env)) o from_blist) init)
End

Datatype:
  gate = <| width: num; height: num; init: blist list |>
End

Definition gate_wf_def:
  gate_wf (g:gate) ⇔
    g.width ≠ 0 ∧ g.height ≠ 0 ∧
    g.width < ^tileN ∧ g.height < ^tileN ∧
    rectangle g.width g.height (MAP from_blist g.init)
End

Definition gate_ports_wf_def:
  gate_ports_wf w h ins outs ⇔
    (∀p d. (p,d) ∈ ins ⇒ MEM (add_pt p (dir_to_xy d)) (make_area w h) ∧
                        ¬MEM (sub_pt p (dir_to_xy d)) (make_area w h)) ∧
    ∀p d. (p,d) ∈ outs ⇒ MEM (sub_pt p (dir_to_xy d)) (make_area w h) ∧
                        ¬MEM (add_pt p (dir_to_xy d)) (make_area w h)
End

Definition is_gate_def:
  is_gate (g:gate)
    (ins: (((int # int) # dir) # value) list)
    (outs: (((int # int) # dir) # value) list) ⇔
  gate_wf g ∧
  gate_ports_wf g.width g.height (set (MAP FST ins)) (set (MAP FST outs)) ∧
  ∀env. env_wf env ⇒
    ∀s. LIST_REL (λ(_,v). v_eval env v) ins s ⇒
      ∃s'. LIST_REL (λ(_,v). v_eval env v) outs s' ∧
        ∀z. circuit (make_area g.width g.height)
          (MAP2 (λ((p,d),_) v. (p,d,v z)) ins s)
          (MAP2 (λ((p,d),_) v. (p,d,v z)) outs s')
          (from_init (env 0 z) g.init)
End

Theorem circuit_perm:
  PERM ins ins' ∧ PERM outs outs' ⇒
  (circuit area ins outs init ⇔ circuit area ins' outs' init)
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
  \\ ho_match_mp_tac PERM_IND \\ rw []
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

Theorem env_wf_translate:
  env_wf f ⇒ env_wf (λi a. f i (add_pt x a))
Proof
  rw [env_wf_def, o_DEF, add_pt_assoc]
QED

Definition delay_def:
  delay n a i = if i < n then F else a (i - n:num)
End

Definition delay'_def:
  delay' (n,ee,env) a i =
    if i < n then eval (λ_. env) (eval_env_kind ee i) else a (i - n:num)
End

Theorem delay'_eq_delay[simp]:
  delay' (n,Zeros,env) = delay n
Proof
  rw [FUN_EQ_THM, delay'_def, delay_def, eval_env_kind_def]
QED

Theorem eval_classify_clock:
  classify_clock da b d = SOME ea ∧ n < da ⇒
  &n − (&da + d) < ^periodZ ∧
  (eval env (eval_env_kind ea n) ⇔ e_clock (&n − (&da + d)) = b) ∧
  (e_clock (&n − (&da + d)) ∨ ¬b ⇒ 0 ≤ &n − (&da + d))
Proof
  Cases_on `b` \\ rw [classify_clock_def, e_clock_def] \\ rw [eval_env_kind_def] \\ TRY ARITH_TAC
QED

Theorem eval_classify_this:
  classify_this da d = SOME ea ∧ n < da ⇒
  &n − (&da + d) < ^periodZ ∧
  (eval env (eval_env_kind ea n) ⇔ 0 ≤ &n − (&da + d))
Proof
  rw [classify_this_def] \\ rw [eval_env_kind_def, e_cell_def] \\ ARITH_TAC
QED

Theorem e_cell_init:
  i < ^periodZ ⇒ (∀env. e_cell env i ⇔ 0 ≤ i ∧ env 0)
Proof
  rw [e_cell_def] \\ Cases_on `0 ≤ i` \\ rw [] \\ AP_TERM_TAC \\ ARITH_TAC
QED

Theorem v_eval'_v_delay':
  classify da a = SOME ea ∧ v_eval' env a s ∧ k ≤ da ⇒
  v_eval' env (v_delay (da - k) a) (λi. delay' (da,ea,env 0 (0,0)) s (k + i))
Proof
  gvs [oneline v_delay_def] \\ CASE_TAC \\ rw [FUN_EQ_THM]
  \\ gvs [v_eval_def, delay'_def]
  >- (`da ≤ i + k ∧ n ≤ (i + k - da) MOD ^periodN ∧
      (i + k − da) DIV ^periodN = i DIV ^periodN` by ARITH_TAC
    \\ simp [])
  \\ reverse (rw []) >- (AP_TERM_TAC \\ ARITH_TAC)
  \\ `&n − (&(da − k) + i) = &(k + n) − (&da + i)` by ARITH_TAC
  \\ `∀ee n. eval (λ_. env 0 (0,0)) (eval_env_kind (and_this ee) n) ⇔
      env 0 (0,0) ∧ eval (λ_. env 0 (0,0)) (eval_env_kind ee n)` by (
    Cases \\ rw [and_this_def, eval_env_kind_def])
  \\ Cases_on `e` \\ gvs [classify_def]
  \\ FIRST (map (drule_then $ drule_then $
      qspec_then `λ_. env 0 (0,0)` strip_assume_tac)
    [eval_classify_clock, eval_classify_this])
  \\ drule e_cell_init \\ strip_tac \\ fs []
  \\ rw [eval_env_kind_def] \\ metis_tac []
QED

Theorem v_eval_v_delay':
  classify da a = SOME ea ∧ v_eval env a s ∧ k ≤ da ⇒
  v_eval env (v_delay (da - k) a) (λz i. delay' (da,ea,env 0 z) (s z) (k + i))
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
  \\ `k ≤ n ∧ (n − k) DIV 586 = n DIV 586` by ARITH_TAC
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
  (* v_and (Exact i Clock) (Approx n nextCell) = Exact i ThisCellClock *)
  >- (rw [FUN_EQ_THM] \\ Cases_on `e_clock (&n' − i)` \\ rw []
    \\ DEP_ASM_REWRITE_TAC [] \\ gvs [e_clock_def, e_cell_def] \\ rw []
    >- ARITH_TAC
    \\ `∃k. i = -&k` by ARITH_TAC \\ gvs [INT_ADD]
    \\ `(k + n') DIV ^periodN = n' DIV ^periodN + 1` by ARITH_TAC
    \\ fs [env_wf_def]
    \\ cong_tac 2 \\ simp [FUN_EQ_THM, FORALL_PROD])
  (* v_and (Exact i' ThisCell) (Exact i NotClock) = Exact d2 ThisCellNotClock *)
  >- (rw [FUN_EQ_THM] \\ Cases_on `e_clock (&n − i)` \\ rw []
    \\ gvs [e_cell_def, e_clock_def] \\ reverse (Cases_on `0 ≤ i`)
    >- (`22 ≤ &n - i` by ARITH_TAC
      \\ `∃k. i = -&k ∧ ∃j. &n − i' = &j` by ARITH_TAC \\ gvs [INT_ADD]
      \\ cong_tac 2 \\ ARITH_TAC)
    \\ `(∃k. i = &k) ∧ ∃k'. i' = &k'` by ARITH_TAC \\ gvs [INT_SUB, INT_SUB_LE]
    \\ `∀m:int. ^periodZ * m ≤ &n − &k ⇔ ^periodZ * m ≤ &n − &k'` by ARITH_TAC
    \\ pop_assum (qspec_then `&(m:num)` (assume_tac o GEN ``m:num`` o SRULE []))
    \\ first_assum (qspec_then `0` mp_tac) \\ simp [NoAsms] \\ rw []
    \\ gvs [INT_SUB, INT_SUB_LE] \\ Cases_on `k' ≤ n` \\ gvs [INT_SUB, INT_SUB_LE]
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
  >- (rw [FUN_EQ_THM] \\ Cases_on `e_clock (&n − i)` \\ rw [])
QED

Theorem v_eval_v_or:
  v_eval env v1 a1 ∧ v_eval env v2 a2 ⇒
  v_eval env (v_or v1 v2) (λz n. a1 z n ∨ a2 z n)
Proof
  rw [v_eval_def] \\ metis_tac [v_eval'_v_or]
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
    delay' (var_CASE x da db, var_CASE x ea eb, env 0n z)
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

Theorem blist_simulation_ok_gate_ports_wf:
  blist_simulation_ok w h ins outs init ⇒
  gate_ports_wf w h (set (MAP (λ(p,d,_). (p,d)) ins)) (set (MAP (λ(p,d,_). (p,d)) outs))
Proof
  rewrite_tac [blist_simulation_ok_def]
  \\ disch_then (mp_tac o CONJUNCT1)
  \\ simp [blist_simple_checks_def, EVERY_MEM, gate_ports_wf_def, MEM_MAP, PULL_EXISTS,
      Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD,
      Q.INST_TYPE [`:α` |-> `:dir`] EXISTS_PROD]
  \\ ntac 6 strip_tac \\ first_x_assum drule \\ simp []
QED

Theorem blist_simulation_ok_gate_wf:
  blist_simulation_ok w h ins outs init ∧ w < ^tileN ∧ h < ^tileN ⇒
  gate_wf (gate w h (instantiate ee init))
Proof
  strip_tac \\ simp [gate_wf_def]
  \\ qpat_x_assum `_ init` mp_tac \\ rewrite_tac [blist_simulation_ok_def]
  \\ disch_then (mp_tac o CONJUNCT1) \\ rewrite_tac [blist_simple_checks_def]
  \\ simp [rectangle_def, instantiate_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
  \\ rw [] \\ first_x_assum $ dxrule_then (rw o single o SYM)
  \\ POP_ASSUM_LIST kall_tac
  \\ Induct_on `y'`
  \\ simp [blist_length_def, instantiate_row_def, from_blist_def]
QED

Theorem blist_simulation_ok_imp_circuit:
  blist_simulation_ok w h ins outs init ∧
  admissible_ins ins = SOME (da, db') ∧
  LIST_REL (λ(_,_,v). v_eval env (vb_eval ((da,a),db,b) v)) ins sin ∧
  (∀x. db' = SOME x ⇒ x = db) ⇒
  circuit (make_area w h)
    (MAP2 (λ(p,d,_) v. (p,d,v z)) ins sin)
    (MAP (λ(p,d,v). (p,d, λn.
      eval (age n (mk_output_env env sin (da,db) (ea,eb) z)) v)) outs)
    (from_init (env 0 z) (instantiate (ea,eb) init))
Proof
  strip_tac
  \\ qmatch_goalsub_abbrev_tac `age _ env2`
  \\ drule_then (qspec_then `env2` suff_eq_tac o
      MATCH_MP simulation_ok_IMP_circuit) blist_simulation_ok_thm
  \\ cong_tac 1 >>> HEADGOAL (cong_tac 1)
  >- (
    fs [eval_io_def]
    \\ MAP_EVERY (C qpat_x_assum mp_tac) [`LIST_REL _ ins _`, `admissible_ins _ = _`]
    \\ fs [oneline admissible_ins_def] \\ rpt CASE_TAC
    \\ rw [] \\ rw [] \\ pairarg_tac \\ rw []
    \\ gvs [FUN_EQ_THM, Abbr`env2`, delay'_def, mk_output_env_def])
  >- (
    fs [eval_io_def, MAP2_self] \\ cong_tac 2
    \\ simp [FUN_EQ_THM, FORALL_PROD])
  \\ simp [MAP_COMPOSE, Abbr`env2`, mk_output_env_def]
  \\ qmatch_goalsub_abbrev_tac `eval env3`
  \\ rw [MAP_COMPOSE, from_init_def, instantiate_def] \\ cong_tac 1
  \\ irule MAP_CONG \\ rw []
  \\ last_x_assum mp_tac \\ rewrite_tac [blist_simulation_ok_def]
  \\ disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) \\ simp [EVERY_MEM]
  \\ disch_then (dxrule o CONJUNCT2)
  \\ `∀v. admissible_bexpr (da,db') v ⇒
      eval (λ_. env 0 z) (subst (instantiate_var (ea,eb)) v) =
      eval env3 v` suffices_by (
    Induct_on `x` \\ simp [admissible_row_def, instantiate_row_def, from_blist_def])
  \\ Induct \\ simp [admissible_bexpr_def, instantiate_var_def,
    subst_def, eval_build_Not, eval_build_If]
  \\ Cases \\ simp [admissible_bexpr_def, instantiate_var_def,
    Abbr`env3`, delay'_def]
  \\ Cases_on `db'` \\ rw []
QED

Theorem blist_simulation_ok_imp_gate:
  blist_simulation_ok w h ins outs init ∧
  admissible_ins ins = SOME (da, db') ∧
  (∀x. db' = SOME x ⇒ x = db) ∧
  w < ^tileN ∧ h < ^tileN ∧
  classify da a = SOME ea ∧
  classify db b = SOME eb ⇒
  is_gate (gate w h (instantiate (ea, eb) init))
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) ins)
    (MAP (λ(p,d,v). ((p,d),vb_eval ((da,a),(db,b)) v)) outs)
Proof
  rw [is_gate_def, LIST_REL_MAP1, LIST_REL_MAP2]
  >- (drule_then irule blist_simulation_ok_gate_wf \\ rw [])
  >- (drule blist_simulation_ok_gate_ports_wf
    \\ simp [MAP_COMPOSE]
    \\ disch_then suff_eq_tac \\ cong_tac 4
    \\ simp [FUN_EQ_THM, FORALL_PROD])
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
    \\ last_x_assum mp_tac \\ rewrite_tac [blist_simulation_ok_def]
    \\ disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) \\ simp [EVERY_MEM]
    \\ disch_then (drule o CONJUNCT1) \\ simp [])
  \\ drule_then (drule_at_then Any $ drule_then $
      qspecl_then [`z`,`s`,`env`,`eb`,`ea`,`b`,`a`] mp_tac o SRULE [])
    blist_simulation_ok_imp_circuit
  \\ impl_tac >- (
    qpat_x_assum `_ s` suff_eq_tac \\ cong_tac 3
    \\ simp [Abbr`f`, FUN_EQ_THM, FORALL_PROD])
  \\ simp [Abbr`f`, MAP2_MAP_L, MAP2_MAP_R, MAP2_self]
  \\ disch_then suff_eq_tac \\ cong_tac 4 >>> HEADGOAL (cong_tac 1)
  \\ simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem blist_simulation_ok_imp_gate_1:
  blist_simulation_ok w h [(p1,d1,Var A da)] outs init ⇒
  w < ^tileN ∧ h < ^tileN ⇒
  classify da a = SOME ea ⇒
  is_gate (gate w h (instantiate (ea, ea) init))
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
  w < ^tileN ∧ h < ^tileN ⇒
  classify da a = SOME ea ∧
  classify db b = SOME eb ⇒
  is_gate (gate w h (instantiate (ea, eb) init))
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
  \\ `MAP FST outs = MAP FST outs'` by (
    CONV_TAC $ PATH_CONV "ll" $ REWR_CONV $ SYM LIST_REL_eq
    \\ simp [EVERY2_MAP] \\ drule_at_then Any irule EVERY2_mono
    \\ simp [FORALL_PROD])
  \\ fs [] \\ rpt strip_tac
  \\ last_x_assum (dxrule_then dxrule) \\ strip_tac
  \\ qexists_tac `s'` \\ conj_tac
  >- (
    last_x_assum (fn h1 => qpat_x_assum `_ s'` (fn h2 =>
      mp_tac (CONJ (MATCH_MP EVERY2_sym_fwd h1) h2)))
    \\ prim_irule $ SPEC_ALL $ UNDISCH EVERY2_trans'
    \\ simp [FORALL_PROD, v_subset_def])
  \\ pop_assum suff_eqr_tac \\ cong_tac 4
  \\ `MAP2 (λ(p,d) v. (p,d,v z)) (MAP FST outs) s' =
      MAP2 (λ(p,d) v. (p,d,v z)) (MAP FST outs') s'` by simp []
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

Definition to_tiling_def:
  to_tiling st env0 =
  iunion (λz:int#int.
    translate_set (mul_pt (75 * ^tile2Z) z)
      (st (z ∈ env0)))
End

Definition union_gates_def:
  union_gates (gates: ((int # int) # gate) list) b =
  U (set (MAP (λ(p,g).
    translate_set (mul_pt 75 p) (from_init b g.init)) gates))
End

Definition in_range_def:
  in_range (x,y) ⇔
    (x % 2 = 0 ∧ 0 ≤ x ∧ x < ^tile2Z) ∧
    (y % 2 = 0 ∧ 0 ≤ y ∧ y < ^tile2Z)
End

Theorem in_range_unique:
  in_range (mk_pt a z) ∧ in_range (mk_pt a z') ⇒ z = z'
Proof
  MAP_EVERY PairCases_on [`a`,`z`,`z'`]
  \\ simp [in_range_def, mk_pt_def] \\ ARITH_TAC
QED

Definition gate_at_wf_def:
  gate_at_wf area (p, g) ⇔ gate_wf g ∧
    ∀x. MEM x (make_area g.width g.height) ⇒ MEM (add_pt p x) area
End

Theorem every_gate_at_wf_mono:
  set l1 ⊆ set l2 ⇒
  EVERY (gate_at_wf l1) init ⇒ EVERY (gate_at_wf l2) init
Proof
  rw [EVERY_MEM] \\ first_x_assum dxrule
  \\ Cases_on `e` \\ fs [gate_at_wf_def, SUBSET_DEF]
QED

Theorem gate_at_wf_bounded:
  gate_at_wf area ((q0,q1),g) ∧ EVERY in_range area ⇒
  ∃r0 r1. q0 = 2*r0 ∧ q1 = 2*r1 ∧ 0 ≤ r0 ∧ 0 ≤ r1 ∧
  r0 + &g.width ≤ ^tileZ ∧ r1 + &g.height ≤ ^tileZ
Proof
  rw [gate_at_wf_def, gate_wf_def, EVERY_MEM, FORALL_PROD]
  \\ `MEM (0,0) (make_area g.width g.height) ∧
      MEM (2 * &g.width - 2,2 * &g.height - 2) (make_area g.width g.height)` by
    (simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS] \\ ARITH_TAC)
  \\ res_tac \\ res_tac \\ fs [in_range_def] \\ ARITH_TAC
QED

Theorem add_sub_pt_assoc =
  SRULE [] $ Q.INST [`c` |-> `neg_pt c`] add_pt_assoc;

Theorem add_pt_left_comm:
  add_pt a (add_pt b c) = add_pt b (add_pt a c)
Proof
  pt_arith_tac
QED

Theorem add_pt_right_comm:
  add_pt (add_pt a b) c = add_pt (add_pt a c) b
Proof
  pt_arith_tac
QED

Theorem sub_add_pt_comm:
  sub_pt (add_pt a b) c = add_pt (sub_pt a c) b
Proof
  pt_arith_tac
QED

Theorem add_sub_pt_comm:
  add_pt a (sub_pt b c) = sub_pt (add_pt a b) c
Proof
  pt_arith_tac
QED

Theorem sub_mk_pt_assoc:
  sub_pt (mk_pt a z) b = mk_pt (sub_pt a b) z
Proof
  pt_arith_tac
QED

Theorem mk_mk_pt_assoc:
  mk_pt (mk_pt a z) z' = mk_pt a (add_pt z z')
Proof
  pt_arith_tac
QED

Theorem neg_pt_inj[simp]:
  neg_pt a = neg_pt b ⇔ a = b
Proof
  pt_arith_tac
QED

Theorem sub_mk_pt_eq_add_neg:
  sub_pt a (mk_pt b z) = mk_pt (sub_pt a b) (neg_pt z)
Proof
  pt_arith_tac
QED

Theorem add_mk_pt_assoc_l:
  add_pt (mk_pt a z) b = mk_pt (add_pt a b) z
Proof
  pt_arith_tac
QED

Theorem add_mk_pt_assoc_r:
  add_pt a (mk_pt b z) = mk_pt (add_pt a b) z
Proof
  pt_arith_tac
QED

Theorem sub_pt_right_comm:
  sub_pt (sub_pt a b) c = sub_pt (sub_pt a c) b
Proof
  pt_arith_tac
QED

Theorem ALL_DISTINCT_MAP_of_MAP:
  ALL_DISTINCT (MAP f ls) ∧
  (∀x y. MEM x ls ∧ MEM y ls ∧ g x = g y ⇒ f x = f y) ⇒
  ALL_DISTINCT (MAP g ls)
Proof
  Induct_on `ls` \\ rw [MAP, ALL_DISTINCT, MEM_MAP, SF DNF_ss] \\ metis_tac []
QED

Definition floodfill_io_wf_def:
  floodfill_io_wf area ins outs ⇔
  (∀a d v z. ((a,d),v) ∈ ins ∧
    MEM (sub_pt (mk_pt a z) (dir_to_xy d)) area ⇒
    ∃z'. ((mk_pt a z',d),λi. v (add_pt i z')) ∈ outs) ∧
  (∀a d v z. ((a,d),v) ∈ outs ∧
    MEM (add_pt (mk_pt a z) (dir_to_xy d)) area ⇒
    ∃z'. ((mk_pt a z',d),λi. v (add_pt i z')) ∈ ins)
End

Definition floodfill_run_def:
  floodfill_run (area: (int # int) list) (init: state)
    (ins: (((int # int) # dir) # (int # int -> num -> bool)) list)
    (outs: (((int # int) # dir) # (int # int -> num -> bool)) list) ⇔
  EVERY in_range area ∧
  (∀a d v. MEM ((a,d),v) ins ⇒ MEM (add_pt a (dir_to_xy d)) area) ∧
  (∀a d v. MEM ((a,d),v) outs ⇒ ∃z. MEM (mk_pt (sub_pt a (dir_to_xy d)) z) area) ∧
  ALL_DISTINCT (MAP (λ((a,d),v). span {(a,d)}) ins) ∧
  ALL_DISTINCT (MAP (λ((a,d),v). span {(a,d)}) outs) ∧
  (floodfill_io_wf area (set ins) (set outs) ⇒
  circuit_run
    (iunion (λz. set (MAP (λp. mk_pt p z) area)))
    (iunion (λz. set (MAP (λ((p,d),v). (mk_pt p z, d, v z)) ins)))
    (iunion (λz. set (MAP (λ((p,d),v). (mk_pt p z, d, v z)) outs)))
    init)
End

Definition floodfill_gate_wf_def:
  floodfill_gate_wf g ins1 outs1 init ⇔
  g.width < ^tileN ∧ g.height < ^tileN ∧
  gate_ports_wf g.width g.height (set (MAP FST ins1)) (set (MAP FST outs1)) ∧
  (∀z. circuit (make_area g.width g.height)
    (MAP (λ((a,d),v). (a,d,v z)) ins1)
    (MAP (λ((a,d),v). (a,d,v z)) outs1)
    (from_init (init z) g.init))
End

Theorem floodfill_run_add_gate:
  ∀ins1 outs1 ins outs init.
  floodfill_gate_wf g ins1 outs1 init ∧
  (∃x y. p = (&(2*x),&(2*y)) ∧ x + g.width ≤ ^tileN ∧ y + g.height ≤ ^tileN) ∧
  EVERY (λa. ¬MEM (add_pt p a) area) (make_area g.width g.height) ∧
  floodfill_run area (to_tiling (union_gates gates) init) ins outs
  ⇒
  floodfill_run (MAP (add_pt p) (make_area g.width g.height) ⧺ area)
    (to_tiling (union_gates ((p,g)::gates)) init)
    (MAP (λ((a,d),v). ((add_pt p a,d),v)) ins1 ++ ins)
    (MAP (λ((a,d),v). ((add_pt p a,d),v)) outs1 ++ outs)
Proof
  simp [floodfill_run_def, floodfill_gate_wf_def, gate_ports_wf_def, circuit_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [] \\ qabbrev_tac `p = (&(2*x):int,&(2*y):int)`
  \\ pop_assum (fn h => POP_ASSUM_LIST (fn hs => MAP_EVERY assume_tac (h::rev hs)))
  \\ `∀a. MEM a (make_area g.width g.height) ⇒ in_range (add_pt p a)` by (
    simp [Abbr`p`, FORALL_PROD, make_area_def, MEM_FLAT, MEM_GENLIST,
      PULL_EXISTS, in_range_def] \\ ARITH_TAC)
  \\ qabbrev_tac `s = make_area g.width g.height`
  \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM,
      Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
  \\ `∀a z z'. MEM (mk_pt a z) s ⇒ ¬MEM (mk_pt (add_pt p a) z') area` by (
    rpt strip_tac \\ res_tac
    \\ `add_pt p (mk_pt a z) = mk_pt (add_pt p a) z` by pt_arith_tac
    \\ pop_assum (fs o single)
    \\ dxrule_then drule in_range_unique \\ strip_tac \\ gvs [])
  \\ rw []
  >- metis_tac [add_pt_assoc]
  >- metis_tac [add_pt_assoc]
  >- metis_tac [add_sub_pt_comm, mk_pt_0]
  >- metis_tac [add_sub_pt_comm]
  >- (
    fs [ALL_DISTINCT_APPEND, MAP_COMPOSE]
    \\ reverse conj_tac >- (
      simp [MEM_MAP, PULL_EXISTS, Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD,
        span_sn_eq_span_sn]
      \\ rpt strip_tac \\ res_tac \\ res_tac
      \\ fs [add_pt_assoc, add_mk_pt_assoc_l]
      \\ `z = (0,0)` by metis_tac [in_range_unique, mk_pt_0]
      \\ gvs [])
    \\ first_x_assum $ qspec_then `(0,0)` $ mp_then (Pos hd) irule ALL_DISTINCT_MAP_of_MAP
    \\ simp [Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD, span_sn_eq_span_sn] \\ rw []
    \\ ntac 2 $ last_assum dxrule \\ pop_assum mp_tac
    \\ MAP_EVERY PairCases_on [`p_1'`,`p_1`,`z`]
    \\ gvs [mk_pt_def, Abbr`p`, Abbr`s`]
    \\ Cases_on `dir_to_xy p_2` \\ drule dir_to_xy_bounded
    \\ simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS]
    \\ ARITH_TAC)
  >- (
    fs [ALL_DISTINCT_APPEND, MAP_COMPOSE]
    \\ reverse conj_tac >- (
      simp [MEM_MAP, PULL_EXISTS, Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD,
        span_sn_eq_span_sn]
      \\ rpt strip_tac \\ res_tac \\ res_tac
      \\ fs [add_sub_pt_assoc, sub_mk_pt_assoc, mk_mk_pt_assoc]
      \\ `add_pt z z' = (0,0)` by metis_tac [in_range_unique, mk_pt_0]
      \\ gvs [])
    \\ first_x_assum $ qspec_then `(0,0)` $ mp_then (Pos hd) irule ALL_DISTINCT_MAP_of_MAP
    \\ simp [Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD, span_sn_eq_span_sn] \\ rw []
    \\ ntac 2 $ last_assum dxrule \\ pop_assum mp_tac
    \\ MAP_EVERY PairCases_on [`p_1'`,`p_1`,`z`]
    \\ gvs [mk_pt_def, Abbr`p`, Abbr`s`]
    \\ Cases_on `dir_to_xy p_2` \\ drule dir_to_xy_bounded
    \\ simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS]
    \\ ARITH_TAC)
  \\ qpat_x_assum `_ ⇒ _` mp_tac \\ impl_tac
  >- (simp [floodfill_io_wf_def] \\ rpt conj_tac
    \\ rw []
    THENL map (fn h => h suffices_by (fs [floodfill_io_wf_def] \\ metis_tac [])) [
      `∀v z. ¬MEM ((mk_pt a z,d),v) (MAP (λ((a,d),v). ((add_pt p a,d),v)) outs1)`,
      `∀v z. ¬MEM ((mk_pt a z,d),v) (MAP (λ((a,d),v). ((add_pt p a,d),v)) ins1)`]
    \\ rw [MEM_MAP, Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
    \\ pop_assum (assume_tac o GSYM)
    \\ strip_tac \\ rpt $ first_x_assum drule \\ rpt strip_tac
    \\ rpt $ first_x_assum drule \\ rpt strip_tac
    \\ rfs [add_sub_pt_comm, sub_mk_pt_assoc, add_pt_assoc, add_mk_pt_assoc_l]
    \\ metis_tac [in_range_unique])
  \\ `∀z. circuit_run (translate_set (mk_pt p z) (set s))
      (translate_port (mk_pt p z) (set (MAP (λ((a,d),v). (a,d,v z)) ins1)))
      (translate_port (mk_pt p z) (set (MAP (λ((a,d),v). (a,d,v z)) outs1)))
      (translate_set (mul_pt 75 (mk_pt p z)) (from_init (init z) g.init))` by (
    gen_tac
    \\ qpat_x_assum `!z. circuit_run _ _ _ _` $ qspec_then `z` strip_assume_tac
    \\ `FST (mk_pt p z) % 2 = 0 ∧ SND (mk_pt p z) % 2 = 0` by (
      PairCases_on `z` \\ fs [mk_pt_def, Abbr`p`] \\ ARITH_TAC)
    \\ drule_all circuit_run_translate \\ simp [])
  \\ pop_assum (fn h => mp_tac $ SRULE [h] $
    HO_PART_MATCH (lhand o lhand) circuit_run_compose_bigunion (concl h))
  \\ qpat_x_assum `!z. circuit_run _ _ _ _` kall_tac \\ impl_tac
  >- (rw []
    >- (simp [DISJOINT_ALT] \\ rpt strip_tac
      \\ res_tac \\ fs [add_sub_pt_comm, sub_mk_pt_eq_add_neg]
      \\ metis_tac [in_range_unique, neg_pt_inj])
    \\ `F` suffices_by rw []
    \\ qpat_x_assum `z ≠ z'` mp_tac \\ rw []
    \\ fs [MEM_MAP]
    \\ MAP_EVERY PairCases_on [`y'`,`p'`,`z`,`z'`]
    \\ gvs [mk_pt_def, Abbr`p`, Abbr`s`]
    \\ last_assum drule \\ pop_assum mp_tac
    \\ Cases_on `dir_to_xy d` \\ drule dir_to_xy_bounded
    \\ simp [make_area_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS]
    \\ ARITH_TAC)
  \\ rw [] \\ dxrule_then dxrule circuit_run_compose_union \\ impl_tac
  >- (
    conj_tac >- (
      fs [DISJOINT_ALT, MEM_MAP, PULL_EXISTS] \\ rpt strip_tac
      \\ ntac 2 $ first_x_assum drule \\ rpt strip_tac
      \\ first_x_assum drule_all \\ fs [sub_mk_pt_assoc, add_mk_pt_assoc_r]
      \\ `mk_pt (add_pt p (sub_pt p' (mk_pt p z'))) z' = p'` by pt_arith_tac
      \\ `z = z'` by metis_tac [in_range_unique]
      \\ gvs [])
    \\ simp [FORALL_AND_THM, PULL_EXISTS, MEM_MAP,
      Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
    \\ fs [EVERY_MEM] \\ rw []
    >- (
      `∀v z. ¬MEM ((mk_pt p_1 z,d),v) outs` by (
        rpt strip_tac \\ res_tac \\ res_tac
        \\ fs [sub_mk_pt_assoc, add_mk_pt_assoc_r, mk_mk_pt_assoc]
        \\ `∀p'. mk_pt (add_pt p (sub_pt p' (mk_pt p z'))) z =
            mk_pt p' (sub_pt z z')` by pt_arith_tac
        \\ pop_assum (fs o single)
        \\ dxrule_all in_range_unique \\ strip_tac \\ gvs [])
      \\ `∃z a. mk_pt p_1 z = add_pt p a ∧ MEM ((a,d),λi. p_2' (add_pt i z)) outs1` by (
        fs [floodfill_io_wf_def, MEM_MAP, Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
        \\ qmatch_asmsub_abbrev_tac `MEM y' s`
        \\ `add_pt p y' = sub_pt (mk_pt p_1 (sub_pt z z')) (dir_to_xy d)` by
          (qunabbrev_tac `y'` \\ pt_arith_tac)
        \\ metis_tac [])
      \\ qexistsl_tac [`sub_pt z z''`, `λi. p_2' (add_pt i z'')`] \\ simp []
      \\ pop_assum suff_eq_tac \\ cong_tac 6
      \\ pop_assum mp_tac \\ pt_arith_tac)
    >- (
      `∀v z. ¬MEM ((mk_pt p_1 z,d),v) ins` by (
        rpt strip_tac \\ res_tac \\ res_tac
        \\ fs [sub_mk_pt_assoc, add_mk_pt_assoc_l, add_mk_pt_assoc_r]
        \\ `∀p'. mk_pt (add_pt p (sub_pt p' (mk_pt p z'))) z =
            mk_pt p' (sub_pt z z')` by pt_arith_tac
        \\ pop_assum (fs o single)
        \\ dxrule_all in_range_unique \\ strip_tac \\ gvs [])
      \\ `∃z a. mk_pt p_1 z = add_pt p a ∧ MEM ((a,d),λi. p_2' (add_pt i z)) ins1` by (
        fs [floodfill_io_wf_def, MEM_MAP, Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
        \\ qmatch_asmsub_abbrev_tac `MEM y' s`
        \\ `add_pt p y' = add_pt (mk_pt p_1 (sub_pt z z')) (dir_to_xy d)` by
          (qunabbrev_tac `y'` \\ pt_arith_tac)
        \\ metis_tac [])
      \\ qexistsl_tac [`sub_pt z z''`, `λi. p_2' (add_pt i z'')`] \\ simp []
      \\ pop_assum suff_eq_tac \\ cong_tac 6
      \\ pop_assum mp_tac \\ pt_arith_tac)
    >- (
      `∃z'. MEM ((mk_pt p' (sub_pt z' z),d),(λi. p_2' (add_pt i z'))) outs ∨
          ∃a. mk_pt p' (sub_pt z' z) = add_pt p a ∧ MEM ((a,d),(λi. p_2' (add_pt i z'))) outs1` by (
        `mk_pt (add_pt p (sub_pt p' (mk_pt p z))) (sub_pt z z') = mk_pt p' (neg_pt z')` by pt_arith_tac
        \\ `sub_pt (mk_pt p' (neg_pt z')) (dir_to_xy d) = p''` by (simp [sub_mk_pt_assoc] \\ pt_arith_tac)
        \\ `∀z'. mk_pt (add_pt p (sub_pt p' (mk_pt p z))) z' = mk_pt p' (sub_pt z' z)` by pt_arith_tac
        \\ fs [floodfill_io_wf_def, MEM_MAP, Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
        \\ metis_tac [])
      >- (first_assum $ irule_at Any
        \\ qexists_tac `sub_pt z z''` \\ simp [] \\ pt_arith_tac)
      \\ fs [sub_mk_pt_eq_add_neg]
      \\ `mk_pt (sub_pt p' (dir_to_xy d)) (neg_pt z') = p''` by (simp [] \\ pt_arith_tac)
      \\ qpat_x_assum `_ = mk_pt _ _` kall_tac \\ gvs []
      \\ `sub_pt (mk_pt p' (sub_pt z'' z)) p = a` by (simp [] \\ pt_arith_tac)
      \\ qpat_x_assum `_ = add_pt _ _` kall_tac \\ gvs [sub_mk_pt_assoc]
      \\ res_tac \\ res_tac
      \\ `∀d. add_pt p (sub_pt (sub_pt p' p) d) = sub_pt p' d` by pt_arith_tac
      \\ fs [add_mk_pt_assoc_l, add_mk_pt_assoc_r, sub_mk_pt_assoc]
      \\ dxrule_all in_range_unique \\ disch_then (fs o single))
    >- (
      `∃z'. MEM ((mk_pt p' (sub_pt z' z),d),(λi. p_2' (add_pt i z'))) ins ∨
          ∃a. mk_pt p' (sub_pt z' z) = add_pt p a ∧ MEM ((a,d),(λi. p_2' (add_pt i z'))) ins1` by (
        `mk_pt (add_pt p (sub_pt p' (mk_pt p z))) (sub_pt z z') = mk_pt p' (neg_pt z')` by pt_arith_tac
        \\ `add_pt (mk_pt p' (neg_pt z')) (dir_to_xy d) = p''` by (simp [add_mk_pt_assoc_l] \\ pt_arith_tac)
        \\ `∀z'. mk_pt (add_pt p (sub_pt p' (mk_pt p z))) z' = mk_pt p' (sub_pt z' z)` by pt_arith_tac
        \\ fs [floodfill_io_wf_def, MEM_MAP, Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
        \\ fs [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
        \\ metis_tac [])
      >- (first_assum $ irule_at Any
        \\ qexists_tac `sub_pt z z''` \\ simp [] \\ pt_arith_tac)
      \\ fs [sub_mk_pt_eq_add_neg]
      \\ `mk_pt (add_pt p' (dir_to_xy d)) (neg_pt z') = p''` by (simp [] \\ pt_arith_tac)
      \\ qpat_x_assum `_ = mk_pt _ _` kall_tac \\ gvs []
      \\ `sub_pt (mk_pt p' (sub_pt z'' z)) p = a` by (simp [] \\ pt_arith_tac)
      \\ qpat_x_assum `_ = add_pt _ _` kall_tac \\ gvs [sub_mk_pt_assoc]
      \\ res_tac \\ res_tac
      \\ `∀d. add_pt p (add_pt (sub_pt p' p) d) = add_pt p' d` by pt_arith_tac
      \\ fs [add_mk_pt_assoc_l, add_mk_pt_assoc_r, sub_mk_pt_assoc]
      \\ dxrule_all in_range_unique \\ disch_then (fs o single)))
  \\ simp []
  \\ disch_then suff_eq_tac
  \\ cong_tac 1 >>> HEADGOAL (cong_tac 1) >>> HEADGOAL (cong_tac 1)
  >- (
    `∀x y z. x = mk_pt (add_pt p y) z ⇔ y = sub_pt x (mk_pt p z)` by pt_arith_tac
    \\ simp [Once EXTENSION, MEM_MAP, PULL_EXISTS] \\ metis_tac [])
  >>> C NTH_GOAL 3 (
    `∀x p z. sub_pt (sub_pt x (mul_pt (75 * ^tile2Z) z)) (mul_pt 75 p) =
      sub_pt x (mul_pt 75 (mk_pt p z))` by pt_arith_tac
    \\ fs [to_tiling_def, union_gates_def, Once EXTENSION, MEM_MAP,
      PULL_EXISTS, Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
    \\ rw [IN_DEF] \\ metis_tac [])
  \\ simp [Once EXTENSION, MEM_MAP, PULL_EXISTS, translate_port_def,
    Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD,
    Q.INST_TYPE [`:α` |-> `:dir`] FORALL_PROD,
    Q.INST_TYPE [`:α` |-> `:γ#δ`] EXISTS_PROD]
  \\ `∀a z. sub_pt (mk_pt (add_pt p a) z) (mk_pt p z) = a ∧
            mk_pt (add_pt p (sub_pt a (mk_pt p z))) z = a` by pt_arith_tac
  \\ metis_tac []
QED

Theorem floodfill_io_wf_union:
  floodfill_io_wf area ins outs ⇒
  floodfill_io_wf area (s ∪ ins) (s ∪ outs)
Proof
  `∀a z. mk_pt (mk_pt a z) (neg_pt z) = a` by pt_arith_tac
  \\ simp [floodfill_io_wf_def]
  \\ strip_tac \\ rpt conj_tac \\ rpt gen_tac
  \\ (reverse strip_tac >- metis_tac [])
  \\ qexists_tac `(0,0)` \\ simp [ETA_THM]
QED

Theorem iunion_union:
  iunion (λz. a z ∪ b z) = iunion a ∪ iunion b
Proof
  simp [Once EXTENSION] \\ metis_tac []
QED

Theorem floodfill_run_cancel:
  floodfill_run area init (del ++ ins) (del ++ outs) ⇒
  floodfill_run area init ins outs
Proof
  simp [floodfill_run_def, ALL_DISTINCT_APPEND] \\ strip_tac
  \\ fs [iunion_union, MEM_MAP, PULL_EXISTS, span_sn_eq_span_sn,
    Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD]
  \\ conj_tac >- metis_tac []
  \\ conj_tac >- metis_tac []
  \\ strip_tac
  \\ qpat_x_assum `_ ⇒ _` mp_tac \\ impl_tac
  >- (irule floodfill_io_wf_union \\ rw [])
  \\ strip_tac \\ drule circuit_run_internalise
  \\ disch_then $ qspec_then
    `iunion (λz. set (MAP (λ((p,d),v). (mk_pt p z,d,v z)) del))`
    (suff_eq_tac o SRULE [])
  \\ `∀a b z z'. mk_pt a z = mk_pt b z' ⇒ b = mk_pt a (sub_pt z z')` by pt_arith_tac
  \\ cong_tac 2
  \\ DEP_REWRITE_TAC [prove(``DISJOINT a b ⇒ a ∪ b DIFF a = b``,
    simp [Once EXTENSION, SUBSET_DEF, DISJOINT_ALT] \\ metis_tac [])]
  \\ simp [DISJOINT_ALT, PULL_EXISTS, MEM_MAP,
    Q.INST_TYPE [`:α` |-> `:γ#δ`] FORALL_PROD]
  \\ metis_tac []
QED

Theorem floodfill_run_perm:
  floodfill_run area init ins outs ∧
  PERM ins ins' ∧ PERM outs outs' ⇒
  floodfill_run area init ins' outs'
Proof
  strip_tac \\ last_x_assum suff_eq_tac
  \\ simp [floodfill_run_def, LIST_TO_SET_MAP]
  \\ metis_tac [MEM_PERM, PERM_LIST_TO_SET, PERM_MAP, ALL_DISTINCT_PERM]
QED

Definition floodfill_def:
  floodfill (area: (int # int) list)
    (ins: (((int # int) # dir) # value) list)
    (outs: (((int # int) # dir) # value) list)
    (crosses: ((int # int) # (int # int) # dir) list)
    (gates: ((int # int) # gate) list) ⇔
  EVERY (gate_at_wf area) gates ∧
  ∀env. env_wf env ⇒
    ∃sin sout.
      LIST_REL (λ(_,v). v_eval env v) ins sin ∧
      LIST_REL (λ(_,v). v_eval env v) outs sout ∧
      ∀scross.
        LENGTH crosses = LENGTH scross ∧
        (∀s. MEM s scross ⇒ ∃v.
          classify 5 v = SOME Zeros ∧
          v_eval env v s) ⇒
        floodfill_run area (to_tiling (union_gates gates) (env 0))
          (ZIP (MAP FST ins, sin) ++
           MAP2 (λ(p,_,d) v. ((p,d),v)) crosses scross)
          (ZIP (MAP FST outs, sout) ++
           MAP2 (λ(_,p,d) v. ((p,d), delay 5 ∘ v)) crosses scross)
End

Theorem floodfill_start:
  floodfill [] [] [] [] []
Proof
  rw [floodfill_def, floodfill_run_def, to_tiling_def, union_gates_def, circuit_run_empty]
QED

Theorem floodfill_add_ins:
  floodfill area ins outs [] gates ∧
  is_gate g [((a,d),Exact dl v)] outs' ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tileN ∧ y' < ^tileN ∧
  g.width = 1 ∧ g.height = 1 ∧ ¬MEM p area ∧
  ¬MEM (add_pt p a) (MAP (FST ∘ FST) (ins ++ outs)) ⇒
  floodfill (p :: area) (((add_pt p a,d),Exact dl v) :: ins)
    (MAP (λ((a',d'),Q). ((add_pt p a',d'),Q)) outs' ++ outs) []
    ((p, g) :: gates)
Proof
  rw [] \\ gvs [floodfill_def]
  \\ simp [floodfill_def] \\ fs [SF DNF_ss]
  \\ conj_tac >- (
    fs [gate_at_wf_def, is_gate_def, make_area_def]
    \\ drule_at_then Any irule every_gate_at_wf_mono \\ simp [])
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
  \\ imp_res_tac LIST_REL_LENGTH
  \\ DEP_REWRITE_TAC [GSYM ZIP_APPEND]
  \\ drule_at_then Any (qspecl_then [`p`,`g`,
      `[((a,d),(λz n. e_eval (λi. env i z) v (&n − dl)))]`,
      `ZIP (MAP FST outs',s')`] mp_tac) floodfill_run_add_gate
  \\ impl_tac >- (
    fs [make_area_def, floodfill_gate_wf_def, MAP_ZIP]
    \\ reverse conj_tac >- simp [Abbr`p`]
    \\ fs [ZIP_MAP, MAP2_ZIP, MAP_COMPOSE, o_DEF, LAMBDA_PROD])
  \\ PairCases_on `p`
  \\ fs [GSYM INSERT_SING_UNION, ZIP_MAP, MAP2_ZIP, MAP_COMPOSE,
    o_DEF, LAMBDA_PROD, make_area_def]
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
  \\ rw []
  \\ qpat_assum `PERM crosses _` $ mp_then (Pos hd)
    (qspec_then `scross` mp_tac) PERM_ZIP_R' o MATCH_MP (iffLR PERM_SYM)
  \\ rw [] \\ rename [`PERM (ZIP (_, scross')) (ZIP (_, scross))`]
  \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [PERM_SYM])
  \\ imp_res_tac PERM_LENGTH
  \\ first_x_assum (qspec_then `scross` mp_tac) \\ impl_tac
  >- (conj_tac >- metis_tac [] \\ metis_tac [MEM_PERM])
  \\ simp [ZIP_MAP, MAP2_ZIP]
  \\ strip_tac \\ drule_then irule floodfill_run_perm
  \\ metis_tac [PERM_CONG, PERM_REFL, PERM_MAP]
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
  floodfill area ins ((pd,Approx d (Cell (0, 0))) :: outs') crosses init
Proof
  strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ POP_ASSUM_LIST (assume_tac o MATCH_MP floodfill_perm o LIST_CONJ o rev)
  \\ irule_at Any floodfill_weaken_gen \\ first_x_assum (irule_at Any)
  \\ simp [EVERY2_refl, FORALL_PROD]
  \\ rw [v_subset_def, v_eval_def, e_cell_def]
  \\ `∃i. (&n:int) − &d = &i` by ARITH_TAC \\ rw []
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
       io_steps k (clear_mods m) n s t ⇒
       FUNPOW step k s = t ∧
       (k ≠ 0 ⇒ t ∩ (m (n + k − 1)).assert_area = (m (n + k − 1)).assert_content)’
  >- (rw [] \\ res_tac \\ gvs [])
  \\ Induct \\ gvs [io_steps_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [io_step_def,clear_mods_def,clear_mod_def]
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

Theorem from_row_lower_bound:
  (a,b) ∈ from_row (x,y) row ⇒ x ≤ a ∧ y = b
Proof
  qid_spec_tac `x` \\ Induct_on `row` \\ simp [from_row_def]
  \\ `∀x:int. (∀a. x + 1 ≤ a ⇒ x ≤ a) ∧ x ≤ x` by ARITH_TAC
  \\ Cases_on `h` \\ simp [from_row_def] \\ metis_tac []
QED

Theorem from_rows_lower_bound:
  (a,b) ∈ from_rows (x,y) rows ⇒ x ≤ a ∧ y ≤ b
Proof
  qid_spec_tac `y` \\ Induct_on `rows` \\ simp [from_rows_def]
  \\ `∀x:int. (∀a. x + 1 ≤ a ⇒ x ≤ a) ∧ x ≤ x ∧
    ∀n. x + 1 + &n = x + &SUC n ∧ x < x + &SUC n` by ARITH_TAC
  \\ metis_tac [from_row_lower_bound]
QED

Definition rectangle'_def:
  rectangle' w h rows ⇔ LENGTH rows = h ∧ EVERY (λrow. LENGTH row = w) rows
End

Theorem rectangle_eq_rectangle':
  rectangle w h rows ⇔ rectangle' (150 * w + 20) (150 * h + 20) rows
Proof
  simp [rectangle_def, rectangle'_def]
QED

Theorem from_rows_rectangle':
  rectangle' w h rows ∧ (a,b) ∈ from_rows (x,y) rows ⇒
  x ≤ a ∧ a < x + &w ∧ y ≤ b ∧ b < y + &h
Proof
  simp [rectangle'_def] \\ strip_tac
  \\ last_x_assum (simp o single o SYM)
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac `y` \\ Induct_on `rows` \\ simp [from_rows_def]
  \\ `∀x:int. (∀a. x + 1 ≤ a ⇒ x ≤ a) ∧ x ≤ x ∧
    ∀n. x + 1 + &n = x + &SUC n ∧ x < x + &SUC n` by ARITH_TAC
  \\ reverse (ntac 4 strip_tac)
  >- metis_tac []
  \\ last_x_assum (simp o single o SYM)
  \\ qpat_x_assum `_∈_` mp_tac
  \\ qid_spec_tac `x` \\ Induct_on `h` \\ simp [from_row_def]
  \\ Cases_on `h'` \\ simp [from_row_def] \\ metis_tac []
QED

Definition test_blist_def:
  test_blist i Nil = False ∧
  test_blist i (Cell b m) = (if i = 0 then b else test_blist (i - 1) m) ∧
  test_blist i (Falses n m) = (if i < n then False else test_blist (i - n) m)
End

Definition test_blists_def:
  test_blists (row,col) ls = case oEL col ls of
    | NONE => False
    | SOME l => test_blist row l
End

Theorem from_row_iff_test_blist:
  (q0 + &i,q1) ∈ from_row (q0,q1) (MAP (eval env) (from_blist m)) ⇔
  eval env (test_blist i m)
Proof
  MAP_EVERY qid_spec_tac [`i`,`q0`]
  \\ Induct_on `m` \\ simp [from_row_def, from_blist_def, test_blist_def]
  THENL [
    Induct \\ simp [from_row_def]
    \\ Cases_on `i` \\ simp [ARITH_PROVE ``(q:int) + &(SUC n) = q + 1 + &n``]
    \\ pop_assum $ qspecl_then [`q0 + 1`, `n'`] (rw o single o SYM),
    rpt gen_tac \\ Cases_on `eval env b0` \\ simp [from_row_def]
    \\ Cases_on `i` \\ simp [ARITH_PROVE ``(q:int) + &(SUC n) = q + 1 + &n``]]
  \\ metis_tac [from_row_lower_bound, ARITH_PROVE ``¬((q:int) + 1 ≤ q)``]
QED

Theorem from_rows_iff_test_blists:
  (q0 + &i,q1 + &j) ∈ from_rows (q0,q1) (MAP (MAP (eval env) ∘ from_blist) ls) ⇔
  eval env (test_blists (i,j) ls)
Proof
  MAP_EVERY qid_spec_tac [`q1`,`j`] \\ simp [test_blists_def]
  \\ Induct_on `ls` \\ reverse (rw [from_rows_def, oEL_def])
  >- metis_tac [from_row_lower_bound,
    ARITH_PROVE ``x ≠ 0 ⇒ (q:int) + 1 + &(x-1) = q + &x ∧ q + &x ≠ q``]
  \\ irule $ METIS_PROVE [] ``¬b ∧ (a ⇔ c) ⇒ (a ∨ b ⇔ c)`` \\ conj_tac
  >- metis_tac [from_rows_lower_bound, ARITH_PROVE ``¬((q:int) + 1 ≤ q)``]
  \\ irule from_row_iff_test_blist
QED

Definition union_blist_def[induction=union_blist_ind]:
  union_blist _ Nil ls acc = blist_rev acc ls ∧
  union_blist m (Falses n ls1) ls acc = union_blist (m + n) ls1 ls acc ∧
  union_blist m (Cell a ls1) ls acc = union_blist' m a ls1 ls acc ∧
  union_blist' m a ls1 Nil acc = blist_rev acc Nil ∧
  union_blist' m a ls1 (Falses n ls) acc = (
    if m < n then union_blist 0 ls1 (Falses (n - (m + 1)) ls) (Cell a (Falses m acc))
    else union_blist' (m - n) a ls1 ls (Falses n acc)) ∧
  union_blist' m a ls1 (Cell b ls) acc = (
    if m = 0 then union_blist 0 ls1 ls (Cell (build_Or a b) acc)
    else union_blist' (m - 1) a ls1 ls (Cell b acc))
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I)
    (λx. case x of
      INL (_,ls1,ls,_) => (blist_size ls1, blist_size ls)
    | INR (_,_,ls1,ls,_) => (blist_size ls1, blist_size ls))`
End

Definition union_blists_inner_def:
  union_blists_inner row (a1::ls1) (a::ls) =
    union_blist row a1 a Nil :: union_blists_inner row ls1 ls ∧
  union_blists_inner _ _ ls = ls
End

Definition union_blists_def:
  union_blists (row,col) ls1 ls =
    TAKE col ls ++ union_blists_inner row ls1 (DROP col ls)
End

Theorem blist_rev_length[simp]:
  blist_length (blist_rev xs acc) = blist_length xs + blist_length acc
Proof
  simp [blist_length_thm, blist_rev_thm]
QED

Theorem blist_length_union_blist[simp]:
  (∀m ls1 ls acc. blist_length (union_blist m ls1 ls acc) = blist_length ls + blist_length acc) ∧
  (∀m a ls1 ls acc. blist_length (union_blist' m a ls1 ls acc) = blist_length ls + blist_length acc)
Proof
  HO_MATCH_MP_TAC union_blist_ind
  \\ rw [union_blist_def, blist_length_def]
QED

Theorem length_union_blists_inner[simp]:
  LENGTH (union_blists_inner row ls1 ls) = LENGTH ls
Proof
  qid_spec_tac `ls` \\ Induct_on `ls1` \\ simp [union_blists_inner_def]
  \\ Cases_on `ls` \\ simp [union_blists_inner_def]
QED

Theorem length_union_blists[simp]:
  LENGTH (union_blists rc ls1 ls) = LENGTH ls
Proof
  PairCases_on `rc` \\ simp [union_blists_def]
  \\ Cases_on `rc1 ≤ LENGTH ls` \\ simp [TAKE_LENGTH_TOO_LONG]
QED

Theorem every_length_union_blists:
  EVERY (λr. blist_length r = n) ls ⇒
  EVERY (λr. blist_length r = n) (union_blists rc ls1 ls)
Proof
  PairCases_on `rc` \\ simp [union_blists_def, EVERY_MEM,
    MEM_MAP, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM]
  \\ ntac 2 strip_tac >- metis_tac [MEM_TAKE]
  \\ `∀y. MEM y (DROP rc1 ls) ⇒ blist_length y = n` by
    metis_tac [MEM_DROP_IMP]
  \\ rename [`union_blists_inner _ _ ls'`]
  \\ pop_assum mp_tac
  \\ qid_spec_tac `ls'` \\ Induct_on `ls1` \\ simp [union_blists_inner_def]
  \\ Cases_on `ls'`
  \\ rw [union_blists_inner_def, DISJ_IMP_THM, FORALL_AND_THM, blist_length_def]
  \\ metis_tac []
QED

Theorem union_blists_inner_nil[simp]:
  union_blists_inner rc ls1 [] = []
Proof
  Cases_on `ls1` \\ simp [union_blists_inner_def]
QED

Theorem union_blists_nil[simp]:
  union_blists rc ls1 [] = []
Proof
  PairCases_on `rc` \\ simp [union_blists_def]
QED

Theorem union_blists_rectangle:
  rectangle w h (MAP from_blist ls) ⇒
  rectangle w h (MAP from_blist (union_blists rc ls1 ls))
Proof
  simp [rectangle_def, EVERY_MAP, GSYM blist_length_thm]
  \\ metis_tac [every_length_union_blists]
QED

Theorem from_row_append[simp]:
  from_row (q0,q1) (l1 ++ l2) =
    from_row (q0,q1) l1 ∪ from_row (q0 + &LENGTH l1,q1) l2
Proof
  qid_spec_tac `q0` \\ Induct_on `l1` \\ rw [from_row_def]
  \\ Cases_on `h` \\ simp [from_row_def,
    ARITH_PROVE ``(x:int) + 1 + &n = x + &SUC n``, UNION_ASSOC]
QED

Theorem from_row_replicate_F[simp]:
  from_row (q0,q1) (REPLICATE n F) = ∅
Proof
  qid_spec_tac `q0` \\ Induct_on `n` \\ rw [from_row_def]
QED

Theorem from_row_cons:
  from_row (q0,q1) (a :: l) = (if a then {(q0,q1)} else ∅) ∪ from_row (q0+1,q1) l
Proof
  Cases_on`a` \\ simp [from_row_def]
QED

Theorem from_row_union_blist:
  (∀m ls1 ls acc.
    m + blist_length ls1 ≤ blist_length ls ⇒
    ∃ret. from_blist (union_blist m ls1 ls acc) = REVERSE (from_blist acc) ++ ret ∧
      ∀q0. from_row (q0,q1) (MAP (eval env) ret) =
        from_row (q0,q1) (MAP (eval env) (from_blist ls)) ∪
        from_row (q0 + &m,q1) (MAP (eval env) (from_blist ls1))) ∧
  (∀m a ls1 ls acc.
    m + blist_length ls1 + 1 ≤ blist_length ls ⇒
    ∃ret. from_blist (union_blist' m a ls1 ls acc) = REVERSE (from_blist acc) ++ ret ∧
      ∀q0. from_row (q0,q1) (MAP (eval env) ret) =
        from_row (q0,q1) (MAP (eval env) (from_blist ls)) ∪
        from_row (q0 + &m,q1) (eval env a :: MAP (eval env) (from_blist ls1)))
Proof
  HO_MATCH_MP_TAC union_blist_ind
  \\ rw [union_blist_def, blist_length_def, from_blist_def, blist_rev_thm,
    from_row_def, INT_ADD_ASSOC, GSYM INT_ADD, from_row_cons]
  \\ qpat_x_assum `_⇒_` mp_tac \\ impl_tac >- ARITH_TAC \\ rw []
  \\ simp [from_row_cons, from_row_def, INT_ADD_ASSOC, GSYM INT_ADD] \\ gen_tac
  >- (`q0 + &m + 1 + &(n − (m + 1)) = q0 + &n` by ARITH_TAC
    \\ simp [AC UNION_ASSOC UNION_COMM])
  >- (`q0 + &n + &(m − n) = q0 + &m` by ARITH_TAC
    \\ simp [AC UNION_ASSOC UNION_COMM])
  >- SET_TAC []
  >- (`q0 + 1 + &(m - 1) = q0 + &m` by ARITH_TAC
    \\ simp [] \\ SET_TAC [])
QED

Theorem from_rows_union_blists:
  ∀q env h.
  EVERY (λl. blist_length l + row ≤ h) ls1 ∧
  EVERY (λl. blist_length l = h) ls ∧
  LENGTH ls1 + col ≤ LENGTH ls
  ⇒
  from_rows q (MAP (MAP (eval env) ∘ from_blist) (union_blists (row,col) ls1 ls)) =
  from_rows q (MAP (MAP (eval env) ∘ from_blist) ls) ∪
    from_rows (add_pt q (&row, &col)) (MAP (MAP (eval env) ∘ from_blist) ls1)
Proof
  simp [union_blists_def] \\ rpt gen_tac
  \\ PairCases_on `q`
  \\ MAP_EVERY qid_spec_tac [`q1`,`ls`]
  \\ reverse (Induct_on `col`) \\ simp []
  >- (
    Cases_on `ls` \\ rw [] \\ fs [from_rows_def, union_blists_inner_def]
    \\ simp [ARITH_PROVE ``(x:int) + 1 + &n = x + &SUC n``, UNION_ASSOC])
  \\ Induct_on `ls1` \\ simp [union_blists_inner_def, from_rows_def]
  \\ Cases_on `ls` \\ rw [] \\ fs [from_rows_def, union_blists_inner_def]
  \\ mp_tac $ Q.SPECL [`row`,`h''`,`h'`,`Nil`] $ CONJUNCT1 from_row_union_blist
  \\ simp [from_blist_def, AC UNION_ASSOC UNION_COMM]
QED

Definition trim_blist_def:
  trim_blist a l Nil = Falses l Nil ∧
  trim_blist a l (Falses n ls) = (
    if a + l ≤ n then Falses l Nil
    else if n ≤ a then trim_blist (a - n) l ls
    else mk_Falses (n - a) (trim_blist 0 (a + l - n) ls)) ∧
  trim_blist a l (Cell b ls) = (
    if l = 0 then Nil else
    if a = 0 then Cell b (trim_blist 0 (l - 1) ls) else
    trim_blist (a - 1) l ls)
End

Definition trim_blists_def:
  trim_blists (a0,a1) (l0,l1) ls =
    MAP (trim_blist a0 l0) (TAKE l1 (DROP a1 ls)) ++
    REPLICATE (l1 - (LENGTH ls - a1)) (Falses l0 Nil)
End

Theorem trim_blist_length[simp]:
  blist_length (trim_blist a l ls) = l
Proof
  MAP_EVERY qid_spec_tac [`a`,`l`] \\ Induct_on `ls`
  \\ rw [trim_blist_def, blist_length_def, blist_length_mk_Falses]
QED

Theorem trim_blists_length[simp]:
  LENGTH (trim_blists (a0,a1) (l0,l1) ls) = l1
Proof
  simp [trim_blists_def]
  \\ Cases_on `l1 ≤ LENGTH ls − a1` \\ simp [TAKE_LENGTH_TOO_LONG]
QED

Theorem trim_blists_every_length:
  EVERY (λr. blist_length r = l0) (trim_blists (a0,a1) (l0,l1) ls)
Proof
  simp [trim_blists_def, blist_length_def, EVERY_MAP]
QED

Definition build_mega_cell_padded_def:
  build_mega_cell_padded [] init = init ∧
  build_mega_cell_padded (((x,y),g)::gates) init =
    union_blists (75 * Num x, 75 * Num y) g.init (build_mega_cell_padded gates init)
End

Definition build_mega_cell_def:
  build_mega_cell gates =
    let init = REPLICATE (150 * ^tileN + 20) (Falses (150 * ^tileN + 20) Nil) in
    let padded = build_mega_cell_padded gates init in
    let ret = trim_blists (10,10) (150 * ^tileN, 150 * ^tileN) padded in
    if union_blists (10, 10) ret init = padded then SOME ret else NONE
End

Definition mega_cell_builder_def:
  mega_cell_builder mega_tile =
  to_tiling (λb.
    from_rows (-75,-75) (MAP (MAP (eval (λ_. b)) ∘ from_blist) mega_tile))
End

Theorem build_mega_cell_length:
  build_mega_cell gates = SOME ret ⇒
  LENGTH ret = 150 * ^tileN ∧
  EVERY (λr. blist_length r = 150 * ^tileN) ret
Proof
  qid_spec_tac `ret` \\ simp [build_mega_cell_def, trim_blists_every_length]
QED

Theorem from_rows_replicate_F[simp]:
  from_rows q (REPLICATE m (REPLICATE n F)) = ∅
Proof
  PairCases_on `q` \\ qid_spec_tac `q1`
  \\ Induct_on `m` \\ simp [from_rows_def]
QED

Theorem build_mega_cell_thm':
  EVERY (gate_at_wf area) gates ∧ EVERY in_range area ∧
  build_mega_cell gates = SOME ret ⇒
  union_gates gates = λb.
    from_rows (-75,-75) (MAP (MAP (eval (λ_. b)) ∘ from_blist) ret)
Proof
  qid_spec_tac `ret` \\ simp [build_mega_cell_def]
  \\ qmatch_goalsub_abbrev_tac `trim_blists _ _ padded`
  \\ strip_tac
  \\ pop_assum (fn h => assume_tac h
    \\ rw [Once FUN_EQ_THM]
    \\ qspecl_then [`(-85,-85)`, `(λ_. b)`] mp_tac $
      Q.GENL [`q`,`env`,`h`] $ PART_MATCH (dest_path "rlrrr")
        from_rows_union_blists (lhs (concl h))
    \\ simp [from_blist_def, blist_length_def])
  \\ impl_tac
  >- (irule MONO_EVERY \\ irule_at Any trim_blists_every_length \\ simp [])
  \\ disch_then (rw o single o SYM)
  \\ pop_assum kall_tac \\ simp [Abbr`padded`, union_gates_def]
  \\ qho_match_abbrev_tac `_ = _ (_ (f gates))`
  \\ qspec_then `LENGTH (f gates) = 150 * ^tileN + 20 ∧
    EVERY (λr. blist_length r = 150 * ^tileN + 20) (f gates)` match_mp_tac AND2_THM
  \\ simp [Abbr`f`] \\ Induct_on `gates`
  \\ simp [from_blist_def, blist_length_def, build_mega_cell_padded_def, FORALL_PROD]
  \\ qmatch_goalsub_abbrev_tac `MAP _ ls`
  \\ rw [every_length_union_blists] \\ fs []
  \\ drule_all gate_at_wf_bounded \\ rw []
  \\ fs [gate_at_wf_def, gate_wf_def, rectangle_def, EVERY_MAP,
    GSYM blist_length_thm]
  \\ (fn g => qspec_then `150 * ^tileN + 20` mp_tac (
    Q.GEN `h` $ PART_MATCH (dest_path "rlr")
      from_rows_union_blists (rhs (snd g))) g)
  \\ simp [] \\ impl_tac
  >- (reverse conj_tac >- ARITH_TAC
    \\ irule MONO_EVERY \\ first_x_assum $ irule_at Any
    \\ simp [] \\ ARITH_TAC)
  \\ disch_then (fn h => rw [h, Once UNION_COMM]) \\ cong_tac 1
  \\ simp [from_init_def, Once EXTENSION, FORALL_PROD]
  \\ CONV_TAC $ ONCE_DEPTH_CONV $ REWR_CONV from_rows_translate_0
  \\ rw [] \\ cong_tac 2 \\ simp [] \\ ARITH_TAC
QED

Theorem build_mega_cell_thm:
  EVERY (gate_at_wf area) gates ∧ EVERY in_range area ∧
  build_mega_cell gates = SOME ret ⇒
  to_tiling (union_gates gates) = mega_cell_builder ret
Proof
  strip_tac
  \\ drule_all_then (fn h => rw [h, mega_cell_builder_def]) build_mega_cell_thm'
QED

Theorem read_mega_cells_build_mega_cells_thm:
  EVERY (gate_at_wf area) gates ∧ EVERY in_range area ∧
  build_mega_cell gates = SOME ret ∧
  test_blists (1801,674) ret = Var A 0 ⇒
  read_mega_cells (mega_cell_builder ret s) = s
Proof
  rw [read_mega_cells_def, mega_cell_builder_def, to_tiling_def, Once EXTENSION]
  \\ HO_BACKCHAIN_TAC $ METIS_PROVE []
    ``(∀z. P z ⇒ z = x) ∧ (P x ⇔ Q) ⇒ ((∃z. P z) ⇔ Q)``
  \\ conj_tac >- (
    rw [] \\ MAP_EVERY PairCases_on [`x`,`z`] \\ fs [mk_pt_def]
    \\ drule_all_then strip_assume_tac build_mega_cell_length
    \\ `∃i0 i1:num. 3150 * x0 + 1801 − 3150 * z0 = -75 + &i0 ∧
        3150 * x1 + 674 − 3150 * z1 = -75 + &i1` by (
      drule_then strip_assume_tac from_rows_lower_bound \\ ARITH_TAC)
    \\ drule_at Any from_rows_rectangle'
    \\ simp [rectangle'_def, EVERY_MAP, GSYM blist_length_thm]
    \\ disch_then drule \\ ARITH_TAC)
  \\ simp []
  \\ rewrite_tac [from_rows_iff_test_blists,
    ARITH_PROVE ``(1726:int) = -75 + 1801 ∧ (599:int) = -75 + 674``]
  \\ simp []
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
    val step_th = gol_rulesTheory.IN_step |> SRULE [IN_DEF]
    val lem = thm_stmt
      |> (SCONV [nextCell_def,step_th,IN_DEF,LET_THM])
      |> SRULE [GSYM int_sub,gol_lemmasTheory.live_adj_eq]
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
    val _ = cv_transLib.cv_auto_trans gol_lemmasTheory.b2n_def
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

Definition floodfill_result_def:
  floodfill_result ret ⇔ ∃area gates.
  floodfill area
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact (-77) Clock)]
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact 509 Clock)] [] gates ∧
  build_mega_cell gates = SOME ret
End

Theorem floodfill_finish:
  floodfill area
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact (-77) Clock)]
    [(((23,8),E),Exact (-15) ThisCell); (((13,0),E),Exact 509 Clock)] [] gates ⇒
  build_mega_cell gates = SOME ret ⇒
  floodfill_result ret
Proof
  metis_tac [floodfill_result_def]
QED

Theorem floodfill_result_finish:
  floodfill_result ret ∧
  test_blists (1801,674) ret = Var A 0 ⇒
  gol_in_gol (mega_cell_builder ret) (^periodN * 60) read_mega_cells
Proof
  rw [floodfill_result_def, gol_rulesTheory.gol_in_gol_def]
  \\ gvs [floodfill_def, SF DNF_ss]
  \\ gvs [FUN_EQ_THM,FORALL_PROD] \\ rw []
  \\ rename [‘FUNPOW step n init (x,y) = _’]
  \\ qabbrev_tac ‘env = λn. FUNPOW step n init’
  \\ ‘env_wf env’ by
   (gvs [env_wf_def,Abbr‘env’] \\ gen_tac \\ PairCases
    \\ simp [GSYM ADD1,FUNPOW_SUC] \\ gvs [nextCell_correct])
  \\ first_x_assum drule \\ strip_tac
  \\ gvs [v_eval_def]
  \\ qmatch_asmsub_rename_tac `floodfill_run _ _
    [(_,latch);(_,clock)] [(_,latch');(_,clock')]`
  \\ `latch = latch' ∧ clock = clock'` by
    (simp [FUN_EQ_THM, e_clock_def] \\ ARITH_TAC)
  \\ `env 0 = init` by simp [Abbr`env`] \\ pop_assum $ fs o single
  \\ qpat_x_assum `floodfill_run _ _ _ _` mp_tac
  \\ simp [floodfill_run_def]
  \\ disch_then ((fn x => assume_tac (hd x) \\ mp_tac (el 6 x)) o CONJUNCTS)
  \\ impl_tac
  >- (ntac 4 $ pop_assum kall_tac
    \\ simp [floodfill_io_wf_def, SF DNF_ss, FUN_EQ_THM]
    \\ metis_tac [add_pt_0, mk_pt_0])
  \\ drule_all_then (simp o single) build_mega_cell_thm
  \\ gvs [circuit_run_def]
  \\ strip_tac
  \\ dxrule run_clear_mods
  \\ impl_tac
  >-
   (simp [can_clear_def]
    \\ gvs [translate_mods_def,EXTENSION,EXISTS_PROD,translate_mod_def,
            circ_mod_def])
  \\ rw []
  \\ gvs [run_def]
  \\ pop_assum $ qspec_then ‘^periodN * 60 * n’ mp_tac
  \\ rw []
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
  \\ ‘(60 * ^periodN * n − 1) MOD 60 = 59’ by
   (rewrite_tac [GSYM MULT_ASSOC]
    \\ Cases_on ‘^periodN * n’ \\ gvs []
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
  \\ gvs [FORALL_PROD,mk_dpt_def,mk_pt_def]
  \\ simp [e_cell_def]
  \\ gvs [IN_DEF,is_ew_def]
  \\ cong_tac 2
  \\ simp [INT_ADD]
  \\ once_rewrite_tac [ADD_COMM]
  \\ ‘0 < 60:num’ by gvs []
  \\ drule ADD_DIV_ADD_DIV
  \\ disch_then $ rewrite_tac o single o GSYM
  \\ gvs [DIV_DIV_DIV_MULT]
QED

Theorem floodfill_add_gate:
  floodfill area ins outs crosses gates ∧
  is_gate g ins1 outs1 ∧
  PERM outs (del ++ outs') ⇒
  ∀p x' y'.
  (p = (&(2 * x'), &(2 * y')) ∧
  x' + g.width ≤ ^tileN ∧ y' + g.height ≤ ^tileN ∧
  del = MAP (λ((a, d), P). ((add_pt p a, d), P)) ins1) ∧
  EVERY (λa. ¬MEM (add_pt p a) area) (make_area g.width g.height) ⇒
  floodfill
    (MAP (add_pt p) (make_area g.width g.height) ++ area) ins
    (MAP (λ((a, d), P). ((add_pt p a, d), P)) outs1 ++ outs') crosses
    ((p, g) :: gates)
Proof
  rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm \\ gvs []
  \\ simp [floodfill_def] \\ strip_tac \\ fs [SF DNF_ss, MEM_MAP]
  \\ rpt conj_tac
  >- (fs [gate_at_wf_def, is_gate_def, EVERY_MEM, MEM_MAP] \\ metis_tac [])
  >- (irule every_gate_at_wf_mono \\ first_assum $ irule_at Any \\ simp [])
  \\ qabbrev_tac `p = (&(2*x'):int, &(2*y'):int)`
  \\ rpt strip_tac \\ first_x_assum $ drule_then strip_assume_tac
  \\ dxrule $ iffLR LIST_REL_SPLIT1 \\ rw [LIST_REL_MAP1]
  \\ rename [`_ outs' sout'`, `_ (_ ∘ _) ins1 sin1`]
  \\ first_x_assum $ irule_at Any
  \\ irule_at Any EVERY2_APPEND_suff \\ rw [LIST_REL_MAP1]
  \\ first_assum $ irule_at Any
  \\ fs [is_gate_def]
  \\ last_x_assum $ drule_then $ qspec_then `sin1` mp_tac
  \\ impl_tac >- (
    irule EVERY2_mono \\ first_x_assum $ irule_at Any
    \\ simp [FORALL_PROD])
  \\ rw [] \\ rename [`_ outs1 sout1`]
  \\ irule_at Any EVERY2_mono \\ first_assum $ irule_at Any
  \\ conj_tac >- simp [FORALL_PROD]
  \\ rw []
  \\ first_assum $ drule_all_then mp_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ DEP_REWRITE_TAC [GSYM ZIP_APPEND] \\ rw []
  \\ drule_at_then Any (qspecl_then [
    `p`,`g`,`ZIP (MAP FST ins1,sin1)`,`ZIP (MAP FST outs1,sout1)`
    ] mp_tac) floodfill_run_add_gate
  \\ impl_tac >- (
    simp [Abbr`p`]
    \\ fs [floodfill_gate_wf_def, gate_wf_def, MAP_ZIP]
    \\ fs [ZIP_MAP, MAP2_ZIP, MAP_COMPOSE, o_DEF, LAMBDA_PROD])
  \\ strip_tac \\ irule floodfill_run_cancel
  \\ qexists_tac `MAP (λ((a,d),v). ((add_pt p a,d),v)) (ZIP (MAP FST ins1,sin1))`
  \\ drule_then irule floodfill_run_perm \\ simp []
  \\ irule $ METIS_PROVE [PERM_CONG, PERM_APPEND, PERM_REFL]
    ``a1 = a1' ∧ a2 = a2' ⇒ PERM (a1++a2++a3++a4) (a2'++a1'++a3++a4)``
  \\ PairCases_on `p`
  \\ simp [ZIP_MAP, MAP_COMPOSE, o_DEF, LAMBDA_PROD, AC UNION_ASSOC UNION_COMM]
QED

Theorem floodfill_add_small_gate:
  floodfill area ins outs crosses init ∧
  is_gate g ins1 outs1 ∧
  PERM outs (del ++ outs') ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tileN ∧ y' < ^tileN ∧
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
  floodfill area ins outs crosses gates ∧
  gate_wf g ∧
  gate_ports_wf 1 1 {(a,d1); (b,d2)} {(a',d1); (b',d2)} ∧
  PERM outs (((p',d1),P) :: outs') ∧
  classify 5 P = SOME ea ∧
  g.width = 1 ∧ g.height = 1 ∧
  (∀env v1 Q v2 z. env_wf env ∧
    classify 5 Q = SOME Zeros ∧
    v_eval env P v1 ∧ v_eval env Q v2 ⇒
    circuit (make_area 1 1) [(a,d1,v1 z); (b,d2,v2 z)]
      [(a',d1, delay' (5,ea,env 0 z) (v1 z));
       (b',d2, delay 5 (v2 z))]
      (from_init (env 0 z) g.init)) ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tileN ∧ y' < ^tileN ∧
  ¬MEM p area ∧
  p' = add_pt p a ⇒
  floodfill (p :: area) ins
    (((add_pt p a',d1),v_delay 5 P) :: outs')
    ((add_pt p b, add_pt p b', d2) :: crosses)
    ((p, g) :: gates)
Proof
  rpt strip_tac \\ qspec_then `crosses` assume_tac PERM_REFL
  \\ dxrule_then (dxrule_then dxrule) floodfill_perm \\ gvs []
  \\ simp [floodfill_def] \\ strip_tac \\ fs [SF DNF_ss, MEM_MAP]
  \\ rpt conj_tac
  >- fs [gate_at_wf_def, make_area_def]
  >- (irule every_gate_at_wf_mono \\ first_assum $ irule_at Any \\ simp [])
  \\ qabbrev_tac `p = (&(2*x'):int, &(2*y'):int)`
  \\ rpt strip_tac \\ ntac 2 $ first_x_assum $ drule_then strip_assume_tac
  \\ rename [`_ outs' sout'`, `v_eval _ P v1`]
  \\ ntac 2 $ first_assum $ irule_at Any
  \\ dxrule_then (drule_then $ qspecl_then [`0`] mp_tac) v_eval_v_delay'
  \\ rw [] \\ pop_assum $ irule_at Any
  \\ simp [LIST_LENGTH_COMPARE_SUC, PULL_EXISTS, SF DNF_ss] \\ rw []
  \\ rename [`v_eval _ Q v2`]
  \\ first_x_assum $ dxrule_then $ dxrule_then dxrule
  \\ first_x_assum $ dxrule_at Any \\ rw [make_area_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ drule_at_then Any (qspecl_then [`p`,`g`,
      `[((a,d1),v1); ((b,d2),v2)]`,
      `[((a',d1),λz. delay' (5,ea,env 0 z) (v1 z)); ((b',d2),delay 5 ∘ v2)]`
    ] mp_tac) floodfill_run_add_gate
  \\ simp [make_area_def]
  \\ impl_tac >- simp [Abbr`p`, floodfill_gate_wf_def, make_area_def]
  \\ strip_tac \\ irule floodfill_run_cancel
  \\ qexists_tac `[((add_pt p a,d1),v1)]`
  \\ drule_then irule floodfill_run_perm
  \\ simp [iffLR PERM_SYM, PERM_FUN_APPEND_CONS]
  \\ CONV_TAC $ DEPTH_CONV ETA_CONV
  \\ metis_tac [PERM_FUN_CONS, PERM_FUN_SWAP_AT_FRONT,
    PERM_FUN_APPEND_CONS, APPEND, PERM_REFL]
QED

Theorem floodfill_add_crossover_l:
  floodfill area ins outs crosses init ∧
  blist_simulation_ok 1 1
    [(a,d1,Var A 5); (b,d2,Var B 5)]
    [(a',d1,Var A 0); (b',d2,Var B 0)] init1 ∧
  PERM outs (((p',d1),P) :: outs') ⇒
  classify 5 P = SOME ea ⇒
  instantiate (ea, Zeros) init1 = init2 ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tileN ∧ y' < ^tileN ∧
  ¬MEM p area ∧
  p' = add_pt p a ⇒
  floodfill (p :: area) ins
    (((add_pt p a',d1),v_delay 5 P) :: outs')
    ((add_pt p b, add_pt p b', d2) :: crosses)
    ((p, gate 1 1 init2) :: init)
Proof
  rpt strip_tac \\ irule floodfill_add_crossover_gen
  \\ rpt $ last_assum $ irule_at Any \\ rw [] >>> ROTATE_LT 2
  >- (drule blist_simulation_ok_gate_ports_wf \\ simp [])
  >- (drule_then irule blist_simulation_ok_gate_wf \\ simp [])
  \\ dxrule blist_simulation_ok_imp_circuit
  \\ simp [admissible_ins_def, PULL_EXISTS]
  \\ disch_then $ rev_drule_then $ drule_then $
    qspecl_then [`z`,`Zeros`,`ea`] suff_eq_tac
  \\ cong_tac 5 >>> NTH_GOAL (cong_tac 2) 2
  \\ simp [FUN_EQ_THM, mk_output_env_def]
QED

Theorem floodfill_add_crossover_r:
  floodfill area ins outs crosses init ∧
  blist_simulation_ok 1 1
    [(a,d1,Var A 5); (b,d2,Var B 5)]
    [(a',d1,Var A 0); (b',d2,Var B 0)] init1 ∧
  PERM outs (((p',d2),P) :: outs') ⇒
  classify 5 P = SOME eb ⇒
  instantiate (Zeros, eb) init1 = init2 ⇒
  ∀p x' y'.
  p = (&(2 * x'), &(2 * y')) ∧ x' < ^tileN ∧ y' < ^tileN ∧
  ¬MEM p area ∧
  p' = add_pt p b ⇒
  floodfill (p :: area) ins
    (((add_pt p b',d2),v_delay 5 P) :: outs')
    ((add_pt p a, add_pt p a', d1) :: crosses)
    ((p, gate 1 1 init2) :: init)
Proof
  rpt strip_tac \\ irule floodfill_add_crossover_gen
  \\ rpt $ last_assum $ irule_at Any \\ rw [] >>> ROTATE_LT 2
  >- (drule blist_simulation_ok_gate_ports_wf \\ simp [INSERT_COMM])
  >- (drule_then irule blist_simulation_ok_gate_wf \\ rw [])
  \\ dxrule blist_simulation_ok_imp_circuit
  \\ simp [admissible_ins_def, PULL_EXISTS]
  \\ disch_then $ dxrule_then $ drule_then $
    qspecl_then [`z`,`eb`,`Zeros`] suff_eq_tac
  \\ irule circuit_perm \\ simp [PERM_SWAP_AT_FRONT]
  \\ irule $ METIS_PROVE [PERM_SWAP_AT_FRONT, PERM_REFL] ``[b;a] = c ⇒ PERM [a;b] c``
  \\ cong_tac 2 >>> NTH_GOAL (cong_tac 2) 2
  \\ simp [FUN_EQ_THM, mk_output_env_def]
QED

Theorem floodfill_finish_crossover:
  floodfill area ins outs crosses init ∧
  PERM outs (((p,d),P) :: outs') ∧
  PERM crosses ((p,q,d) :: crosses') ⇒
  classify 5 P = SOME Zeros ⇒
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
    \\ simp [FUN_EQ_THM, delay_def, delay'_def, eval_env_kind_def])
  \\ rw []
  \\ first_x_assum (qspec_then `v::scross` mp_tac)
  \\ simp [SF DNF_ss]
  \\ disch_then $ drule_then $ drule_then assume_tac
  \\ irule floodfill_run_cancel
  \\ qexists_tac `[((p,d),v)]`
  \\ drule_then irule floodfill_run_perm \\ simp [PERM_FUN_APPEND_CONS]
QED

Theorem floodfill_run_teleport:
  floodfill_run area init ins ((ad,v)::outs) ⇒
  floodfill_run area init ins ((mk_dpt ad z,v ∘ add_pt z)::outs)
Proof
  Cases_on `ad` \\ simp [floodfill_run_def, mk_dpt_def] \\ strip_tac
  \\ fs [SF DNF_ss] \\ qexists_tac `sub_pt z' z` \\ rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- simp [sub_mk_pt_assoc, mk_mk_pt_assoc]
  >- first_assum ACCEPT_TAC
  >- metis_tac [span_sn_eq_span_sn]
  \\ strip_tac \\ qpat_x_assum `_ ⇒ _` mp_tac
  \\ impl_tac >- (
    fs [floodfill_io_wf_def, SF DNF_ss] \\ rpt conj_tac
    >- (rw [] \\ first_assum drule_all
      \\ reverse (rw []) >- metis_tac []
      \\ disj1_tac \\ qexists_tac `sub_pt z'³' z`
      \\ conj_tac >- (qpat_x_assum `mk_pt _ _ = _` mp_tac \\ pt_arith_tac)
      \\ `∀i. add_pt i (sub_pt z'³' z) = add_pt (sub_pt i z) z'³'` by pt_arith_tac
      \\ fs [FUN_EQ_THM] \\ rw [])
    >- (
      `(∀z''. mk_pt (mk_pt q z) (sub_pt z'' z) = mk_pt q z'') ∧
       ∀i z''. add_pt z (add_pt i z'') = add_pt i (add_pt z z'')` by pt_arith_tac
      \\ pop_assum (fs o single)
      \\ metis_tac [mk_mk_pt_assoc])
    >- first_assum ACCEPT_TAC)
  \\ disch_then suff_eq_tac \\ cong_tac 2 \\ simp [Once EXTENSION]
  \\ simp [SF DNF_ss] \\ strip_tac \\ cong_tac 2
  \\ Cases_on `q` \\ Cases_on `z` \\ simp [EXISTS_PROD, mk_pt_def]
  \\ eq_tac \\ strip_tac \\ gvs []
  THENL (map qexistsl_tac [[`p_1+q`,`p_2+r''`], [`p_1-q`,`p_2-r''`]])
  \\ (conj_tac >- ARITH_TAC \\ cong_tac 1 \\ simp [] \\ ARITH_TAC)
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
    \\ Cases_on `a` \\ fs [v_teleport_def]
    \\ metis_tac [add_pt_comm, add_pt_assoc])
  \\ rw [] \\ first_x_assum $ drule_all_then assume_tac
  \\ drule_then irule floodfill_run_teleport
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
