(* val _ = HOL_Interactive.toggle_quietdec(); *)
open HolKernel bossLib boolLib Parse;
open gol_simTheory listTheory gol_gatesTheory gol_circuitTheory pred_setTheory
     pairTheory alistTheory arithmeticTheory sortingTheory;
(* val _ = HOL_Interactive.toggle_quietdec(); *)

val _ = new_theory "gol_in_gol_circuit2";

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
  evalue = Clock | NotClock | ThisCell | NextCell | ThisCellUntilClock num;
  value = Reg num rvalue | Exact num evalue | Fail
End

val period = ``586:num``
val pulse = ``18:num``

Definition r_eval_def[simp]:
  (r_eval f (Cell (i,j)) ⇔ f (i, j)) ∧
  (r_eval f (RNot v) ⇔ ¬r_eval f v) ∧
  (r_eval f (RAnd v1 v2) ⇔ r_eval f v1 ∧ r_eval f v2) ∧
  (r_eval f (ROr v1 v2) ⇔ r_eval f v1 ∨ r_eval f v2) ∧
  (r_eval f (RXor v1 v2) ⇔ r_eval f v1 ≠ r_eval f v2)
End

Definition e_eval_def[simp]:
  (e_eval f n Clock ⇔ (n:int) % &^period < &^pulse) ∧
  (e_eval f n NotClock ⇔ ¬(n % &^period < &^pulse)) ∧
  (e_eval f n ThisCell ⇔ f (n / &^period)) ∧
  (e_eval f n NextCell ⇔ (n:int) % &^period < &^pulse ∧ f (n / &^period + 1)) ∧
  (e_eval f n (ThisCellUntilClock p) ⇔ f (n / &^period) ∧ ¬((n + &p) % &^period < &^pulse))
End

Definition v_eval'_def[simp]:
  (v_eval' (f, t) (Reg d rv) s ⇔
    ∀ n i. d ≤ i ∧ i < ^period ⇒ s (t + ^period * n + i) = r_eval (f (&n)) rv) ∧
  (v_eval' (f, t) (Exact d ev) s ⇔ ∀n. s n = e_eval (λi. f i (0, 0)) (&n - &(t + d)) ev) ∧
  (v_eval' (f, t) Fail s ⇔ T)
End

Definition v_eval_def:
  v_eval (f:int -> state, t) v s ⇔
    ∀x y:int. v_eval' ((λi (a,b). f i (x+a,y+b)), t) v (s (x, y))
End

Theorem v_eval_fail[simp]:
  v_eval env Fail s
Proof
  Cases_on `env` \\ simp [v_eval_def]
QED

Definition v_delay_def[simp]:
  v_delay n (Reg i v) = Reg (n + i) v ∧
  v_delay n (Exact i v) = Exact (n + i) v ∧
  v_delay n Fail = Fail
End

Theorem v_delay_0[simp]:
  v_delay 0 v = v
Proof
  Cases_on `v` \\ rw []
QED

Definition to_reg_def[simp]:
  to_reg (Reg i v) = SOME (i, v) ∧
  to_reg (Exact i ThisCell) = SOME (i, Cell (0, 0)) ∧
  to_reg _ = NONE
End

Definition v_teleport_def:
  v_teleport (x, y) v = case to_reg v of
    | SOME (i, Cell (a, b)) => Reg i (Cell (a + x, b + y))
    | _ => Fail
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

Definition v_and_def:
  (v_and (Exact d1 ThisCell) (Exact d2 NotClock) =
    if d1 ≤ d2 ∧ d1 ≤ ^pulse then Exact d1 (ThisCellUntilClock (d2 - d1))
    else Fail) ∧
  (v_and (Exact d1 Clock) (Reg d2 v2) =
    if v2 = nextCell ∧ d2 ≤ d1 then Exact d1 NextCell else Fail) ∧
  (v_and v1 v2 = case (to_reg v1, to_reg v2) of
    | (SOME (d1, rv1), SOME (d2, rv2)) => Reg (MAX d1 d2) (RAnd rv1 rv2)
    | _ => Fail)
End
Theorem v_and_def[simp,compute,allow_rebind] = SRULE [] v_and_def;

Theorem v_and_fail[simp]:
  v_and v Fail = Fail
Proof
  Cases_on `v` \\ simp [] \\ Cases_on `e` \\ simp []
QED

Definition v_or_def:
  (v_or (Exact d1 NextCell) (Exact d2 (ThisCellUntilClock d3)) =
    if d1 = d2 + d3 ∧ d1 = ^period then Exact 0 ThisCell else Fail) ∧
  (v_or v1 v2 = case (to_reg v1, to_reg v2) of
    | (SOME (d1, rv1), SOME (d2, rv2)) => Reg (MAX d1 d2) (ROr rv1 rv2)
    | _ => Fail)
End
Theorem v_or_def[simp,allow_rebind] = SRULE [] v_or_def;

Theorem v_or_fail[simp]:
  v_or v Fail = Fail
Proof
  Cases_on `v` \\ simp [] \\ Cases_on `e` \\ simp []
QED

Theorem v_or_thiscell:
  v_or (Exact n ThisCell) v = v_or (Reg n (Cell (0,0))) v ∧
  v_or v (Exact n ThisCell) = v_or v (Reg n (Cell (0,0)))
Proof
  Cases_on `v` \\ rw [] \\ Cases_on `e` \\ rw []
QED

Definition v_not_def[simp]:
  (v_not (Reg d1 v1) = Reg d1 (RNot v1)) ∧
  (v_not (Exact d1 ThisCell) = Reg d1 (RNot (Cell (0, 0)))) ∧
  (v_not (Exact d1 Clock) = Exact d1 NotClock) ∧
  (v_not _ = Fail)
End

Definition v_xor_def:
  v_xor v1 v2 = case (to_reg v1, to_reg v2) of
    | (SOME (d1, rv1), SOME (d2, rv2)) => Reg (MAX d1 d2) (RXor rv1 rv2)
    | _ => Fail
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

Definition is_exact_def[simp]:
  is_exact (Exact _ _) = T ∧ is_exact _ = F
End

Definition env_wf_def:
  env_wf (f:int->state, t:num) = (ARB:bool)
End

Definition assign_ext_def:
  assign_ext (s, dom) (s', dom') ⇔ dom ⊆ dom' ∧ (∀x. x ∈ dom ⇒ s x = s' x)
End

Definition assign_sat_def:
  assign_sat env (s, dom) (p, d:dir, v) ⇔ p ∈ dom ∧ v_eval env v (s p)
End

Definition max_delay_def[simp,compute]:
  (max_delay (da, a) (Var a' d) = if a = a' then da - d else 0) ∧
  (max_delay a (Not x)   = max_delay a x) ∧
  (max_delay a (And x y) = MAX (max_delay a x) (max_delay a y)) ∧
  (max_delay a (Or x y)  = MAX (max_delay a x) (max_delay a y)) ∧
  (max_delay _ _         = 0)
End

Definition vb_eval'_def[simp,compute]:
  (vb_eval' ((da, a), _) (Var A d) = v_delay da a) ∧
  (vb_eval' (_, (db, b)) (Var B d) = v_delay db b) ∧
  (vb_eval' env (Not x)   = v_not (vb_eval' env x)) ∧
  (vb_eval' env (And x y) = v_and (vb_eval' env x) (vb_eval' env y)) ∧
  (vb_eval' env (Or x y)  = v_or  (vb_eval' env x) (vb_eval' env y)) ∧
  (vb_eval' _ _ = Fail)
End

Definition vb_eval_def[compute]:
  vb_eval ((da, a), (db, b)) v =
    vb_eval' ((max_delay (da, A) v, a), (max_delay (db, B) v, b)) v
End

Theorem is_exact_unique:
  is_exact v ∧ v_eval env v s ∧ v_eval env v t ⇒ s = t
Proof
  Cases_on `v` \\ simp [FUN_EQ_THM, is_exact_def, FORALL_PROD]
  \\ Cases_on `env` \\ simp [v_eval_def, v_eval'_def]
QED

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

Definition gate_def:
  gate (width:num) (height:num)
    (ins: ((int # int) # dir # value) list)
    (outs: ((int # int) # dir # value) list)
    (init: bool list list) ⇔
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  ∀env. env_wf env ⇒
  ∀s. (∀v. MEM v ins ⇒ assign_sat env s v) ∧
    (∀p d v. MEM (p,d,v) outs ∧ p ∈ SND s ⇒
      is_exact v ∧ assign_sat env s (p,d,v)) ⇒
  ∃s'. assign_ext s s' ∧ SND s' = SND s ∪ set (MAP FST outs) ∧
    (∀v. MEM v outs ⇒ assign_sat env s' v) ∧
  ∀z. circuit (make_area width height)
    (MAP (λ(p,d,_). (p,d,FST s' p z)) ins)
    (MAP (λ(p,d,_). (p,d,FST s' p z)) outs)
    [] (from_rows (-85,-85) init)
End

Theorem blist_simulation_ok_imp_gate:
  blist_simulation_ok w h ins outs init
  (* ∧
  (∀a. ¬EXISTS (λx. case x of (_,_,Var a' _) => a = a' | _ => F) ins ⇒
    ¬EXISTS (λx. case x of (_,_,v) => a = a' | _ => F) outs) *)
  ⇒
  ∀env. gate w h
    (MAP (λ(p,d,v). (p,d,vb_eval env v)) ins)
    (MAP (λ(p,d,v). (p,d,vb_eval env v)) outs) ARB
Proof
  simp [gate_def] \\ ntac 2 strip_tac
  \\ qpat_abbrev_tac `f = λ(p,d,v). (p,d,vb_eval env v)`
  \\ simp [MEM_MAP, PULL_EXISTS, MAP_COMPOSE]
  \\ `FST ∘ f = FST` by simp [Abbr`f`, FORALL_PROD, FUN_EQ_THM]
  \\ pop_assum (simp o single) \\ conj_asm1_tac
  >- fs [blist_simulation_ok_def, blist_simple_checks_def]
  \\ rpt strip_tac \\ PairCases_on `env` \\ rename1 `((da,a),(db,b))`
  \\ Cases_on `s` \\ simp [EXISTS_PROD, assign_ext_def]
  \\ qabbrev_tac `env2 = (ARB:int#int->var#num->bool)`
  \\ qabbrev_tac `s1 = λ v p n. eval (age n (env2 p)) v`
  \\ sg `∀v. v_eval env' (vb_eval ((da,a),(db,b)) v) (s1 v)` >- cheat
  \\ qexists_tac `λx. case ALOOKUP outs x of | NONE => q x | SOME (_,v) => s1 v` \\ rw []
  >- (rpt CASE_TAC \\ rw []
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ first_x_assum (drule_at_then Any (drule_at Any))
    \\ rw [Abbr`f`, assign_sat_def]
    \\ irule is_exact_unique \\ rpt $ first_assum $ irule_at Any)
  >- (Cases_on `y` \\ Cases_on `r'` \\ rw [Abbr`f`, assign_sat_def]
    \\ simp [MEM_MAP, Once EXISTS_PROD] >- metis_tac []
    \\ drule_at Any ALOOKUP_ALL_DISTINCT_MEM \\ fs [ALL_DISTINCT_APPEND])
  \\ cheat
QED

Theorem gate_weaken:
  LIST_REL (λ(p,d,v) (p',d',v'). p = p' ∧ d = d' ∧ v ⊑ v') outs outs' ∧
  gate w h ins outs init ⇒ gate w h ins outs' init
Proof
  cheat
QED

Theorem half_adder_weaken:
  gate w h ins [(p,d,v_or
    (v_and a (v_or (v_and a (v_not b)) (v_and (v_not a) (v_and b (v_not b)))))
    (v_and (v_not a) (v_or a b))); out] init ⇒
  gate w h ins [(p,d,v_xor a b);out] init
Proof
  strip_tac \\ dxrule_at_then Any irule gate_weaken
  \\ PairCases_on `out` \\ simp []
  \\ Q.HO_MATCH_ABBREV_TAC `f a b ⊑ _`
  \\ `∀ na nb ra rb. f (Reg na ra) (Reg nb rb) ⊑
        Reg (MAX na nb) (RXor ra rb)` by (
    rw [Abbr`f`] \\ rw [MAX_ASSOC, v_subset_def]
    \\ Cases_on `env` \\ fs [v_eval_def] \\ pop_assum $ K $ metis_tac [])
  \\ `∀n a. f (Exact n ThisCell) a = f (Reg n (Cell (0, 0))) a ∧
            f a (Exact n ThisCell) = f a (Reg n (Cell (0, 0)))` by (
    rw [Abbr`f`] \\ Cases_on `a` \\ simp [] \\ Cases_on `e` \\ simp [])
  \\ simp [v_xor_def]
  \\ (Cases_on `a` THENL [ALL_TAC, Cases_on `e`, ALL_TAC] \\ simp [])
  \\ (Cases_on `b` THENL [ALL_TAC, Cases_on `e`, ALL_TAC] \\ simp [])
QED

Theorem gate_and_en_e:
  gate 1 1 [((-1,0),E,a); ((0,1),N,b)]
    [((1,0),E, v_and (v_delay 5 a) (v_delay 5 b))]
    and_en_e_concrete
Proof
  cheat
QED

val tile = ``21:num``;

Definition gate_at'_def:
  gate_at' (x,y) = from_rows (75*x-85, 75*y-85)
End

Definition gate_at_def:
  gate_at (x:int,y:int) init =
    U {gate_at' (x + i * 2 * &^tile, y + j * 2 * &^tile) init | i, j | T}
End

Definition floodfill_ins_def:
  floodfill_ins (f, t) p = [
    ((22:int,8:int),E,λn. f ((&n - &t) / &^period : int) p);
    ((32,0),E,λn. (&n - &t) % &^period < &^pulse)]
End

Definition floodfill_mod_def:
  floodfill_mod (area: (int # int) list)
    (ins: ((int # int) # dir) list)
    (outs: ((int # int) # dir) list) s =
  join_all (UNIV, λ(i,j).
    translate_mods (i * 150 * &^tile, j * 150 * &^tile)
      (circ_mod (set area)
        (set (MAP (λ(p,d). (p,d,FST s p (i, j))) ins))
        (set (MAP (λ(p,d). (p,d,FST s p (i, j))) outs)) {}))
End

Definition floodfill_def:
  floodfill (area: (int # int) list)
    (ins: ((int # int) # dir # value) list)
    (outs: ((int # int) # dir # value) list)
    (crosses: ((int # int) # (int # int) # dir) list)
    (init: (int # int) set) ⇔
  (∀x y. MEM (x,y) area ⇒ x % 2 = 0 ∧ 0 ≤ x ∧ x < 2 * &^tile) ∧
  (∀x y. MEM (x,y) area ⇒ y % 2 = 0 ∧ 0 ≤ y ∧ y < 2 * &^tile) ∧
  ∀env. env_wf env ⇒
  ∃s. (∀v. MEM v (ins ++ outs) ⇒ assign_sat env s v) ∧
  ∀s'. assign_ext s s' ∧
  (∀pi po d. MEM (pi,po,d) crosses ⇒ ∃v.
    assign_sat env s' (pi,d,v) ∧
    assign_sat env s' (po,d,v_delay 5 v)) ⇒
  run (floodfill_mod area
    (MAP (λ(p,d,_). (p,d)) ins ++ MAP (λ(p,_,d). (p,d)) crosses)
    (MAP (λ(p,d,_). (p,d)) outs ++ MAP (λ(_,p,d). (p,d)) crosses)
    s') init
End

Theorem floodfill_add_start_gate:
  floodfill area ins outs crosses init ∧
  gate w h ins1 outs1 init1 ∧
  &(2 * x') = x ∧ &(2 * y') = y ∧ x' + w ≤ ^tile ∧ y' + h ≤ ^tile ∧
  EVERY (λ(a,b). ¬MEM (x+a,y+b) area) (make_area width height) ∧
  PERM outs (del ++ outs') ∧
  LIST_REL (λ((a,b),d,P) (p,d',Q). p = (x+a,y+b) ∧ d = d' ∧ P ⊑ Q) ins1 del ⇒
  floodfill area ins (MAP (λ((a,b),Q). ((x+a,y+b),Q)) outs1 ++ outs') crosses
    (gate_at (x,y) init1 ∪ init)
Proof
  cheat
QED

Theorem floodfill_start:
  floodfill [] [] [] [] ∅
Proof
  rw [floodfill_def] \\ qexists_tac `(λ_ _ _. F), ∅`
  \\ rw [floodfill_mod_def]
  \\ qpat_abbrev_tac `m = join_all _`
  \\ `m = empty_mod` suffices_by simp [run_empty_mod]
  \\ rw [Once FUN_EQ_THM, Abbr`m`, join_all_def, pairTheory.LAMBDA_PROD]
  \\ simp [empty_mod_def, BIGUNION_GSPEC]
QED

Theorem floodfill_add_ins:
  floodfill area ins outs [] init ∧
  gate 1 1 [((a,b),d,Exact dl v)] outs' init1 ⇒
  ∀x y x' y'.
  &(2 * x') = x ∧ &(2 * y') = y ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM (x,y) area ∧
  ¬MEM (x+a,y+b) (MAP FST (ins ++ outs)) ⇒
  floodfill ((x,y) :: area) (((x+a,y+b),d,Exact dl v) :: ins)
    (MAP (λ((a',b'),d',Q). ((x+a',y+b'),d',Q)) outs' ++ outs) []
    (gate_at (x,y) init1 ∪ init)
Proof
  cheat
QED

Definition ffins_def:
  ffins = [((22:int,8:int),E,Exact 0 ThisCell); ((32,0),E,Exact 0 Clock)]
End

(* Theorem floodfill_start:
  floodfill [] [
    ((22:int,8:int),E,Exact 0 ThisCell);
    ((32,0),E,Exact 0 Clock)] [] ∅
Proof
  cheat
QED *)

Theorem floodfill_finish:
  floodfill area
    [((23,8),E,Exact 0 ThisCell); ((33,0),E,Exact 0 Clock)]
    [((23,8),E,Exact 0 ThisCell); ((33,0),E,Exact 586 Clock)] [] init ∧
  env_wf (f, t) ⇒
  run (join_all' {
    translate_mods (i * 150 * &^tile, j * 150 * &^tile)
      (circ_mod (set area) ∅ ∅
        {((22,8),E, λn. f ((&n - &t) / &^period : int) (i, j))})
    | i, j | T}) init
Proof
  cheat
QED

Theorem floodfill_add_gate:
  floodfill area ins outs crosses init ∧
  gate w h ins1 outs1 init1 ∧
  PERM outs (del ++ outs') ⇒
  ∀x y x' y'.
  (&(2 * x') = x ∧ &(2 * y') = y ∧ x' + w ≤ ^tile ∧ y' + h ≤ ^tile ∧
  LIST_REL (λ((a,b),d,P) (p,d',Q). p = (x+a,y+b) ∧ d = d' ∧ P ⊑ Q) ins1 del) ∧
  EVERY (λ(a,b). ¬MEM (x+a,y+b) area) (make_area w h) ⇒
  floodfill
    (MAP (λ(a,b). (x+a,y+b)) (make_area w h) ++ area) ins
    (MAP (λ((a,b),dQ). ((x+a,y+b),dQ)) outs1 ++ outs') crosses
    (gate_at (x,y) init1 ∪ init)
Proof
  cheat
QED

Theorem floodfill_add_small_gate:
  floodfill area ins outs crosses init ∧
  gate 1 1 ins1 outs1 init1 ∧
  PERM outs (del ++ outs') ⇒
  ∀x y x' y'.
  &(2 * x') = x ∧ &(2 * y') = y ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM (x,y) area ∧
  LIST_REL (λ((a,b),d,P) (p,d',Q). p = (x+a,y+b) ∧ d = d' ∧ P ⊑ Q) ins1 del ⇒
  floodfill ((x,y) :: area) ins
    (MAP (λ((a,b),dQ). ((x+a,y+b),dQ)) outs1 ++ outs') crosses
    (gate_at (x,y) init1 ∪ init)
Proof
  cheat
QED

Definition half_adder_ee_ee_concrete_def:
  half_adder_ee_ee_concrete = (ARB:bool list list)
End

Theorem gate_half_adder_ee_ee:
  gate 2 2 [((-1,0),E,a); ((-1,2),E,b)]
    [((3,0),E, v_xor (v_delay 15 a) (v_delay 18 b));
     ((3,2),E, v_and (v_delay 17 a) (v_delay 15 b))]
  half_adder_ee_ee_concrete
Proof
  cheat
QED

Definition crossover_def:
  crossover
    (i1: int # int) (o1: int # int) (d1: dir)
    (i2: int # int) (o2: int # int) (d2: dir)
    (init: bool list list) ⇔
  ∀a b. circuit [(0,0)]
    [(i1,d1,a); (i2,d2,b)]
    [(o1,d1,delay 5 a); (o2,d2,delay 5 b)]
    [] (from_rows (-85,-85) init)
End

Theorem blist_simulation_ok_imp_crossover:
  blist_simulation_ok 1 1
    [(i1,d1,Var A 5); (i2,d2,Var B 5)]
    [(o1,d1,Var A 0); (o2,d2,Var B 0)] init ⇒
  crossover i1 o1 d1 i2 o2 d2 ARB
Proof
  rw [crossover_def]
  \\ dxrule_then assume_tac blist_simulation_ok_thm
  \\ dxrule_then assume_tac simulation_ok_IMP_circuit
  \\ pop_assum $ qspec_then `λ(x,n). delay 5 (var_CASE x a b) n` assume_tac
  \\ Cases_on `i1` \\ Cases_on `i2` \\ Cases_on `o1` \\ Cases_on `o2`
  \\ `∀a. (λn. delay 5 a (n + 5)) = a ∧ (λn. delay 5 a n) = delay 5 a`
    by simp [FUN_EQ_THM, delay_def]
  \\ `MAP (MAP (eval (λ(x,n). delay 5 (var_CASE x a b) n)))
      (MAP from_blist init) = ARB` by cheat
  \\ fs [eval_io_def, make_area_def]
QED

Theorem crossover_symm:
  crossover i1 o1 d1 i2 o2 d2 init ⇒
  crossover i2 o2 d2 i1 o1 d1 init
Proof
  simp [crossover_def, circuit_def, INSERT_COMM]
QED

Theorem floodfill_add_crossover:
  floodfill area ins outs crosses init ∧
  crossover (a,b) (a',b') d1 (c,d) (c',d') d2 init1 ∧
  PERM outs ((p',d1,P) :: outs') ⇒
  ∀x y x' y'.
  &(2 * x') = x ∧ &(2 * y') = y ∧ x' < ^tile ∧ y' < ^tile ∧
  ¬MEM (x,y) area ∧
  p' = (x+a,y+b) ⇒
  floodfill ((x,y) :: area) ins
    (((x+a',y+b'),d1,v_delay 5 P) :: outs')
    (((x+c,y+d), (x+c',y+d'), d2) :: crosses)
    (gate_at (x,y) init1 ∪ init)
Proof
  cheat
QED

Theorem floodfill_finish_crossover:
  floodfill area ins outs crosses init ∧
  PERM outs ((p,d,P) :: outs') ∧
  PERM crosses ((p,q,d) :: crosses') ⇒
  floodfill area ins ((q,d,v_delay 5 P) :: outs') crosses' init
Proof
  cheat
QED

Theorem floodfill_teleport:
  floodfill area ins outs crosses init ∧
  PERM outs (((a,b),d,P) :: outs') ⇒
  ∀x y.
  floodfill area ins
    (((a + 2 * &^tile * x, b + 2 * &^tile * y),d,v_teleport (x, y) P) :: outs')
    crosses init
Proof
  cheat
QED

Theorem make_area_2_2 = EVAL ``EVERY (λ(a,b). ¬MEM (x+a,y+b) area) (make_area 2 2)``

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
