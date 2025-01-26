(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open preamble;

val _ = new_theory "gol_rules";

Overload "U"[local] = “BIGUNION”;

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

(* consequences *)

Theorem IN_step:
  (i,j) ∈ step s ⇔ if (i,j) ∈ s then live_adj s i j ∈ {2;3}
                                else live_adj s i j = 3
Proof
  fs [IN_DEF,step_def]
QED

Theorem b2n_eq[simp]:
  (b2n b = 0 ⇔ ~b) ∧
  (b2n b = 1 ⇔ b)
Proof
  Cases_on ‘b’ \\ fs []
QED

(* area of influence *)

Definition infl_def: (* influence *)
  infl s (i,j) ⇔ live_adj s i j ≠ 0 ∨ (i,j) ∈ s
End

Theorem infl_compose:
  infl s ∩ infl t = ∅ ⇒
  step (s ∪ t) = step s ∪ step t
Proof
  fs [EXTENSION,FORALL_PROD]
  \\ rw [IN_DEF,infl_def,step_def]
  \\ first_x_assum (qspecl_then [‘p_1’,‘p_2’] mp_tac)
  \\ Cases_on ‘s (p_1,p_2)’ \\ fs [] \\ rw []
  \\ fs [live_adj_def,IN_DEF]
QED

Theorem infl_thm:
  (i,j) ∈ infl s ⇔
    (i-1, j-1) ∈ s ∨ (i, j-1) ∈ s ∨ (i+1, j-1) ∈ s ∨
    (i-1, j  ) ∈ s ∨ (i, j  ) ∈ s ∨ (i+1, j  ) ∈ s ∨
    (i-1, j+1) ∈ s ∨ (i, j+1) ∈ s ∨ (i+1, j+1) ∈ s
Proof
  fs [IN_DEF,infl_def]
  \\ Cases_on ‘s (i,j)’ \\ fs [live_adj_def]
  \\ fs [AC DISJ_COMM DISJ_ASSOC]
QED

Theorem infl_mono:
  x ⊆ y ⇒ infl x ⊆ infl y
Proof
  fs [infl_thm,SUBSET_DEF,FORALL_PROD]
  \\ rw [] \\ fs []
QED

Theorem step_SUBSET_infl:
  step s ⊆ infl s
Proof
  fs [step_def,SUBSET_DEF] \\ PairCases \\ fs [IN_step,infl_thm]
  \\ strip_tac
  \\ ‘live_adj s x0 x1 ≠ 0’ by (pop_assum mp_tac \\ IF_CASES_TAC \\ fs [])
  \\ last_x_assum kall_tac
  \\ fs [live_adj_def,IN_DEF]
QED

Theorem infl_union:
  infl (s ∪ s') = infl s ∪ infl s'
Proof
  fs [EXTENSION,IN_DISJOINT,FORALL_PROD] \\ rw []
  \\ eq_tac \\ fs [infl_thm]
  \\ rw [] \\ fs []
QED

(* list to set *)

Definition to_state_def:
  to_state xs = { p | MEM (p,T) xs } : state
End

(* runs *)

Datatype:
  modifier =
    <| area           : (int # int) set ;
       deletions      : (int # int) set ;
       insertions     : (int # int) set ;
       assert_area    : (int # int) set ;
       assert_content : (int # int) set |>
End

Definition mod_step_def:
  mod_step c s1 s3 ⇔
    ∃s2.
      infl s1 ⊆ c.area ∧
      step s1 = s2 ∧
      s2 ∩ c.assert_area = c.assert_content ∧
      s3 = c.insertions ∪ (s2 DIFF c.deletions)
End

Theorem mod_step_univ:
  c.area = UNIV ∧ c.insertions = EMPTY ∧ c.deletions = EMPTY
  ⇒
  (mod_step c s1 s2
   ⇔
   step s1 = s2 ∧
   s2 ∩ c.assert_area = c.assert_content)
Proof
  gvs [mod_step_def] \\ metis_tac []
QED

Definition mod_steps_def:
  mod_steps 0 c n s1 s2 = (s1 = s2) ∧
  mod_steps (SUC k) c n s1 s3 =
     ∃s2. mod_step (c n) s1 s2 ∧ mod_steps k c (n+1:num) s2 s3
End

Definition run_to_def:
  run_to k c s t ⇔ mod_steps k c 0 s t
End

Definition run_def:
  run c s = ∀k. ∃t. run_to k c s t
End

Definition disjoint_mod_def:
  disjoint_mod m1 m2 ⇔ DISJOINT m1.area m2.area
End

Definition disjoint_mods_def:
  disjoint_mods c1 c2 ⇔ ∀n. disjoint_mod (c1 n) (c2 n)
End

Definition mod_wf_def:
  mod_wf m ⇔
    m.deletions ⊆ m.area ∧
    m.assert_area ⊆ m.area ∧
    m.assert_content ⊆ m.assert_area
End

Definition mods_wf_def:
  mods_wf c = ∀n. mod_wf (c (n:num))
End

Definition join_def:
  join c1 c2 =
    λn. <| area           := (c1 n).area ∪ (c2 n).area ;
           deletions      := (c1 n).deletions ∪ (c2 n).deletions ;
           insertions     := (c1 n).insertions ∪ (c2 n).insertions ;
           assert_area    := (c1 n).assert_area ∪ (c2 n).assert_area ;
           assert_content := (c1 n).assert_content ∪ (c2 n).assert_content |>
End

Theorem mod_steps_compose:
  ∀c1 c2 k n s1 s2 t1 t2.
    disjoint_mods c1 c2 ∧
    mods_wf c1 ∧
    mods_wf c2 ∧
    mod_steps k c1 n s1 t1 ∧
    mod_steps k c2 n s2 t2 ⇒
    mod_steps k (join c1 c2) n (s1 ∪ s2) (t1 ∪ t2)
Proof
  gen_tac \\ gen_tac \\ Induct \\ gvs [mod_steps_def]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum drule_all
  \\ rename [‘_ (u1 ∪ u2) (_ ∪ _)’]
  \\ disch_then $ irule_at Any

  \\ gvs [mod_step_def,join_def]
  \\ gvs [infl_union,mods_wf_def,disjoint_mods_def,disjoint_mod_def]
  \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [mod_wf_def]
  \\ DEP_REWRITE_TAC [infl_compose]
  \\ qabbrev_tac ‘u1 = step s1’
  \\ qabbrev_tac ‘u2 = step s2’
  \\ ‘u1 ⊆ infl s1’ by gvs [step_SUBSET_infl,Abbr‘u1’]
  \\ ‘u2 ⊆ infl s2’ by gvs [step_SUBSET_infl,Abbr‘u2’]
  \\ gvs [IN_DISJOINT,EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Definition join_all_def:
  join_all cst =
    λn. <| area           := U { (c n).area           | ∃s t. (c,s,t) ∈ cst } ;
           deletions      := U { (c n).deletions      | ∃s t. (c,s,t) ∈ cst } ;
           insertions     := U { (c n).insertions     | ∃s t. (c,s,t) ∈ cst } ;
           assert_area    := U { (c n).assert_area    | ∃s t. (c,s,t) ∈ cst } ;
           assert_content := U { (c n).assert_content | ∃s t. (c,s,t) ∈ cst } |>
End

Theorem infl_bigunion:
  infl (U ss) = U { infl s | s ∈ ss }
Proof
  cheat
QED

Theorem infl_compose_bigunion:
  (∀x y. x ∈ ss ∧ y ∈ ss ∧ x ≠ y ⇒ DISJOINT (infl x) (infl y))
  ⇒
  step (U ss) = U { step s | s ∈ ss }
Proof
  cheat
QED

Theorem mod_steps_compose_bigunion:
  ∀k cst n.
    (∀x y. x ∈ cst ∧ y ∈ cst ∧ x ≠ y ⇒ disjoint_mods (FST x) (FST y)) ∧
    (∀c s t. (c,s,t) ∈ cst ⇒ mods_wf c ∧ mod_steps k c n s t)
    ⇒
    mod_steps k (join_all cst) n
                (U { s | ∃c t. (c,s,t) ∈ cst })
                (U { t | ∃c s. (c,s,t) ∈ cst })
Proof
  Induct \\ gvs [mod_steps_def]
  >-
   (rw [] \\ simp [Once EXTENSION]
    \\ rw [] \\ eq_tac \\ rw []
    \\ res_tac \\ gvs [PULL_EXISTS]
    \\ first_x_assum $ irule_at Any \\ gvs [])
  \\ rpt strip_tac \\ gvs []
  \\ qabbrev_tac ‘cst1 = { (c,s1,t) | ∃s. (c,s,t) ∈ cst ∧ mod_step (c n) s s1 }’
  \\ last_x_assum $ qspecl_then [‘cst1’,‘n+1’] mp_tac
  \\ impl_tac
  >- cheat
  \\ strip_tac
  \\ ‘∀t. (∃c s. (c,s,t) ∈ cst1) ⇔ (∃c s. (c,s,t) ∈ cst)’ by cheat
  \\ gvs [] \\ pop_assum kall_tac
  \\ ‘join_all cst1 = join_all cst’ by cheat
  \\ gvs [] \\ pop_assum kall_tac
  \\ pop_assum $ irule_at Any
  \\ gvs [Abbr‘cst1’]
  \\ gvs [mod_step_def,join_all_def,infl_bigunion]
  \\ DEP_REWRITE_TAC [infl_compose_bigunion]
  \\ rpt conj_tac
  >-
   (gvs [] \\ rpt strip_tac
    \\ first_x_assum (fn th => qspec_then ‘c’ mp_tac th \\ qspec_then ‘c'’ mp_tac th)
    \\ disch_then $ drule_then strip_assume_tac
    \\ disch_then $ drule_then strip_assume_tac
    \\ last_x_assum $ dxrule_then $ dxrule
    \\ gvs [disjoint_mods_def]
    \\ gvs [disjoint_mod_def]
    \\ disch_then $ qspec_then ‘n’ assume_tac
    \\ metis_tac [IN_DISJOINT,SUBSET_DEF])
  >-
   (gvs [SUBSET_DEF] \\ rw []
    \\ first_x_assum $ drule_then $ strip_assume_tac
    \\ gvs [PULL_EXISTS]
    \\ last_x_assum $ irule_at $ Pos last \\ gvs [])
  >-
   (gvs [mods_wf_def,mod_wf_def]
    \\ irule EQ_TRANS
    \\ qexists_tac ‘U {step s ∩ (c n).assert_area | (∃c t. (c,s,t) ∈ cst)}’
    \\ conj_tac
    >- cheat
    \\ cheat)
  \\ cheat
QED

Theorem run_compose_bigunion:
  ∀k cst n.
    (∀x y. x ∈ cst ∧ y ∈ cst ∧ x ≠ y ⇒ disjoint_mods (FST x) (FST y)) ∧
    (∀c s t. (c,s,t) ∈ cst ⇒ mods_wf c ∧ run c s)
    ⇒
    run (join_all cst) (U { s | ∃c t. (c,s,t) ∈ cst })
Proof
  cheat (* true if the above is *)
QED

(*
  deletions and insertions --> assertions
*)

Definition can_assert_def:
  can_assert p c ⇔
    ∀n:num.
      p ∩ (c n).deletions ≠ EMPTY ⇒
      p ⊆ (c n).deletions ∧
      p ⊆ (c n).assert_area ∧
      (c n).insertions ∩ p = (c n).assert_content ∩ p
End

Definition assert_mod_def:
  assert_mod p m =
    if p ∩ m.deletions = EMPTY then m else
      m with <| insertions := m.insertions DIFF p ;
                deletions := m.deletions DIFF p |>
End

Definition assert_def:
  assert p c = λn. assert_mod p (c n)
End

Theorem to_assert:
  ∀k n s t.
    mod_steps k c n s t ∧
    can_assert p c
    ⇒
    mod_steps k (assert p c) n s t
Proof
  Induct
  \\ gvs [mod_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [mod_step_def,assert_def,assert_mod_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem to_assert_run:
  ∀c s.
    run c s ∧
    can_assert p c
    ⇒
    run (assert p c) s
Proof
  rw [run_def,run_to_def]
  \\ last_x_assum $ qspec_then ‘k’ strip_assume_tac
  \\ drule_all to_assert
  \\ disch_then $ irule_at Any
QED

(*
  deletions and insertions --> nop
*)

Definition del_io_mod_def:
  del_io_mod p m =
    if p ∩ m.deletions = EMPTY then m else
      m with <| assert_area := m.assert_area DIFF p ;
                assert_content := m.assert_content DIFF p ;
                insertions := m.insertions DIFF p ;
                deletions := m.deletions DIFF p |>
End

Definition del_io_def:
  del_io p c = λn. del_io_mod p (c n)
End

Theorem to_del_io:
  ∀k n s t.
    mod_steps k c n s t ∧
    can_assert p c
    ⇒
    mod_steps k (del_io p c) n s t
Proof
  Induct
  \\ gvs [mod_steps_def,PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [can_assert_def]
  \\ first_x_assum $ qspec_then ‘n’ assume_tac
  \\ gvs [mod_step_def,del_io_def,del_io_mod_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem to_assert_run:
  ∀c s.
    run c s ∧
    can_assert p c
    ⇒
    run (del_io p c) s
Proof
  rw [run_def,run_to_def]
  \\ last_x_assum $ qspec_then ‘k’ strip_assume_tac
  \\ drule_all to_del_io
  \\ disch_then $ irule_at Any
QED

(*
  translate by dx dy
*)

(*
  circuit conventions (set and list versions)
   - uses 75x75 coordinates
*)

Definition box_def:
  box (x:int,y:int) (w:num,h:num) = { (x + &i, y + &j) | i < w ∧ j < h }
End

Definition base_area_def:
  base_area area =
    U { box (75 * x - 75, 75 * y - 75) (150,150) | (x,y) ∈ area }
End

Definition io_box_def:
  io_box (x:int, y:int) =
    box (75 * x - 6, 75 * y - 6) (12, 12)
End

Datatype:
  dir = N | S | W | E
End

Definition circ_mod_wf_def:
  circ_mod_wf area ins outs as ⇔
    (∀x y. (x,y) ∈ area ⇒ x % 2 = 0 ∧ y % 2 = 0) ∧
    (∀x y r. ((x,y),r) ∈ ins ∪ outs ∪ as ⇒ ((x % 2 = 0) ≠ (y % 2 = 0))) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ ins ∧ ((x,y),r2) ∈ ins ⇒ r1 = r2) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ outs ∪ as ∧ ((x,y),r2) ∈ outs ∪ as ⇒ r1 = r2) ∧
    (∀x y r. ((x,y),N,r) ∈ ins ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ ins ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ ins ⇒ (x+1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ ins ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),N,r) ∈ outs ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ outs ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ outs ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ outs ⇒ (x+1,y) ∈ area)
End

Definition circ_area_def:
  circ_area area ins outs n =
    if n MOD 60 < 30 then
      base_area area DIFF
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {N;S} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {E;W} }) ∪
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {E;W} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {N;S} })
    else
      base_area area DIFF
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {E;W} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {N;S} }) ∪
      (U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ ins ∧ d ∈ {N;S} } ∪
       U { io_box (x,y) | ∃d r. ((x,y),d,r) ∈ outs ∧ d ∈ {E;W} })
End

Definition circ_io_area_def:
  circ_io_area outs n =
    if n MOD 60 = 29 then
      U { io_box (x,y) | ∃r. ((x,y),r) ∈ outs ∧ x % 2 = 0 }
    else if n MOD 60 = 59 then
      U { io_box (x,y) | ∃r. ((x,y),r) ∈ outs ∧ x % 2 ≠ 0 }
    else
      {}
End

Definition io_gate_def:
  io_gate E =
   [[F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;T;F;F;T;F];
    [F;F;F;F;F;F;F;F;F;T];
    [F;F;F;F;F;T;F;F;F;T];
    [F;F;F;F;F;F;T;T;T;T];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F]] ∧
  io_gate W =
   [[F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [T;T;T;T;F;F;F;F;F;F];
    [T;F;F;F;T;F;F;F;F;F];
    [T;F;F;F;F;F;F;F;F;F];
    [F;T;F;F;T;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F]] ∧
  io_gate N =
   [[F;F;T;T;T;F;F;F;F;F];
    [F;T;F;F;T;F;F;F;F;F];
    [F;F;F;F;T;F;F;F;F;F];
    [F;F;F;F;T;F;F;F;F;F];
    [F;T;F;T;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F]] ∧
  io_gate S =
   [[F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;F;F;F;F];
    [F;F;F;F;F;F;T;F;T;F];
    [F;F;F;F;F;T;F;F;F;F];
    [F;F;F;F;F;T;F;F;F;F];
    [F;F;F;F;F;T;F;F;T;F];
    [F;F;F;F;F;T;T;T;F;F]]
End

Definition from_row_def:
  from_row (x,y) [] = {} ∧
  from_row (x,y) (F::xs) = from_row (x+1:int,y:int) xs ∧
  from_row (x,y) (T::xs) = {(x,y)} ∪ from_row (x+1,y) xs
End

Definition from_rows_def:
  from_rows (x,y) [] = {} ∧
  from_rows (x,y) (row :: rows) = from_row (x,y) row ∪ from_rows (x,y+1) rows
End

Definition lwss_as_set_def:
  lwss_as_set (x,y) d = from_rows (x,y) (io_gate d)
End

Definition lwss_at_def:
  lwss_at n ((x,y),d,r) =
    if d ∈ {E; W} ∧ n MOD 60 = 59 ∧ r (n DIV 60) then
      lwss_as_set (75 * x - 5, 75 * y - 5) d
    else if d ∈ {N; S} ∧ n MOD 60 = 29 ∧ r (n DIV 60) then
      lwss_as_set (75 * x - 5, 75 * y - 5) d
    else
      {}
End

Definition circ_io_lwss_def:
  circ_io_lwss ins n = U (IMAGE (lwss_at n) ins )
End

Definition circ_mod_def:
  circ_mod area ins outs as n =
    <| area           := circ_area area ins outs n ;
       deletions      := circ_io_area outs n ;
       insertions     := circ_io_lwss ins n ;
       assert_area    := circ_io_area (outs ∪ as) n ;
       assert_content := circ_io_lwss (outs ∪ as) n |>
End

Theorem mods_wf_circ_mod:
  circ_mod_wf area ins outs as ⇒
  mods_wf (circ_mod area ins outs as)
Proof
  cheat
QED

Definition circuit_run_def:
  circuit_run area ins outs as init ⇔
    run (circ_mod area ins outs as) init ∧
    circ_mod_wf area ins outs as
End

Definition circuit_def:
  circuit area ins outs as init ⇔
    circuit_run (set area) (set ins) (set outs) (set as) init ∧
    ALL_DISTINCT area ∧
    ALL_DISTINCT (MAP FST ins) ∧
    ALL_DISTINCT (MAP FST outs) ∧
    ALL_DISTINCT (MAP FST as)
End

Theorem run_to_le:
  ∀k k0 c s t. run_to k c s t ∧ k0 ≤ k ⇒ ∃u. run_to k0 c s u
Proof
  cheat
QED

Theorem run_to_imp_run:
  ∀k c s.
    (∀n. ∃t. run_to (k * n) c s t) ∧ k ≠ 0 ⇒
    run c s
Proof
  rw [run_def] \\ rename [‘run_to k1’]
  \\ last_x_assum $ qspec_then ‘k1’ strip_assume_tac
  \\ irule run_to_le
  \\ pop_assum $ irule_at Any \\ gvs []
QED

Definition eval_io_def:
  eval_io env ins =
    MAP (λ((x,y),d,e). ((x,y),d, λn. eval (age n env) e)) ins
End

Theorem imp_circuit:
  (∀env.
    run_to 60
      (circ_mod (set area)
                (set (eval_io env ins))
                (set (eval_io env outs))
                {})
      (from_rows (x,y) (MAP (MAP (eval env)) rows))
      (from_rows (x,y) (MAP (MAP (eval (age 1 env))) rows)))
  ⇒
  circuit
    area
    (eval_io env ins)
    (eval_io env ins)
    []
    (from_rows (x,y) (MAP (MAP (eval env)) rows))
Proof
  cheat
QED





(*
params:
 - inputs
 - outputs
 - asserts
 - init state
sets:
 - area
 - insertions
 - deletions
 - state s
 - assertions
*)

val _ = export_theory();
