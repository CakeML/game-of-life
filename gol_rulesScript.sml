(*
  A formalisation of the rules of Conway's Game of Life (GOL).
*)
open preamble;

val _ = new_theory "gol_rules";

Overload "U" = “BIGUNION”;

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

Theorem IMP_infl_subset:
  s ⊆ COMPL (infl (COMPL t)) ⇒ infl s ⊆ t
Proof
  gvs [SUBSET_DEF] \\ gvs [IN_DEF, infl_def, FORALL_PROD]
  \\ gvs [live_adj_def,IN_DEF] \\ rw []
  \\ Cases_on ‘s (p_1,p_2)’ \\ gvs []
  \\ last_x_assum drule \\ gvs [integerTheory.INT_SUB_ADD]
  \\ gvs [intLib.COOPER_PROVE “m + k - k:int = m”]
QED

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
  rw [Once SET_EQ_SUBSET, BIGUNION_SUBSET]
  >-
   (fs [SUBSET_DEF, FORALL_PROD, infl_thm]
    \\ simp [GSYM EXISTS_OR_THM, GSYM RIGHT_AND_OVER_OR, GSYM infl_thm]
    \\ metis_tac [])
  \\ metis_tac [SUBSET_BIGUNION_I, infl_mono]
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

Theorem to_del_io_run:
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
  TODO: translate by dx dy
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

Definition is_ns_def:
  is_ns ((x,y),d,r) = (d = N ∨ d = S)
End

Definition is_ew_def:
  is_ew ((x,y),d,r) = (d = E ∨ d = W)
End

Definition circ_mod_wf_def:
  circ_mod_wf area ins outs as ⇔
    (∀x y. (x,y) ∈ area ⇒ x % 2 = 0 ∧ y % 2 = 0) ∧
    (∀x y r. ((x,y),r) ∈ ins ∪ outs ∪ as ⇒ ((x % 2 = 0) ≠ (y % 2 = 0))) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ ins ∧ ((x,y),r2) ∈ ins ⇒ r1 = r2) ∧
    (∀x y r1 r2. ((x,y),r1) ∈ outs ∪ as ∧ ((x,y),r2) ∈ outs ∪ as ⇒ r1 = r2) ∧
    (∀x y r. ((x,y),N,r) ∈ ins ∪ as ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ ins ∪ as ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ ins ∪ as ⇒ (x+1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ ins ∪ as ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),N,r) ∈ outs ∪ as ⇒ (x,y+1) ∈ area) ∧
    (∀x y r. ((x,y),S,r) ∈ outs ∪ as ⇒ (x,y-1) ∈ area) ∧
    (∀x y r. ((x,y),E,r) ∈ outs ∪ as ⇒ (x-1,y) ∈ area) ∧
    (∀x y r. ((x,y),W,r) ∈ outs ∪ as ⇒ (x+1,y) ∈ area) ∧
    (∀x y r. ((x,y),r) ∈ as ⇒ ∀q. ((x,y),q) ∉ ins ∧ ((x,y),q) ∉outs)
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
  circ_io_area outs =
    U { io_box (x,y) | ∃r. ((x,y),r) ∈ outs }
End

Definition circ_output_area_def:
  circ_output_area outs n =
    circ_io_area (if n MOD 60 = 29 then outs ∩ is_ns else
                  if n MOD 60 = 59 then outs ∩ is_ew else {})
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

Theorem from_rows_EMPTY:
  ∀x y.
    EVERY (EVERY (λx. x = F)) bools ⇒
    from_rows (x,y) bools = ∅
Proof
  Induct_on ‘bools’ \\ gvs [from_rows_def,SF SFY_ss]
  \\ Induct \\ gvs [from_row_def]
QED

Definition lwss_as_set_def:
  lwss_as_set (x,y) d = from_rows (x,y) (io_gate d)
End

Definition lwss_at_def:
  lwss_at n ((x,y),d,r) =
    if r (n DIV 60) then
      lwss_as_set (75 * x - 5, 75 * y - 5) d
    else
      {}
End

Definition circ_io_lwss_def:
  circ_io_lwss ins n =
    if n MOD 60 = 29 then
      U (IMAGE (lwss_at n) (ins ∩ is_ns) )
    else if n MOD 60 = 59 then
      U (IMAGE (lwss_at n) (ins ∩ is_ew) )
    else
      {}
End

Definition circ_mod_def:
  circ_mod area ins outs as n =
    <| area           := circ_area area ins outs n ;
       deletions      := circ_output_area outs n ;
       insertions     := circ_io_lwss ins n ;
       assert_area    := circ_output_area (outs ∪ as) n ;
       assert_content := circ_io_lwss (outs ∪ as) n |>
End

Theorem IN_from_row:
  ∀row i j x y.
    (x,y) ∈ from_row (i,j) row ⇔
    y = j ∧ ∃n. oEL n row = SOME T ∧ x = i + &n
Proof
  Induct \\ gvs [from_row_def,oEL_def]
  \\ rw [] \\ gvs [from_row_def,oEL_def]
  \\ Cases_on ‘h’ \\ gvs [from_row_def,oEL_def]
  \\ Cases_on ‘y = j’ \\ gvs []
  \\ eq_tac \\ rw []
  >- (qexists_tac ‘0’ \\ gvs [])
  >- (qexists_tac ‘n+1’ \\ gvs [] \\ intLib.COOPER_TAC)
  \\ gvs [AllCaseEqs()]
  >- (qexists_tac ‘n-1’ \\ gvs [] \\ intLib.COOPER_TAC)
  >- (qexists_tac ‘n+1’ \\ gvs [] \\ intLib.COOPER_TAC)
  >- (qexists_tac ‘n-1’ \\ gvs [] \\ intLib.COOPER_TAC)
QED

Theorem IN_from_rows:
  ∀rows i j x y.
    (x,y) ∈ from_rows (i,j) rows ⇔
      ∃dx dy row.
        x = i + & dx ∧ y = j + & dy ∧
        oEL dy rows = SOME row ∧
        oEL dx row = SOME T
Proof
  Induct \\ gvs [from_rows_def] \\ gvs [oEL_def,IN_from_row]
  \\ rpt gen_tac \\ eq_tac \\ strip_tac
  >- (pop_assum $ irule_at Any \\ qrefinel [‘_’,‘0’] \\ gvs [])
  >- (qrefinel [‘dx’,‘1+dy’] \\ gvs [] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘dy’ \\ gvs []
  \\ rpt $ pop_assum $ irule_at Any
  \\ intLib.COOPER_TAC
QED

Theorem io_gate_lenth:
  LENGTH (io_gate d) = 10 ∧
  ∀row. MEM row (io_gate d) ⇒ LENGTH row = 10
Proof
  Cases_on ‘d’ \\ gvs [io_gate_def, SF DNF_ss]
QED

Theorem lwss_at_imp_io_box:
  (x,y) ∈ lwss_at n ((i,j),r) ⇒ (x,y) ∈ io_box (i,j)
Proof
  PairCases_on ‘r’ \\ rw [lwss_at_def,io_box_def, lwss_as_set_def]
  \\ gvs [box_def,IN_from_rows]
  \\ qexists_tac ‘dx + 1’
  \\ qexists_tac ‘dy + 1’
  \\ qsuff_tac ‘dx < 10 ∧ dy < 10’ >- intLib.COOPER_TAC
  \\ gvs [oEL_THM]
  \\ rename [‘io_gate d’]
  \\ strip_assume_tac io_gate_lenth
  \\ gvs [MEM_EL,PULL_EXISTS]
QED

Theorem IN_io_box_io_box:
  (a0,a1) ∈ io_box (x,y) ⇒ ((a0,a1) ∈ io_box (x1,y1) ⇔ x = x1 ∧ y = y1)
Proof
  gvs [io_box_def,box_def] \\ intLib.COOPER_TAC
QED

Theorem mods_wf_circ_mod:
  circ_mod_wf area ins outs as ⇒
  mods_wf (circ_mod area ins outs as)
Proof
  rw [circ_mod_wf_def]
  \\ gvs [mods_wf_def,mod_wf_def,circ_mod_def] \\ rw []
  >-
   (gvs [circ_output_area_def,circ_area_def] \\ rw []
    \\ gvs [circ_io_area_def,SUBSET_DEF,PULL_EXISTS]
    \\ gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD]
    \\ metis_tac [])
  >-
   (gvs [circ_output_area_def,circ_area_def] \\ rw []
    \\ gvs [circ_io_area_def,SUBSET_DEF,PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ PairCases_on ‘r’ \\ gvs []
    >- (gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD] \\ metis_tac [])
    >-
     (disj1_tac
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ rename [‘a ∈ io_box (x,y)’] \\ PairCases_on ‘a’
      \\ ‘(x,y − 1) ∈ area ∧ (x,y + 1) ∈ area’ by
        (gvs [IN_DEF,is_ns_def,SF DNF_ss] \\ res_tac \\ gvs [])
      \\ drule IN_io_box_io_box
      \\ disch_then (fn th => rewrite_tac [th])
      \\ reverse conj_tac >- metis_tac []
      \\ gvs [base_area_def,PULL_EXISTS,box_def,io_box_def]
      \\ Cases_on ‘j < 6’
      >-
       (qexists_tac ‘x’ \\ qexists_tac ‘y-1’ \\ gvs []
        \\ qexists_tac ‘75 - 6 + i’
        \\ qexists_tac ‘150 - 6 + j’
        \\ intLib.COOPER_TAC)
      >-
       (qexists_tac ‘x’ \\ qexists_tac ‘y+1’ \\ gvs []
        \\ qexists_tac ‘75 - 6 + i’
        \\ qexists_tac ‘j - 6’
        \\ intLib.COOPER_TAC))
    >- (gvs [IN_DEF,is_ns_def,is_ew_def,EXISTS_PROD,FORALL_PROD] \\ metis_tac [])
    >-
     (disj1_tac
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ rename [‘a ∈ io_box (x,y)’] \\ PairCases_on ‘a’
      \\ ‘(x − 1,y) ∈ area ∧ (x + 1,y) ∈ area’ by
        (gvs [IN_DEF,is_ew_def,SF DNF_ss] \\ res_tac \\ gvs [])
      \\ drule IN_io_box_io_box
      \\ disch_then (fn th => rewrite_tac [th])
      \\ reverse conj_tac >- metis_tac []
      \\ gvs [base_area_def,PULL_EXISTS,box_def,io_box_def]
      \\ Cases_on ‘i < 6’
      >-
       (qexists_tac ‘x-1’ \\ qexists_tac ‘y’ \\ gvs []
        \\ qexists_tac ‘150 - 6 + i’
        \\ qexists_tac ‘75 - 6 + j’
        \\ intLib.COOPER_TAC)
      >-
       (qexists_tac ‘x+1’ \\ qexists_tac ‘y’ \\ gvs []
        \\ qexists_tac ‘i - 6’
        \\ qexists_tac ‘75 - 6 + j’
        \\ intLib.COOPER_TAC)))
  \\ rw [circ_io_lwss_def]
  \\ simp [circ_io_area_def,circ_output_area_def,
           SUBSET_DEF,FORALL_PROD,PULL_EXISTS,EXISTS_PROD]
  \\ rewrite_tac [GSYM AND_IMP_INTRO]
  \\ rpt gen_tac
  \\ rpt $ disch_then assume_tac
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ imp_res_tac lwss_at_imp_io_box \\ gvs []
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

Theorem mod_steps_add:
  ∀k c n s1 s2.
    mod_steps (l + k) c n s1 s2 ⇔
    ∃s3. mod_steps k c n s1 s3 ∧ mod_steps l c (n + k) s3 s2
Proof
  Induct_on ‘k’ \\ gvs []
  \\ once_rewrite_tac [mod_steps_def] \\ gvs [ADD_CLAUSES]
  \\ gvs [mod_steps_def] \\ gvs [PULL_EXISTS,ADD1]
  \\ metis_tac []
QED

Theorem run_to_le:
  ∀k k0 c s t. run_to k c s t ∧ k0 ≤ k ⇒ ∃u. run_to k0 c s u
Proof
  rw [] \\ gvs [LESS_EQ_EXISTS,run_to_def]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [mod_steps_add] \\ rw []
  \\ first_x_assum $ irule_at Any
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

Datatype:
  var = A | B
End

Datatype:
  bexp = True | False | Var var num
       | Not bexp | And bexp bexp | Or bexp bexp
End

Definition eval_def[simp]:
  eval env True      = T ∧
  eval env False     = F ∧
  eval env (Var v n) = env (v,n) ∧
  eval env (Not x)   = ~(eval env x) ∧
  eval env (And x y) = (eval env x ∧ eval env y) ∧
  eval env (Or x y) = (eval env x ∨ eval env y)
End

Definition age_def[simp]:
  age k env (v,n) = env (v,n+k:num)
End

Definition eval_io_def:
  eval_io env ins =
    MAP (λ((x,y),d,e). ((x,y),d, λn. eval (age n env) e)) ins
End

Theorem MAP_FST_eval_io[simp]:
  MAP FST (eval_io env ins) = MAP FST ins
Proof
  Induct_on ‘ins’ \\ gvs [eval_io_def,FORALL_PROD]
QED

Theorem mod_steps_age:
  ∀k c n s t. mod_steps k c n s t ⇔ mod_steps k (λl. c (l + n)) 0 s t
Proof
  Induct
  \\ once_rewrite_tac [mod_steps_def] >- simp []
  \\ pop_assum $ once_rewrite_tac o single \\ gvs []
QED

Theorem circ_area_age:
  circ_area (set area) (set (eval_io (age 1 env) ins))
            (set (eval_io (age 1 env) outs)) l =
  circ_area (set area) (set (eval_io env ins))
            (set (eval_io env outs)) (l + 60)
Proof
  gvs [circ_area_def,eval_io_def,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
QED

Theorem circ_output_area_age:
  circ_output_area (set (eval_io (age 1 env) outs)) l =
  circ_output_area (set (eval_io env outs)) (l + 60)
Proof
  gvs [circ_output_area_def,eval_io_def,circ_io_area_def] \\ rw []
  \\ gvs [MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ rw []
  \\ gvs [IN_DEF,is_ew_def,is_ns_def]
QED

Theorem age_age:
  age n (age k x) = age (n + k) x
Proof
  gvs [age_def,FUN_EQ_THM,FORALL_PROD]
QED

Theorem circ_io_lwss_age:
  circ_io_lwss (set (eval_io (age 1 env) ins)) l =
  circ_io_lwss (set (eval_io env ins)) (l + 60)
Proof
  simp [EXTENSION]
  \\ gvs [circ_io_lwss_def,eval_io_def] \\ rw []
  \\ gvs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,lwss_at_def,age_age]
  \\ ‘0 < 60:num’ by gvs []
  \\ drule arithmeticTheory.ADD_DIV_ADD_DIV
  \\ disch_then $ qspec_then ‘1’ assume_tac \\ gvs []
  \\ gvs [IN_DEF,is_ns_def,is_ew_def]
QED

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
  ALL_DISTINCT (MAP FST ins) ∧
  ALL_DISTINCT (MAP FST outs) ∧
  ALL_DISTINCT area ∧
  circ_mod_wf (set area) (set (eval_io env ins)) (set (eval_io env outs)) ∅
  ⇒
  circuit
    area
    (eval_io env ins)
    (eval_io env outs)
    []
    (from_rows (x,y) (MAP (MAP (eval env)) rows))
Proof
  rpt strip_tac
  \\ simp [circuit_def,circuit_run_def]
  \\ irule run_to_imp_run
  \\ qexists_tac ‘60’ \\ simp []
  \\ pop_assum kall_tac
  \\ qid_spec_tac ‘env’
  \\ Induct_on ‘n’
  >- gvs [run_to_def,mod_steps_def]
  \\ rpt strip_tac
  \\ gvs [run_to_def,mod_steps_def,MULT_CLAUSES]
  \\ simp [mod_steps_add]
  \\ last_x_assum $ qspec_then ‘env’ $ irule_at Any
  \\ first_x_assum $ qspec_then ‘age 1 env’ strip_assume_tac
  \\ once_rewrite_tac [mod_steps_age]
  \\ qsuff_tac
     ‘circ_mod (set area) (set (eval_io (age 1 env) ins))
        (set (eval_io (age 1 env) outs)) ∅  =
      λl. circ_mod (set area) (set (eval_io env ins))
                   (set (eval_io env outs)) ∅  (l + 60)’
  >- (rw [] \\ qexists_tac ‘t’ \\ gvs [])
  \\ gvs [FUN_EQ_THM,circ_mod_def]
  \\ gvs [circ_area_def,circ_io_lwss_age,circ_area_age,circ_output_area_age]
QED

Definition bvar_lt_def:
  bvar_lt (n1,g1) (n2,g2:num) =
    if n1 = n2 then g1 ≤ g2 else n1 = A
End

Definition add_to_sorted_def:
  add_to_sorted [] v = [v] ∧
  add_to_sorted (x::xs) v =
    if bvar_lt x v then x :: add_to_sorted xs v else
    if x = v then x :: xs else v :: x :: xs
End

Definition get_bvars_def:
  get_bvars False acc = acc ∧
  get_bvars True acc = acc ∧
  get_bvars (Not x) acc = get_bvars x acc ∧
  get_bvars (Or x y) acc = get_bvars x (get_bvars y acc) ∧
  get_bvars (And x y) acc = get_bvars x (get_bvars y acc) ∧
  get_bvars (Var n g) acc = add_to_sorted acc (n,g)
End

Definition build_Not_def:
  build_Not x =
    case x of
    | True => False
    | False => True
    | Not y => y
    | _ => Not x
End

Definition build_If_def:
  build_If x y z =
    if y = z then y else
    if y = True ∧ z = False then x else
    if y = False ∧ z = True then build_Not x else
    if z = False then And x y else
    if y = True then Or x z else
    if z = True then Or y (build_Not x) else
    if y = False then And z (build_Not x) else
      Or (And x y) (And (build_Not x) z)
End

Definition build_Or_def:
  build_Or x y =
    if x = True then True else
    if y = True then True else
    if x = False then y else
    if y = False then x else
      Or x y
End

Theorem eval_build_Or[simp]:
  eval env (build_Or x y) = eval env (Or x y)
Proof
  rw [build_Or_def]
QED

Definition get_bvars8_def:
  get_bvars8 (y1,y2,y3,y4,y5,y6,y7,y8) =
    (get_bvars y1 $ get_bvars y2 $ get_bvars y3 $ get_bvars y4 $
     get_bvars y5 $ get_bvars y6 $ get_bvars y7 $ get_bvars y8 [])
End

Definition eval_bexp_def[simp]:
  eval_bexp env True      = T ∧
  eval_bexp env False     = F ∧
  eval_bexp env (Not x)   = ~(eval_bexp env x) ∧
  eval_bexp env (And x y) = (eval_bexp env x ∧ eval_bexp env y) ∧
  eval_bexp env (Or x y)  = (eval_bexp env x ∨ eval_bexp env y) ∧
  eval_bexp env (Var v n) = case ALOOKUP env (v,n) of SOME b => b | NONE => F
End

Definition eval_bexp8_def:
  eval_bexp8 env (y1,y2,y3,y4,y5,y6,y7,y8) =
    b2n (eval_bexp env y1) +
    b2n (eval_bexp env y2) +
    b2n (eval_bexp env y3) +
    b2n (eval_bexp env y4) +
    b2n (eval_bexp env y5) +
    b2n (eval_bexp env y6) +
    b2n (eval_bexp env y7) +
    b2n (eval_bexp env y8)
End

Definition count_falses_def:
  count_falses x (y1,y2,y3,y4,y5,y6,y7,y8) =
    b2n (x  = False) +
    b2n (y1 = False) +
    b2n (y2 = False) +
    b2n (y3 = False) +
    b2n (y4 = False) +
    b2n (y5 = False) +
    b2n (y6 = False) +
    b2n (y7 = False) +
    b2n (y8 = False)
End

Definition to_bexp_def[simp]:
  to_bexp T = True ∧
  to_bexp F = False
End

Definition gol_eval_def:
  gol_eval vars env x ys =
    case vars of
    | ((n,g)::vs) =>
        build_If (Var n g)
          (gol_eval vs (((n,g),T)::env) x ys)
          (gol_eval vs (((n,g),F)::env) x ys)
    | [] =>
        let k = eval_bexp8 env ys in
        let mid = eval_bexp env x in
          to_bexp (if mid then (k = 2 ∨ k = 3) else (k = 3))
End

Definition gol_cell_def:
  gol_cell x ys =
    if count_falses x ys >= 7 then False else
      let vars = get_bvars x (get_bvars8 ys) in
        gol_eval vars [] x ys
End

Definition hd_or_false_def:
  hd_or_false [] = False ∧
  hd_or_false (x::xs) = x
End

Definition gol_row_def:
  gol_row x0 (x1::xs)
          y0 (y1::ys)
          z0 (z1::zs) =
    gol_cell y1 (x0, x1, hd_or_false xs,
                 y0,     hd_or_false ys,
                 z0, z1, hd_or_false zs) ::
    gol_row x1 xs
            y1 ys
            z1 zs ∧
  gol_row _ _ _ _ _ _ = []
End

Definition gol_rows_def:
  gol_rows prev (row :: rest) =
    gol_row False prev
            False row
            False (case rest of
                   | [] => REPLICATE (LENGTH row) False
                   | r :: _ => r)
    :: gol_rows row rest ∧
  gol_rows prev [] = []
End

Definition gol_step_rows_def:
  gol_step_rows [] = [] ∧
  gol_step_rows (x::xs) = gol_rows (REPLICATE (LENGTH x) False) (x::xs)
End

Definition check_mask1_def:
  (* check_mask1 = LIST_REL (λe m. m ∨ e = False) *)
  (check_mask1 [] [] ⇔ T) ∧ (check_mask1 (a::as) [] ⇔ F) ∧
  (check_mask1 [] (b::bs) ⇔ F) ∧
  (check_mask1 (a::as) (b::bs) ⇔ (b ∨ a = False) ∧ check_mask1 as bs)
End

Definition check_mask_def':
  (* check_mask = LIST_REL (LIST_REL (λe m. m ∨ e = False)) *)
  (check_mask [] [] ⇔ T) ∧ (check_mask (a::as) [] ⇔ F) ∧
  (check_mask [] (b::bs) ⇔ F) ∧
  (check_mask (a::as) (b::bs) ⇔ check_mask1 a b ∧ check_mask as bs)
End

Theorem check_mask_def:
  ∀rows mask.
    check_mask rows mask =
    LIST_REL (λr m. LIST_REL (λe m. m ∨ e = False) r m) rows mask
Proof
  Induct \\ Cases_on ‘mask’ \\ gvs [check_mask_def']
  \\ qsuff_tac ‘∀x y. check_mask1 x y = LIST_REL (λe m. m ∨ e = False) x y’ >- gvs []
  \\ Induct \\ Cases_on ‘y’ \\ gvs [check_mask1_def]
QED

Definition gol_checked_steps_def:
  gol_checked_steps 0 rows mask = SOME rows ∧
  gol_checked_steps (SUC n) rows mask =
    if check_mask rows mask then
      gol_checked_steps n (gol_step_rows rows) mask
    else NONE
End

Definition inc_def:
  inc (Var n g) = Var n (g+1) ∧
  inc (And x y) = And (inc x) (inc y) ∧
  inc (Or x y)  = Or (inc x) (inc y) ∧
  inc (Not x)   = Not (inc x) ∧
  inc True      = True ∧
  inc False     = False
End

Definition inc_vars_def:
  inc_vars rows = MAP (MAP inc) rows
End

Definition or_row_def:
  or_row x p [] = [] ∧
  or_row x [] row = row ∧
  or_row x (p::pat) (r::row) =
    if x = 0:num then build_Or p r :: or_row x pat row else
      r :: or_row (x-1) (p::pat) row
End

Definition or_at_def:
  or_at x y pat [] = [] ∧
  or_at x y [] (row::rows) = row::rows ∧
  or_at x y (p::pat) (row::rows) =
    if y = 0:num then or_row x p row :: or_at x y pat rows else
      row :: or_at x (y-1) (p::pat) rows
End

Definition or_lwss_def:
  or_lwss rows [] = SOME rows ∧
  or_lwss rows (((x,y),d,v)::rest) =
    case or_lwss rows rest of
    | NONE => NONE
    | SOME rows1 =>
        SOME (or_at (Num (x * 75 - 5 + 85)) (Num (y * 75 - 5 + 85))
               (MAP (MAP (λb. if b then v else False)) (io_gate d)) rows1)
End

(*

Definition tabulate_def:
  tabulate (f:int -> int -> 'a) rows =
    MAPi (λy row. MAPi (λx u. f (& x) (& y)) row) rows
End

Definition mask_cell_def:
  mask_cell phase1 area ins outs x y ⇔
    (x, y) ∈ infl (COMPL (circ_area (set area) (set ins) (set outs) (if phase1 then 0 else 30)))
End

Definition io_area_cell_def:
  io_area_cell phase1 outs x y ⇔
    (x, y) ∈  circ_output_area (set outs) (if phase1 then 29 else 59)
End

*)

Definition diff_rows_def:
  diff_rows (rows : bexp list list) (bools: bool list list) =
    MAP2 (λrow bs. MAP2 (λr b. if b then False else r) row bs) rows bools
End

Definition inter_rows_def:
  inter_rows (rows : bexp list list) (bools: bool list list) =
    MAP2 (λrow bs. MAP2 (λr b. if b then r else False) row bs) rows bools
End

Definition make_area_def:
  make_area w h = FLAT (GENLIST (λy. GENLIST (λx. (2 * &x:int, 2 * &y:int)) w) h)
End

Definition add_margin_def:
  add_margin fill n xss =
    let ys = REPLICATE n fill in
    let yss = MAP (λxs. ys ++ xs ++ ys) xss in
    let l = (case yss of (row::_) => LENGTH row | _ => n+n) in
    let ts = REPLICATE n (REPLICATE l fill) in
      ts ++ yss ++ ts
End

Definition make_base_area_def:
  make_base_area w h =
    let trues = REPLICATE (h * 150) (REPLICATE (w * 150) T) in
      add_margin F 10 trues : bool list list
End

Definition shrink_row_def:
  shrink_row (x1::x2::x3::xs)
             (y1::y2::y3::ys)
             (z1::z2::z3::zs) =
    ((x1 ∧ x2 ∧ x3 ∧ y1 ∧ y2 ∧ y3 ∧ z1 ∧ z2 ∧ z3) :: shrink_row (x2::x3::xs)
                                                                (y2::y3::ys)
                                                                (z2::z3::zs)) ∧
  shrink_row _ _ _ = []
End

Definition shrink_all_def:
  shrink_all (r1::r2::r3::rest) =
    shrink_row r1 r2 r3 :: shrink_all (r2::r3::rest) ∧
  shrink_all _ = []
End

Definition shrink_def:
  shrink xs = add_margin F 1 (shrink_all xs)
End

Definition or_box_row_def:
  or_box_row x w [] = [] ∧
  or_box_row x w (r::rs) =
    if x = 0:num then if w = 0:num then r :: rs else T :: or_box_row x (w-1) rs
    else r :: or_box_row (x-1) w rs
End

Definition or_box_def:
  or_box x y w h [] = [] ∧
  or_box x y w h (r::rs) =
    if y = 0:num then
      if h = 0:num then r :: rs else
        or_box_row x w r :: or_box x y w (h-1) rs
    else
      r :: or_box x (y-1) w h rs
End

Definition or_io_areas_def:
  or_io_areas [] t = t ∧
  or_io_areas (((x,y),r)::rest) t =
    or_box (Num (85 + 75 * x - 6)) (Num (85 + 75 * y - 6)) 12 12
      (or_io_areas rest t)
End

Definition rectangle_def:
  rectangle w h rows ⇔
    LENGTH rows = 150 * h + 20 ∧
    EVERY (λrow. LENGTH row = 150 * w + 20) rows
End

Theorem or_box_row_length:
  ∀xs x m. LENGTH (or_box_row x m xs) = LENGTH xs
Proof
  Induct \\ gvs [or_box_row_def] \\ rw []
QED

Theorem LIST_REL_or_box:
  ∀xs ys x y m n.
    LIST_REL (λx y. LENGTH x = LENGTH y) xs ys ⇒
    LIST_REL (λx y. LENGTH x = LENGTH y) (or_box x y m n xs) ys
Proof
  Induct \\ gvs [or_box_def,PULL_EXISTS,SF SFY_ss] \\ rw []
  \\ gvs [or_box_row_length]
QED

Theorem or_io_areas_rectangle:
  or_io_areas xs t = res ∧
  rectangle w h t ⇒
  rectangle w h res
Proof
  rw [] \\ gvs [rectangle_def]
  \\ qsuff_tac ‘LIST_REL (λx y. LENGTH x = LENGTH y) (or_io_areas xs t) t’
  >- gvs [LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS,SF SFY_ss]
  \\ rpt $ pop_assum kall_tac
  \\ qid_spec_tac ‘t’
  \\ Induct_on ‘xs’ \\ gvs [or_io_areas_def,FORALL_PROD]
  >- gvs [LIST_REL_EL_EQN]
  \\ rw [] \\ irule LIST_REL_or_box \\ gvs []
QED

Definition or_def:
  or xss yss =
    MAP2 (λxs ys. MAP2 (λx y. x ∨ y) xs ys) xss yss
    : bool list list
End

Definition diff_def:
  diff (xss : bool list list) (yss : bool list list) =
    MAP2 (λxs ys. MAP2 (λx y. if y then F else x) xs ys) xss yss
    : bool list list
End

Definition masks_def:
  masks w h ins outs =
    let base_area_bools = make_base_area w h in
    let bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F) in
    let sets1 = or_io_areas (FILTER is_ns ins ++ FILTER is_ew outs) bools in
    let sets2 = or_io_areas (FILTER is_ew ins ++ FILTER is_ns outs) bools in
      (or sets2 (diff base_area_bools sets1),
       or sets1 (diff base_area_bools sets2))
End

Definition simple_checks_def:
  simple_checks w h ins outs rows ⇔
    rectangle w h rows ∧ h ≠ 0 ∧ w ≠ 0 ∧
    ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
    EVERY (λ((x,y),r).
             (x % 2 = 0 ⇎ y % 2 = 0) ∧
             -1 ≤ x ∧ -1 ≤ y ∧ x ≤ 2 * &w - 1 ∧ y ≤ 2 * &h - 1)
          (ins ++ outs) ∧
    let area = make_area w h in
      ALL_DISTINCT area ∧
      EVERY (λ((x,y),d,r). d = N ⇒ MEM (x,y-1) area) ins ∧
      EVERY (λ((x,y),d,r). d = S ⇒ MEM (x,y+1) area) ins ∧
      EVERY (λ((x,y),d,r). d = E ⇒ MEM (x+1,y) area) ins ∧
      EVERY (λ((x,y),d,r). d = W ⇒ MEM (x-1,y) area) ins ∧
      EVERY (λ((x,y),d,r). d = N ⇒ MEM (x,y+1) area) outs ∧
      EVERY (λ((x,y),d,r). d = S ⇒ MEM (x,y-1) area) outs ∧
      EVERY (λ((x,y),d,r). d = E ⇒ MEM (x-1,y) area) outs ∧
      EVERY (λ((x,y),d,r). d = W ⇒ MEM (x+1,y) area) outs
End

Definition simulation_ok_def:
  simulation_ok w h ins outs rows ⇔
    simple_checks w h ins outs rows ∧
    let bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F) in
    let (m1,m2) = masks w h ins outs in
    let del1 = or_io_areas (FILTER is_ns outs) bools in
    let del2 = or_io_areas (FILTER is_ew outs) bools in
    let ins1 = FILTER is_ns ins in
    let ins2 = FILTER is_ew ins in
    let outs1 = FILTER is_ns outs in
    let outs2 = FILTER is_ew outs in
    let empty = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) False) in
      case gol_checked_steps 30 rows (shrink m1) of
      | NONE => F
      | SOME rows1 =>
        if or_lwss empty outs1 ≠ SOME (inter_rows rows1 del1) then F else
          case or_lwss (diff_rows rows1 del1) ins1 of
          | NONE => F
          | SOME rowsA =>
            case gol_checked_steps 30 rowsA (shrink m2) of
            | NONE => F
            | SOME rows2 =>
                if or_lwss empty outs2 ≠ SOME (inter_rows rows2 del2) then F else
                  case or_lwss (diff_rows rows2 del2) ins2 of
                  | NONE => F
                  | SOME rowsB =>
                     inc_vars rows = rowsB
End

Theorem opt_bool =
  “option_CASE x F h = T” |> SCONV [AllCaseEqs()] |> SRULE [];

Definition steps_def:
  steps s1 t s2 ⇔
    s2 = FUNPOW step 30 s1 ∧
    ∀n. n < 30 ⇒ infl (FUNPOW step n s1) ⊆ t
End

Theorem mod_steps_FUNPOW:
  ∀k n s cc.
    (∀i. i < k ⇒
         infl (FUNPOW step i s) ⊆ (cc (i + n)).area ∧
         (cc (i + n)).assert_area = {} ∧
         (cc (i + n)).assert_content = {} ∧
         (cc (i + n)).deletions = {} ∧
         (cc (i + n)).insertions = {}) ⇒
    mod_steps k cc n s (FUNPOW step k s)
Proof
  Induct \\ gvs [mod_steps_def] \\ rw [] \\ gvs [FUNPOW]
  \\ last_x_assum $ irule_at Any \\ conj_tac
  >- (gen_tac \\ strip_tac
      \\ last_x_assum $ qspec_then ‘SUC i’ mp_tac \\ gvs [FUNPOW,ADD1])
  \\ gvs [mod_step_def]
  \\ pop_assum $ qspec_then ‘0’ assume_tac \\ gvs []
QED

Theorem circ_io_lwss_empty:
  i < 29 ⇒ circ_io_lwss ins i = ∅ ∧ circ_io_lwss ins (i + 30) = ∅
Proof
  simp [EXTENSION]
  \\ gvs [circ_io_lwss_def]
  \\ gvs [FORALL_PROD]
  \\ gvs [lwss_at_def]
  \\ CCONTR_TAC \\ gvs []
QED

Triviality run_to_60_lemma:
  (∃s1 s2 s3.
    steps s (circ_area area ins outs 0) s1 ∧
    s1 ∩ circ_output_area (outs ∪ as) 29 = circ_io_lwss (outs ∪ as) 29 ∧
    s2 = circ_io_lwss ins 29 ∪ (s1 DIFF circ_output_area outs 29) ∧
    steps s2 (circ_area area ins outs 30) s3 ∧
    s3 ∩ circ_output_area (outs ∪ as) 59 = circ_io_lwss (outs ∪ as) 59 ∧
    t = circ_io_lwss ins 59 ∪ (s3 DIFF circ_output_area outs 59))
  ⇒
  run_to 60 (circ_mod area ins outs as) s t
Proof
  strip_tac
  \\ gvs [run_to_def]
  \\ rewrite_tac [EVAL “30 + 30:num” |> GSYM]
  \\ rewrite_tac [mod_steps_add] \\ gvs []
  \\ qexists_tac ‘circ_io_lwss ins 29 ∪ (s1 DIFF circ_output_area outs 29)’
  \\ conj_tac
  >-
   (ntac 2 (pop_assum kall_tac) \\ gvs [steps_def]
    \\ simp [mod_steps_def]
    \\ rewrite_tac [EVAL “1 + 29:num” |> GSYM]
    \\ rewrite_tac [mod_steps_add] \\ gvs []
    \\ qexists_tac ‘FUNPOW step 29 s’
    \\ conj_tac
    >- (irule mod_steps_FUNPOW \\ gvs [circ_mod_def,circ_area_def]
        \\ gvs [circ_output_area_def,circ_io_lwss_empty,circ_io_area_def])
    \\ ntac 2 $ simp [Once (oneline mod_steps_def)]
    \\ gvs [mod_step_def,circ_mod_def,SF SFY_ss]
    \\ ‘step (FUNPOW step 29 s) = FUNPOW step 30 s’
         by rewrite_tac [EVAL “SUC 29” |> GSYM, FUNPOW_SUC]
    \\ gvs [] \\ gvs [circ_area_def])
  \\ last_x_assum kall_tac
  \\ last_x_assum kall_tac
  \\ qabbrev_tac ‘t5 = circ_io_lwss ins 29 ∪ (s1 DIFF circ_output_area outs 29)’
  \\ pop_assum kall_tac
  \\ rewrite_tac [EVAL “1 + 29:num” |> GSYM]
  \\ rewrite_tac [mod_steps_add] \\ gvs []
  \\ qexists_tac ‘FUNPOW step 29 t5’
  \\ gvs [steps_def]
  \\ conj_tac
  >- (irule mod_steps_FUNPOW \\ gvs [circ_mod_def,circ_area_def]
      \\ gvs [circ_output_area_def,circ_io_lwss_empty,circ_io_area_def])
  \\ ntac 2 $ simp [Once (oneline mod_steps_def)]
  \\ gvs [mod_step_def,circ_mod_def,SF SFY_ss]
  \\ ‘step (FUNPOW step 29 t5) = FUNPOW step 30 t5’
    by rewrite_tac [EVAL “SUC 29” |> GSYM, FUNPOW_SUC]
  \\ gvs [] \\ gvs [circ_area_def]
QED

Theorem length_gol_row:
  ∀xs ys zs x1 y1 z1.
    LENGTH xs = LENGTH ys ∧ LENGTH zs = LENGTH ys ⇒
    LENGTH (gol_row x1 xs y1 ys z1 zs) = LENGTH ys
Proof
  Induct \\ gvs [gol_row_def]
  \\ Cases_on ‘ys’ \\ gvs []
  \\ Cases_on ‘zs’ \\ gvs []
  \\ gvs [SF SFY_ss,gol_row_def]
QED

Theorem gol_rows_length:
  ∀rows prev.
    EVERY (λrow. LENGTH row = LENGTH prev) rows ⇒
    LIST_REL (λx y. LENGTH x = LENGTH y) rows (gol_rows prev rows)
Proof
  Induct \\ gvs [gol_rows_def] \\ rw []
  \\ DEP_REWRITE_TAC [length_gol_row] \\ gvs []
  \\ Cases_on ‘rows’ \\ gvs []
  \\ Cases_on ‘h’ \\ gvs []
  \\ Cases_on ‘prev’ \\ gvs []
  \\ DEP_REWRITE_TAC [length_gol_row] \\ gvs []
  \\ Cases_on ‘h'’ \\ gvs []
  \\ DEP_REWRITE_TAC [length_gol_row] \\ gvs []
QED

Theorem gol_step_rows_length:
  ∀rows k.
    EVERY (λrow. LENGTH row = k) rows ⇒
    LIST_REL (λx y. LENGTH x = LENGTH y) rows (gol_step_rows rows)
Proof
  gen_tac \\ Cases_on ‘rows = []’ \\ gvs [gol_step_rows_def]
  \\ ‘gol_step_rows rows = gol_rows (REPLICATE (LENGTH (HD rows)) False) rows’ by
       (Cases_on ‘rows’ \\ gvs [gol_step_rows_def])
  \\ gvs [] \\ rw []
  \\ irule gol_rows_length \\ gvs []
  \\ Cases_on ‘rows’ \\ gvs []
QED

Theorem gol_step_rows_rectangle:
  rectangle w h rows ⇒
  rectangle w h (gol_step_rows rows)
Proof
  rw [rectangle_def]
  \\ qspec_then ‘rows’ drule gol_step_rows_length
  \\ gvs [LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS,EVERY_MEM]
QED

Theorem gol_checked_steps_rectangle:
  ∀n rows m1 rows1.
    gol_checked_steps n rows m1 = SOME rows1 ∧
    rectangle w h rows ⇒
    rectangle w h rows1
Proof
  Induct \\ gvs [gol_checked_steps_def] \\ rw []
  \\ last_x_assum $ drule_then irule
  \\ irule gol_step_rows_rectangle \\ gvs []
QED

Theorem oEL_MAP_EQ_SOME:
  ∀xs f n y.
    LLOOKUP (MAP f xs) n = SOME y ⇔
    ∃x. LLOOKUP xs n = SOME x ∧ y = f x
Proof
  Induct \\ gvs [oEL_def] \\ rw [] \\ eq_tac \\ rw []
QED

Theorem LLOOKUP_gol_row:
  ∀xs ys zs x y z n res.
    LLOOKUP (gol_row x xs y ys z zs) n = SOME res ⇔
    n < LENGTH xs ∧ n < LENGTH ys ∧ n < LENGTH zs ∧
    res = gol_cell (EL n ys)
            ((if n = 0 then x else EL (n-1) xs),
             EL n xs,
             (if n+1 < LENGTH xs then EL (n+1) xs else False),
             (if n = 0 then y else EL (n-1) ys),
             (if n+1 < LENGTH ys then EL (n+1) ys else False),
             (if n = 0 then z else EL (n-1) zs),
             EL n zs,
             (if n+1 < LENGTH zs then EL (n+1) zs else False))
Proof
  Induct \\ Cases_on ‘ys’ \\ Cases_on ‘zs’ \\ gvs [gol_row_def,oEL_def]
  \\ rpt gen_tac \\ Cases_on ‘n’ \\ gvs []
  \\ ‘∀xs. (if 1 < SUC (LENGTH xs) then HD xs else False) = hd_or_false xs’
       by (Cases \\ gvs [hd_or_false_def]) \\ gvs []
  >- (eq_tac \\ rw [])
  \\ gvs [ADD_CLAUSES]
  \\ Cases_on ‘n' ’ \\ gvs []
QED

Theorem LLOOKUP_gol_rows:
  ∀xs prev n ys.
    LLOOKUP (gol_rows prev xs) n = SOME ys ⇔
    n < LENGTH xs ∧
    ys = gol_row False (if n = 0 then prev else EL (n-1) xs)
                 False (EL n xs)
                 False (if n+1 < LENGTH xs then EL (n+1) xs
                        else REPLICATE (LENGTH (EL n xs)) False)
Proof
  Induct \\ gvs [gol_rows_def,oEL_def] \\ rpt gen_tac
  \\ IF_CASES_TAC
  >- (gvs [] \\ Cases_on ‘xs’ \\ gvs []
      \\ rw [] \\ eq_tac \\ rw [])
  \\ gvs [GSYM ADD1]
  \\ Cases_on ‘n’ \\ gvs [] \\ gvs [ADD1]
  \\ Cases_on ‘xs’ \\ gvs []
  \\ Cases_on ‘n'’ \\ gvs []
QED

Definition decide_step_def:
  decide_step y2 (x1,x2,x3,y1,y3,z1,z2,z3) =
    if y2 then
      b2n x1 + b2n x2 + b2n x3 +
      b2n y1 +          b2n y3 +
      b2n z1 + b2n z2 + b2n z3 ∈ {2;3}
    else
      b2n x1 + b2n x2 + b2n x3 +
      b2n y1 +          b2n y3 +
      b2n z1 + b2n z2 + b2n z3 = 3
End

Theorem IN_step_lemma:
  (x,y) ∈ step s ⇔
  decide_step ((x,y) ∈ s)
    ((x-1,y-1) ∈ s, (x,y-1) ∈ s, (x+1,y-1) ∈ s,
     (x-1,y)   ∈ s,              (x+1,y  ) ∈ s,
     (x-1,y+1) ∈ s, (x,y+1) ∈ s, (x+1,y+1) ∈ s)
Proof
  gvs [step_def,IN_DEF,live_adj_def,decide_step_def]
QED

Theorem y_SUB_IN_from_rows:
  (x,y-1) ∈ from_rows (a,b) rows ⇔ (x,y) ∈ from_rows (a,b) ([]::rows)
Proof
  gvs [IN_from_rows,oEL_def]
  \\ rw [] \\ eq_tac \\ rw []
  \\ gvs [SF intLib.INT_ARITH_ss]
  >- (qexists_tac ‘dy+1’ \\ gvs [SF intLib.INT_ARITH_ss])
  \\ Cases_on ‘dy’ \\ gvs [] \\ gvs [oEL_def]
  \\ first_x_assum $ irule_at $ Pos last
  \\ first_x_assum $ irule_at $ Pos last
  \\ gvs [SF intLib.INT_ARITH_ss]
QED

Theorem x_SUB_IN_from_rows:
  (x-1,y) ∈ from_rows (a,b) rows ⇔ (x,y) ∈ from_rows (a,b) (MAP (λr. F::r) rows)
Proof
  gvs [IN_from_rows,oEL_def,oEL_MAP_EQ_SOME,PULL_EXISTS,CaseEq"bool"]
  \\ rw [] \\ eq_tac \\ rw []
  \\ gvs [SF intLib.INT_ARITH_ss]
  >- (qexists_tac ‘dx+1’ \\ gvs [SF intLib.INT_ARITH_ss])
  \\ first_x_assum $ irule_at $ Pos last
  \\ gvs [SF intLib.INT_ARITH_ss]
  \\ intLib.COOPER_TAC
QED

Theorem LENGTH_if:
  LENGTH (if b then xs else ys) =
  if b then LENGTH xs else LENGTH ys
Proof
  rw []
QED

Theorem count_falses_lemma:
  ∀xs.
    SUM (MAP (b2n o (λe. e = False)) xs) +
    SUM (MAP (b2n o eval env) xs) ≤ LENGTH xs
Proof
  Induct \\ gvs [] \\ rw []
  \\ Cases_on ‘h = False’ \\ gvs []
  \\ rw [oneline b2n_def]
QED

Definition vars_of_def:
  vars_of (And e1 e2) = vars_of e1 ∪ vars_of e2 ∧
  vars_of (Or e1 e2)  = vars_of e1 ∪ vars_of e2 ∧
  vars_of (Not e1)    = vars_of e1 ∧
  vars_of (Var g n)   = {(g,n)} ∧
  vars_of _           = {}
End

Theorem eval_build_Not:
  eval env (build_Not e) = eval env (Not e)
Proof
  Cases_on ‘e’ \\ gvs [build_Not_def]
QED

Theorem eval_build_If:
  eval env (build_If x y z) =
  if eval env x then eval env y else eval env z
Proof
  rw [build_If_def,eval_build_Not]
QED

Theorem eval_bexp_eq_eval:
  EVERY (λ(v,x). env v ⇔ x) l ∧
  vars_of x ⊆ set (MAP FST l) ⇒
  eval_bexp l x = eval env x
Proof
  Induct_on ‘x’ \\ gvs [vars_of_def,eval_bexp_def]
  \\ Induct_on ‘l’ \\ gvs [] \\ PairCases \\ gvs []
  \\ rw [] \\ gvs []
QED

Theorem eval_to_bexp:
  eval env (to_bexp b) = b
Proof
  Cases_on ‘b’ \\ gvs []
QED

Theorem eval_gol_eval:
  ∀vars l env x1 x2 x3 y1 y2 y3 z1 z2 z3.
    vars_of x1 ∪ vars_of x2 ∪ vars_of x3 ∪
    vars_of y1 ∪ vars_of y2 ∪ vars_of y3 ∪
    vars_of z1 ∪ vars_of z2 ∪ vars_of z3 ⊆ set vars ∪ set (MAP FST l) ∧
    EVERY (λ(v,x). env v = x) l ⇒
    eval env (gol_eval vars l y2 (x1,x2,x3,y1,y3,z1,z2,z3)) =
    decide_step (eval env y2)
                (eval env x1,eval env x2,eval env x3,eval env y1,
                 eval env y3,eval env z1,eval env z2,eval env z3)
Proof
  reverse Induct
  >-
   (PairCases
    \\ simp [Once gol_eval_def] \\ rw [] \\ rw [eval_build_If]
    \\ last_x_assum irule
    \\ gvs [SUBSET_DEF, SF DNF_ss, AC DISJ_COMM DISJ_ASSOC])
  \\ simp [Once gol_eval_def]
  \\ gvs [decide_step_def,eval_bexp8_def]
  \\ rpt strip_tac
  \\ drule eval_bexp_eq_eval \\ gvs [eval_to_bexp]
QED

Theorem get_bvars_thm:
  ∀x acc. set (get_bvars x acc) = vars_of x ∪ set acc
Proof
  Induct \\ gvs [get_bvars_def,vars_of_def, AC UNION_COMM UNION_ASSOC]
  \\ induct_on ‘acc’ \\ gvs [add_to_sorted_def] \\ rw []
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []
  \\ rpt (PairCases_on ‘h’ \\ gvs [])
  \\ PairCases_on ‘x’ \\ gvs []
QED

Theorem gol_cell_decide_step:
  px1 = eval env x1 ∧
  px2 = eval env x2 ∧
  px3 = eval env x3 ∧
  py1 = eval env y1 ∧
  py2 = eval env y2 ∧
  py3 = eval env y3 ∧
  pz1 = eval env z1 ∧
  pz2 = eval env z2 ∧
  pz3 = eval env z3
  ⇒
  eval env (gol_cell y2 (x1,x2,x3,y1,y3,z1,z2,z3)) =
  decide_step py2 (px1,px2,px3,py1,py3,pz1,pz2,pz3)
Proof
  rw [] \\ rw [gol_cell_def]
  >-
   (gvs [decide_step_def] \\ gvs [count_falses_def]
    \\ qspec_then ‘[x1;x2;x3;y1;y2;y3;z1;z2;z3]’ assume_tac count_falses_lemma
    \\ gvs [] \\ rw [] \\ CCONTR_TAC \\ gvs [])
  \\ irule eval_gol_eval \\ gvs []
  \\ gvs [get_bvars8_def,get_bvars_thm,SUBSET_DEF]
QED

Theorem gol_step_rows:
  EVERY (λr. HD r = False ∧ LAST r = False) rows ∧
  (rows ≠ [] ⇒ EVERY (λx. x = False) (HD rows)) ∧
  (rows ≠ [] ⇒ EVERY (λx. x = False) (LAST rows)) ∧
  rectangle w h rows ⇒
  from_rows (-85,-85) (MAP (MAP (eval env)) (gol_step_rows rows)) =
  step (from_rows (-85,-85) (MAP (MAP (eval env)) rows))
Proof
  Cases_on ‘rows’ >- gvs [rectangle_def]
  \\ rewrite_tac [gol_step_rows_def,NOT_CONS_NIL]
  \\ rename [‘x::xs’]
  \\ ‘LENGTH x = LENGTH (HD (x::xs))’ by gvs []
  \\ asm_rewrite_tac []
  \\ qspec_tac (‘x::xs’,‘ys’)
  \\ pop_assum kall_tac \\ rw []
  \\ gvs [EXTENSION] \\ PairCases
  \\ rename [‘(x,y) ∈ _’]
  \\ simp [IN_step_lemma]
  \\ rewrite_tac [x_SUB_IN_from_rows]
  \\ rewrite_tac [y_SUB_IN_from_rows]
  \\ simp [IN_from_rows,oEL_MAP_EQ_SOME,PULL_EXISTS]
  \\ gvs [LLOOKUP_gol_rows]
  \\ gvs [LLOOKUP_gol_row,PULL_EXISTS]
  \\ Cases_on ‘x < -85’ >-
   (‘∀dx. x ≠ -85 + &dx’ by intLib.COOPER_TAC \\ gvs []
    \\ ‘∀dx. x + 1 = -85 + &dx <=>
             x + 1 = -85 + &dx ∧ dx = 0’ by intLib.COOPER_TAC
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ gvs [] \\ gvs [oEL_THM] \\ gvs [EVERY_EL, SF CONJ_ss]
    \\ EVAL_TAC \\ rw [oneline b2n_def])
  \\ Cases_on ‘y < -85’ >-
   (‘∀dx. y ≠ -85 + &dx’ by intLib.COOPER_TAC \\ gvs []
    \\ ‘∀dx. y + 1 = -85 + &dx <=>
             y + 1 = -85 + &dx ∧ dx = 0’ by intLib.COOPER_TAC
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ gvs [] \\ gvs [oEL_THM] \\ gvs [EVERY_EL, SF CONJ_ss]
    \\ EVAL_TAC \\ rw [oneline b2n_def])
  \\ ‘∃dx. x = -85 + &dx’ by intLib.COOPER_TAC \\ gvs []
  \\ ‘∃dy. y = -85 + &dy’ by intLib.COOPER_TAC \\ gvs []
  \\ gvs [GSYM integerTheory.INT_ADD_ASSOC,integerTheory.INT_ADD]
  \\ reverse $ Cases_on ‘dy < LENGTH ys’ \\ gvs []
  >-
   (gvs [oEL_THM]
    \\ reverse $ Cases_on ‘dy < SUC (LENGTH ys)’ \\ gvs [] >- EVAL_TAC
    \\ ‘dy = LENGTH ys’ by gvs [] \\ gvs []
    \\ DEP_REWRITE_TAC [EL_CONS]
    \\ gvs [MAP_MAP_o,arithmeticTheory.PRE_SUB1]
    \\ conj_tac >- gvs [rectangle_def]
    \\ gvs [EVERY_EL]
    \\ gvs [SF CONJ_ss, GSYM (SRULE [PRE_SUB1] LAST_EL), EL_MAP]
    \\ ‘dx < LENGTH (EL (LENGTH ys − 1) (MAP (MAP (eval env)) ys)) ∧
        EL dx (EL (LENGTH ys − 1) (MAP (MAP (eval env)) ys)) ⇔ F’ by
      (DEP_ONCE_REWRITE_TAC [EL_MAP]
       \\ gvs [SF CONJ_ss, EL_MAP]
       \\ DEP_REWRITE_TAC [GSYM (SRULE [PRE_SUB1] LAST_EL)]
       \\ gvs [rectangle_def]
       \\ ‘LENGTH ys ≠ 0’ by decide_tac
       \\ gvs []
       \\ CCONTR_TAC \\ gvs []
       \\ gvs [SF CONJ_ss, EL_MAP])
    \\ asm_rewrite_tac []
    \\ EVAL_TAC \\ rw [oneline b2n_def])
  \\ gvs [LENGTH_if]
  \\ ‘∀n. n < LENGTH ys ⇒ LENGTH (EL n ys) = LENGTH (HD ys)’ by
     (gvs [rectangle_def,EVERY_EL]
      \\ Cases_on ‘ys’ \\ gvs []
      \\ first_x_assum $ qspec_then ‘0’ mp_tac \\ gvs [])
  \\ gvs [SF CONJ_ss]
  \\ reverse $ Cases_on ‘dx < LENGTH (HD ys)’ \\ gvs []
  >-
   (gvs [oEL_THM, SF CONJ_ss]
    \\ Cases_on ‘dy’ \\ gvs []
    >- (EVAL_TAC \\ rw [oneline b2n_def])
    \\ gvs [EL_MAP]
    \\ reverse $ Cases_on ‘dx < SUC (LENGTH (HD ys))’ \\ gvs []
    >- EVAL_TAC
    \\ DEP_REWRITE_TAC [EL_CONS] \\ gvs []
    \\ conj_asm1_tac >- (Cases_on ‘ys’ \\ gvs [rectangle_def])
    \\ gvs [EL_MAP]
    \\ ‘eval env (EL (PRE dx) (EL n ys)) = F’ by
     (‘dx = LENGTH (HD ys)’ by gvs []
      \\ gvs [PRE_SUB1]
      \\ ‘LENGTH (HD ys) = LENGTH (EL n ys)’ by simp []
      \\ asm_rewrite_tac []
      \\ DEP_REWRITE_TAC [GSYM (SRULE [PRE_SUB1] LAST_EL)]
      \\ pop_assum kall_tac
      \\ gvs [EVERY_EL]
      \\ rewrite_tac [GSYM LENGTH_NIL]
      \\ ‘n < LENGTH ys’ by gvs []
      \\ res_tac
      \\ decide_tac)
    \\ EVAL_TAC \\ rw [oneline b2n_def])
  \\ irule gol_cell_decide_step
  \\ rpt strip_tac
  >- (Cases_on ‘dy’ \\ gvs [oEL_def,EL_REPLICATE]
      \\ gvs [oEL_MAP_EQ_SOME,PULL_EXISTS]
      \\ Cases_on ‘dx’ \\ gvs [oEL_def]
      \\ gvs [oEL_MAP_EQ_SOME,PULL_EXISTS]
      \\ gvs [oEL_THM])
  >- (Cases_on ‘dy’ \\ gvs [oEL_def,EL_REPLICATE]
      \\ gvs [oEL_MAP_EQ_SOME,PULL_EXISTS] \\ gvs [oEL_THM])
  >- (Cases_on ‘dy’ \\ gvs [oEL_def,EL_REPLICATE]
      \\ gvs [oEL_MAP_EQ_SOME,PULL_EXISTS]
      \\ gvs [oEL_THM] \\ rw [])
  >- (Cases_on ‘dx’ \\ gvs [oEL_def,oEL_MAP_EQ_SOME,PULL_EXISTS]
      \\ gvs [oEL_THM])
  >- (Cases_on ‘dx’ \\ gvs [oEL_def,oEL_MAP_EQ_SOME,PULL_EXISTS]
      \\ gvs [oEL_THM])
  >- (rw [] \\ gvs [oEL_THM])
  >- (Cases_on ‘dx’ \\ gvs [oEL_def,oEL_MAP_EQ_SOME,PULL_EXISTS]
      \\ rw [] \\ gvs [oEL_THM,EL_MAP,EL_REPLICATE])
  \\ rw [] \\ gvs [oEL_THM,EL_MAP,EL_REPLICATE]
QED

Theorem check_mask_thm:
  check_mask rows m ⇒
  from_rows (-85,-85) (MAP (MAP (eval env)) rows) ⊆
  from_rows (-85,-85) m
Proof
  gvs [check_mask_def,LIST_REL_EL_EQN,SUBSET_DEF,FORALL_PROD]
  \\ rw [IN_from_rows] \\ gvs [oEL_THM,EL_MAP]
  \\ first_x_assum drule \\ strip_tac
  \\ pop_assum $ qspec_then ‘dx’ mp_tac \\ gvs []
  \\ strip_tac \\ gvs []
QED

Theorem check_mask_F:
  check_mask rows m ⇒
  ∀x y row.
    oEL y m = SOME row ∧ oEL x row = SOME F ⇒
    ∃r. oEL y rows = SOME r ∧ oEL x r = SOME False
Proof
  gvs [check_mask_def,LIST_REL_EL_EQN,oEL_THM] \\ metis_tac []
QED

Theorem HD_EL:
  HD xs = EL 0 xs
Proof
  Cases_on ‘xs’ \\ gvs []
QED

Theorem from_row_append:
  ∀xs ys x y.
    from_row (x,y) (xs ++ ys) =
    from_row (x,y) xs ∪ from_row (x + & LENGTH xs,y) ys
Proof
  Induct \\ gvs [from_row_def]
  \\ Cases \\ gvs [from_row_def,ADD1]
  \\ rpt gen_tac
  \\ gvs [UNION_ASSOC]
  \\ rpt AP_TERM_TAC
  \\ rpt AP_THM_TAC
  \\ rpt AP_TERM_TAC
  \\ gvs [] \\ intLib.COOPER_TAC
QED

Theorem from_rows_append:
  ∀xs ys x y.
    from_rows (x,y) (xs ++ ys) =
    from_rows (x,y) xs ∪ from_rows (x,y + & LENGTH xs) ys
Proof
  Induct \\ gvs [from_rows_def]
  \\ rpt gen_tac
  \\ gvs [UNION_ASSOC]
  \\ rpt AP_TERM_TAC
  \\ rpt AP_THM_TAC
  \\ rpt AP_TERM_TAC
  \\ gvs [] \\ intLib.COOPER_TAC
QED

Triviality from_row_rep_F:
  ∀x y. from_row (x,y) (REPLICATE l F) = {}
Proof
  Induct_on ‘l’ \\ gvs [from_row_def]
QED

Triviality from_rows_rep_rep_F:
  from_rows (x,y) (REPLICATE k (REPLICATE l F)) = {}
Proof
  irule from_rows_EMPTY \\ gvs []
QED

Theorem from_rows_add_margin:
  from_rows (x,y) (add_margin F k m) =
  from_rows (x + &k,y + &k) m
Proof
  gvs [add_margin_def,from_rows_append]
  \\ gvs [from_rows_rep_rep_F]
  \\ qid_spec_tac ‘y’
  \\ qid_spec_tac ‘x’
  \\ Induct_on ‘m’ \\ gvs [from_rows_def]
  \\ gvs [from_row_append,from_row_rep_F]
  \\ rpt gen_tac \\ AP_TERM_TAC
  \\ first_x_assum $ qspecl_then [‘x’,‘y+1’] mp_tac
  \\ gvs [AC integerTheory.INT_ADD_COMM integerTheory.INT_ADD_ASSOC]
QED

Theorem IN_COMPL_infl_COMPL:
  (x,y) ∈ COMPL (infl (COMPL s)) ⇔
  { (x-1,y-1); (x,y-1); (x+1,y-1);
    (x-1,y  ); (x,y  ); (x+1,y  );
    (x-1,y+1); (x,y+1); (x+1,y+1) } ⊆ s
Proof
  gvs [] \\ simp [IN_DEF,infl_def]
  \\ gvs [live_adj_def,IN_DEF]
  \\ eq_tac \\ rw []
QED

Triviality from_row_cons_imp:
  (p,q) ∈ from_row (x,y) (t::ts) ⇒
  (p,q) = (x,y) ∧ t ∨ (p,q) ∈ from_row (x+1,y) ts
Proof
  Cases_on ‘t’ \\ gvs [from_row_def]
QED

Theorem from_row_cons_eq:
  (a,b) ∈ from_row (x,y) (r::rs) ⇔
  (r ∧ a = x ∧ b = y) ∨ (a,b) ∈ from_row (x+1,y) rs
Proof
  Cases_on ‘r’ \\ gvs [from_row_def]
QED

Theorem from_row_shrink_row:
  ∀r1 r2 r3 a b x y.
    (a,b) ∈ from_row (x,y) (shrink_row r1 r2 r3) ⇒
    (a-1,b-1) ∈ from_row (x-1,y-1) r1 ∧
    (a,b-1)   ∈ from_row (x-1,y-1) r1 ∧
    (a+1,b-1) ∈ from_row (x-1,y-1) r1 ∧
    (a-1,b)   ∈ from_row (x-1,y) r2 ∧
    (a,b)     ∈ from_row (x-1,y) r2 ∧
    (a+1,b)   ∈ from_row (x-1,y) r2 ∧
    (a-1,b+1) ∈ from_row (x-1,y+1) r3 ∧
    (a,b+1)   ∈ from_row (x-1,y+1) r3 ∧
    (a+1,b+1) ∈ from_row (x-1,y+1) r3
Proof
  ho_match_mp_tac shrink_row_ind
  \\ gvs [shrink_row_def,from_row_def]
  \\ rpt gen_tac \\ disch_tac
  \\ rpt gen_tac \\ disch_tac
  \\ dxrule from_row_cons_imp
  \\ strip_tac \\ gvs []
  >- gvs [from_row_def]
  \\ once_rewrite_tac [from_row_cons_eq]
  \\ metis_tac [intLib.COOPER_PROVE “m + n - n:int = m”,
                intLib.COOPER_PROVE “m - n + n:int = m”]
QED

Theorem from_rows_shrink:
  from_rows (x,y) (shrink m) ⊆
  COMPL (infl (COMPL (from_rows (x,y) m)))
Proof
  gvs [shrink_def,from_rows_add_margin]
  \\ qsuff_tac
     ‘∀m x y.
        from_rows (x,y) (shrink_all m) ⊆
        COMPL (infl (COMPL (from_rows (x-1,y-1) m)))’
  >- metis_tac [intLib.COOPER_PROVE “x+1-1:int = x”]
  \\ rewrite_tac [SUBSET_DEF]
  \\ once_rewrite_tac [GSYM PAIR]
  \\ rewrite_tac [IN_COMPL_infl_COMPL]
  \\ gvs [FORALL_PROD]
  \\ ho_match_mp_tac shrink_all_ind
  \\ gvs [shrink_all_def,from_rows_def]
  \\ rpt gen_tac \\ disch_tac
  \\ rpt gen_tac \\ reverse strip_tac
  >- metis_tac [intLib.COOPER_PROVE “m + n - n:int = m”,
                intLib.COOPER_PROVE “m - n + n:int = m”]
  \\ dxrule from_row_shrink_row \\ gvs []
QED

Theorem length_shrink_row:
  ∀xs ys zs.
    LENGTH xs = LENGTH ys ∧
    LENGTH zs = LENGTH ys ⇒
    LENGTH (shrink_row xs ys zs) = LENGTH ys - 2
Proof
  ho_match_mp_tac shrink_row_ind \\ gvs [shrink_row_def]
QED

Theorem length_shrink_all:
  ∀m. LENGTH (shrink_all m) = LENGTH m - 2
Proof
  ho_match_mp_tac shrink_all_ind \\ gvs [shrink_all_def]
QED

Theorem shrink_rectangle:
  rectangle w h m ⇒ rectangle w h (shrink m)
Proof
  rw [rectangle_def,EVERY_MEM,shrink_def,add_margin_def]
  \\ gvs [length_shrink_all,MEM_MAP]
  >-
   (CASE_TAC \\ gvs []
    \\ Cases_on ‘m’ \\ gvs []
    \\ rename [‘shrink_all (x::xs)’] \\ Cases_on ‘xs’ \\ gvs []
    \\ rename [‘shrink_all (x::y::xs)’] \\ Cases_on ‘xs’ \\ gvs []
    \\ gvs [shrink_all_def] \\ gvs [SF DNF_ss]
    \\ DEP_REWRITE_TAC [length_shrink_row] \\ gvs [])
  >-
   (last_x_assum kall_tac
    \\ gvs [GSYM EVERY_MEM]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘m’
    \\ ho_match_mp_tac shrink_all_ind \\ gvs [shrink_all_def]
    \\ rw [] \\ gvs [SF SFY_ss]
    \\ DEP_REWRITE_TAC [length_shrink_row] \\ gvs [])
  >-
   (CASE_TAC \\ gvs []
    \\ Cases_on ‘m’ \\ gvs []
    \\ rename [‘shrink_all (x::xs)’] \\ Cases_on ‘xs’ \\ gvs []
    \\ rename [‘shrink_all (x::y::xs)’] \\ Cases_on ‘xs’ \\ gvs []
    \\ gvs [shrink_all_def] \\ gvs [SF DNF_ss]
    \\ DEP_REWRITE_TAC [length_shrink_row] \\ gvs [])
QED

Theorem gol_checked_steps_gen:
  ∀rows rows1 area.
    gol_checked_steps 30 rows (shrink m) = SOME rows1 ∧
    rectangle w h rows ∧
    rectangle w h m ∧
    area = from_rows (-85,-85) m ⇒
    steps (from_rows (-85,-85) (MAP (MAP (eval env)) rows))
          area
          (from_rows (-85,-85) (MAP (MAP (eval env)) rows1))
Proof
  simp [steps_def]
  \\ qspec_tac (‘30:num’,‘k’)
  \\ Induct
  \\ gvs [gol_checked_steps_def]
  \\ rpt gen_tac \\ strip_tac
  \\ last_x_assum drule
  \\ impl_tac >- gvs [gol_step_rows_rectangle]
  \\ strip_tac \\ gvs []
  \\ qabbrev_tac ‘m1 = shrink m’
  \\ ‘rectangle w h m1’ by
    (simp [Abbr‘m1’] \\ irule shrink_rectangle \\ gvs [])
  \\ ‘m1 ≠ [] ∧ EVERY (λx. x ≠ []) m1’ by
   (gvs [rectangle_def,EVERY_MEM] \\ CCONTR_TAC \\ gvs []
    \\  res_tac \\ gvs [])
  \\ ‘EVERY (λx. x = F) (HD m1) ∧
      EVERY (λx. x = F) (LAST m1) ∧
      EVERY (λr. HD r = F ∧ LAST r = F) m1’ by
   (gvs [shrink_def,Abbr‘m1’]
    \\ gvs [add_margin_def]
    \\ Cases_on ‘shrink_all m’
    >- gvs [rectangle_def]
    \\ gvs [EVAL “REPLICATE 1 x”]
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ gvs [GSYM SNOC_APPEND]
    \\ rewrite_tac [GSYM SNOC,LAST_SNOC]
    \\ rewrite_tac [DECIDE “m + 2 = 1 + m + 1:num”]
    \\ rewrite_tac [GSYM rich_listTheory.REPLICATE_APPEND]
    \\ rewrite_tac [EVAL “REPLICATE 1 x”] \\ gvs []
    \\ gvs [GSYM SNOC_APPEND]
    \\ rewrite_tac [GSYM SNOC,LAST_SNOC]
    \\ qspec_tac (‘LENGTH h'’,‘k’)
    \\ Induct \\ gvs [])
  \\ ‘EVERY (λx. x = False) (HD rows) ∧
      EVERY (λx. x = False) (LAST rows) ∧
      EVERY (λr. HD r = False ∧ LAST r = False) rows’ by
   (rpt conj_tac
    >- (Cases_on ‘rows’ >- gvs [rectangle_def]
        \\ gvs [check_mask_def,EVERY_EL,LIST_REL_EL_EQN])
    >- (Cases_on ‘rows’ using SNOC_CASES >- gvs [rectangle_def]
        \\ gvs [LAST_SNOC,check_mask_def,listTheory.LIST_REL_SNOC]
        \\ gvs [check_mask_def,EVERY_EL,LIST_REL_EL_EQN])
    \\ gvs [EVERY_EL,LIST_REL_EL_EQN,check_mask_def]
    \\ gen_tac \\ strip_tac
    \\ last_x_assum drule \\ strip_tac
    \\ last_x_assum drule \\ strip_tac
    \\ ‘EL n rows ≠ []’ by
      (gvs [rectangle_def,EVERY_EL]
       \\ rewrite_tac [GSYM LENGTH_NIL]
       \\ res_tac \\ decide_tac)
    \\ first_assum $ qspec_then ‘0’ mp_tac
    \\ impl_tac
    >-
     (pop_assum mp_tac
      \\ rewrite_tac [GSYM LENGTH_NIL]
      \\ decide_tac)
    \\ gvs [] \\ rw []
    \\ first_x_assum $ qspec_then ‘PRE (LENGTH (EL n m1))’ mp_tac
    \\ ‘EL n m1 ≠ []’ by metis_tac [LENGTH_NIL]
    \\ gvs [LAST_EL]
    \\ impl_keep_tac
    >- (irule (DECIDE “m ≠ 0 ⇒ PRE m < m”) \\ gvs [])
    \\ strip_tac \\ gvs []
    \\ qsuff_tac ‘F’ \\ gvs []
    \\ pop_assum mp_tac \\ gvs []
    \\ first_x_assum drule
    \\ gvs [LAST_EL])
  \\ gvs [FUNPOW,gol_step_rows, SF SFY_ss] \\ rw []
  \\ Cases_on ‘n’ \\ gvs [GSYM FUNPOW]
  \\ irule IMP_infl_subset
  \\ irule SUBSET_TRANS
  \\ irule_at Any check_mask_thm
  \\ last_x_assum $ irule_at Any
  \\ gvs [from_rows_shrink,Abbr‘m1’]
QED

Theorem or_at_length:
  ∀x y xs ys. LIST_REL (λa b. LENGTH a = LENGTH b) (or_at x y xs ys) ys
Proof
  ho_match_mp_tac or_at_ind
  \\ gvs [or_at_def] \\ rw []
  \\ gvs [LIST_REL_EL_EQN]
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘p’
  \\ Induct_on ‘row’ \\ gvs [or_row_def,FORALL_PROD]
  \\ Cases_on ‘p’ \\ gvs [or_row_def] \\ rw [] \\ gvs []
QED

Theorem or_lwss_rectangle:
  ∀ins xs ys.
    or_lwss xs ins = SOME ys ∧
    rectangle w h xs ⇒
    rectangle w h ys
Proof
  Induct \\ gvs [or_lwss_def,FORALL_PROD,CaseEq"option"]
  \\ rw [] \\ last_x_assum drule \\ rw []
  \\ gvs [rectangle_def,EVERY_MEM]
  \\ rename [‘or_at x y ts us’]
  \\ qspecl_then [‘x’,‘y’,‘ts’,‘us’] mp_tac or_at_length
  \\ gvs [MEM_EL,PULL_EXISTS,LIST_REL_EL_EQN]
QED

Theorem from_row_or_row:
  ∀m p row x y.
    m + LENGTH p < LENGTH row ⇒
    from_row (x,y) (MAP (eval env) (or_row m p row)) =
    from_row (x,y) (MAP (eval env) row) ∪
    from_row (x + &m,y) (MAP (eval env) p)
Proof
  ho_match_mp_tac or_row_ind \\ gvs [] \\ rw []
  \\ gvs [or_row_def,from_row_def] \\ rw []
  \\ gvs [from_row_def]
  \\ Cases_on ‘eval env r’ \\ gvs [from_row_def]
  >-
   (Cases_on ‘eval env p’ \\ gvs [from_row_def]
    \\ gvs [EXTENSION]
    \\ rw [] \\ eq_tac \\ rw [] \\ gvs [])
  >-
   (Cases_on ‘eval env p’ \\ gvs [from_row_def]
    \\ gvs [AC UNION_COMM UNION_ASSOC])
  \\ Cases_on ‘m’ \\ gvs [ADD1]
  \\ gvs [ADD1,intLib.COOPER_PROVE “& (m + n) = & n + & m:int”]
  \\ gvs [AC UNION_COMM UNION_ASSOC,
          AC integerTheory.INT_ADD_COMM integerTheory.INT_ADD_ASSOC]
QED

Theorem from_rows_or_at:
  ∀m n ds rows1 x y.
    n + LENGTH ds < LENGTH rows1 ∧
    EVERY (λrow. EVERY (λd. m + LENGTH d < LENGTH row) ds) rows1 ⇒
    from_rows (x,y) (MAP (MAP (eval env)) (or_at m n ds rows1)) =
    from_rows (x,y) (MAP (MAP (eval env)) rows1) ∪
    from_rows (x + &m,y + &n) (MAP (MAP (eval env)) ds)
Proof
  ho_match_mp_tac or_at_ind \\ rw []
  >- gvs [from_rows_def,or_at_def]
  \\ gvs [or_at_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [from_rows_def]
  >-
   (last_x_assum (fn th => DEP_REWRITE_TAC [th])
    \\ conj_tac >- gvs [EVERY_MEM]
    \\ gvs [from_row_or_row, AC UNION_COMM UNION_ASSOC])
  \\ Cases_on ‘n’
  \\ gvs [ADD1,intLib.COOPER_PROVE “& (m + n) = & n + & m:int”]
  \\ gvs [from_row_or_row, AC UNION_COMM UNION_ASSOC,
          AC integerTheory.INT_ADD_COMM integerTheory.INT_ADD_ASSOC]
QED

Theorem age_0[simp]:
  age 0 = I
Proof
  gvs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem from_rows_io_gate:
  -1 ≤ x ∧ -1 ≤ y ⇒
  from_rows (-85 + &Num (x * 75 − 5 + 85),-85 + &Num (y * 75 − 5 + 85))
    (MAP (MAP (λb. eval env (if b then r else False))) (io_gate d)) =
  lwss_at 0 ((x,y),d,(λn. eval (age n env) r))
Proof
  gvs [lwss_at_def] \\ reverse $ rw []
  >-
   (irule from_rows_EMPTY
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ CCONTR_TAC \\ gvs []
    \\ Cases_on ‘b’ \\ gvs [])
  \\ gvs [lwss_as_set_def]
  \\ irule (METIS_PROVE [] “x1 = x2 ∧ y1 = y2 ⇒ f x1 y1 = f x2 y2”)
  \\ conj_tac
  >- (gvs [] \\ intLib.COOPER_TAC)
  \\ gvs [MAP_EQ_ID] \\ rw [] \\ rw []
QED

Theorem or_lwss_imp:
  or_lwss xs ins = SOME ys ∧ rectangle w h xs ∧
  simple_checks w h ins1 outs1 (rows:bexp list list) ∧
  set ins ⊆ set (ins1 ++ outs1) ⇒
  from_rows (-85,-85) (MAP (MAP (eval env)) ys) =
  from_rows (-85,-85) (MAP (MAP (eval env)) xs) ∪
  U (IMAGE (lwss_at 0) (set (eval_io env ins)))
Proof
  strip_tac
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ Induct_on ‘ins’
  \\ gvs [or_lwss_def]
  >- (rw [] \\ gvs [EXTENSION,eval_io_def])
  \\ PairCases
  \\ rename [‘((x,y),d,r)::_’]
  \\ simp [GSYM AND_IMP_INTRO,or_lwss_def,CaseEq"option"]
  \\ Cases_on ‘set ins ⊆ set ins1 ∪ set outs1’ \\ gvs []
  \\ disch_then assume_tac
  \\ ‘-1 ≤ x ∧ -1 ≤ y ∧ x ≤ 2 * &w - 1 ∧ y ≤ 2 * &h - 1’ by
       (gvs [EVERY_MEM,simple_checks_def] \\ res_tac \\ fs [])
  \\ qpat_x_assum ‘_ ∨ _’ kall_tac
  \\ rw [] \\ gvs []
  \\ DEP_REWRITE_TAC [from_rows_or_at]
  \\ drule_all or_lwss_rectangle \\ strip_tac
  \\ conj_tac
  >-
   (gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,io_gate_lenth,rectangle_def]
    \\ rw [] \\ res_tac
    \\ gvs [io_gate_lenth, SF SFY_ss] \\ intLib.COOPER_TAC)
  \\ gvs [GSYM UNION_ASSOC]
  \\ AP_TERM_TAC
  \\ gvs [MAP_MAP_o,o_DEF,SF ETA_ss]
  \\ gvs [eval_io_def]
  \\ gvs [from_rows_io_gate, AC UNION_COMM UNION_ASSOC]
QED

Theorem set_INTER:
  set xs ∩ p = set (FILTER p xs)
Proof
  simp [EXTENSION,MEM_FILTER]
  \\ simp [IN_DEF,AC CONJ_COMM CONJ_ASSOC]
QED

Theorem FILTER_eval_io:
  FILTER is_ns (eval_io env outs) = eval_io env (FILTER is_ns outs) ∧
  FILTER is_ew (eval_io env outs) = eval_io env (FILTER is_ew outs)
Proof
  Induct_on ‘outs’ \\ gvs [eval_io_def,FORALL_PROD,is_ns_def,is_ew_def] \\ rw []
QED

Theorem lwss_29_59:
  lwss_at 29 = lwss_at 0 ∧ lwss_at 59 = lwss_at 0
Proof
  gvs [FUN_EQ_THM,FORALL_PROD,lwss_at_def]
QED

Theorem MAP_MAP_inc_vars:
  MAP (MAP (eval env)) (inc_vars rows) =
  MAP (MAP (eval (age 1 env))) rows
Proof
  gvs [inc_vars_def,MAP_MAP_o,MAP_EQ_f] \\ rw []
  \\ qsuff_tac ‘∀e env. eval env (inc e) ⇔ eval (age 1 env) e’ \\ gvs []
  \\ Induct \\ gvs [inc_def]
QED

Theorem box_SUC:
  box (x,y) (w,SUC n) =
  box (x,y) (w,1) ∪ box (x,y+1) (w,n)
Proof
  gvs [box_def,EXTENSION] \\ rw[] \\ eq_tac \\ rw []
  >- (Cases_on ‘j’ \\ gvs [] \\ qexists_tac ‘n'’ \\ gvs []
      \\ intLib.COOPER_TAC)
  >- (qexists_tac ‘0’ \\ gvs [])
  \\ qexists_tac ‘SUC j’ \\ gvs [] \\ intLib.COOPER_TAC
QED

Theorem from_row_or_box_row:
  ∀h m w x y.
    m + w ≤ LENGTH h ⇒
    from_row (x,y) (or_box_row m w h) =
    from_row (x,y) h ∪ box (x + &m,y) (w,1)
Proof
  Induct
  \\ gvs [or_box_row_def,from_row_def,box_def]
  \\ rpt strip_tac
  \\ reverse $ Cases_on ‘m’ \\ gvs []
  >-
   (Cases_on ‘h'’ \\ rw [from_row_def]
    \\ gvs [AC UNION_COMM UNION_ASSOC, ADD1,
            intLib.COOPER_PROVE “&(m + n:num) :int = & m + & n”]
    \\ gvs [AC integerTheory.INT_ADD_COMM integerTheory.INT_ADD_ASSOC])
  \\ Cases_on ‘w’ \\ gvs [from_row_def]
  \\ ‘{(x + &i,y + &j) | i < SUC n ∧ j = 0} =
      {(x,y)} ∪ {(x + 1 + &i,y + &j) | i < n ∧ j = 0}’ by
   (gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []
    >- (Cases_on ‘i’ \\ gvs [] \\ pop_assum $ irule_at Any
        \\ intLib.COOPER_TAC)
    >- (qexists_tac ‘0’ \\ gvs [])
    >- (qexists_tac ‘SUC i’ \\ gvs [] \\ intLib.COOPER_TAC))
  \\ gvs []
  \\ Cases_on ‘h'’ \\ rw [from_row_def]
  \\ gvs [AC UNION_COMM UNION_ASSOC]
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
QED

Theorem from_rows_or_box:
  ∀rest x y m n w h.
    EVERY (λrow. m + w ≤ LENGTH row) rest ∧
    n + h ≤ LENGTH rest ⇒
    from_rows (x,y) (or_box m n w h rest) =
    box (x + & m, y + & n) (w, h) ∪ from_rows (x,y) rest
Proof
  Induct
  >- gvs [box_def,or_box_def,from_rows_def]
  \\ rw [or_box_def,from_rows_def]
  >- gvs [box_def]
  >-
   (DEP_REWRITE_TAC [from_row_or_box_row]
    \\ gvs [] \\ Cases_on ‘h'’
    \\ gvs [box_SUC, AC UNION_COMM UNION_ASSOC])
  \\ ‘y + 1 + &(n − 1) = y + &n’ by intLib.COOPER_TAC
  \\ gvs [AC UNION_COMM UNION_ASSOC]
QED

Theorem or_io_areas_eq:
  ∀outs ins1 outs1.
    simple_checks w h ins1 outs1 (rows : bexp list list) ∧
    set outs ⊆ set ins1 ∪ set outs1 ⇒
    from_rows (-85,-85)
              (or_io_areas outs
                 (REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F))) =
    circ_io_area (set (eval_io env outs))
Proof
  gvs [circ_io_area_def,eval_io_def,MEM_MAP,EXISTS_PROD]
  \\ rw []
  \\ Induct_on ‘outs’
  \\ gvs [or_io_areas_def]
  >- (irule from_rows_EMPTY \\ gvs [])
  \\ gen_tac
  \\ disch_then assume_tac
  \\ PairCases_on ‘h'’
  \\ rename [‘(((x,y),d,r)::outs)’]
  \\ ‘-1 ≤ x ∧ -1 ≤ y ∧ x ≤ 2 * &w - 1 ∧ y ≤ 2 * &h - 1 ∧
      set outs ⊆ set ins1 ∪ set outs1’ by
       (gvs [EVERY_MEM,simple_checks_def] \\ res_tac \\ fs [])
  \\ qpat_x_assum ‘(_ ∨ _) ∧ _’ kall_tac
  \\ irule EQ_TRANS
  \\ qexists_tac ‘
       io_box (x,y) ∪
       U {io_box (x,y) | (∃p_1 p_2''. MEM ((x,y),p_1,p_2'') outs)}’
  \\ reverse conj_tac
  >- (gvs [EXTENSION,PULL_EXISTS] \\ metis_tac [])
  \\ gvs [or_io_areas_def]
  \\ DEP_REWRITE_TAC [from_rows_or_box]
  \\ conj_tac
  >-
   (qabbrev_tac ‘rows1 = (or_io_areas outs
             (REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F)))’
    \\ ‘rectangle w h rows1’ by
     (gvs [Abbr‘rows1’]
      \\ irule (or_io_areas_rectangle |> GEN_ALL |> SRULE [])
      \\ gvs [rectangle_def])
    \\ gvs [rectangle_def,EVERY_MEM]
    \\ rw [] \\ intLib.COOPER_TAC)
  \\ asm_rewrite_tac [io_box_def]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs []
  \\ intLib.COOPER_TAC
QED

Theorem inter_rows_rectangle:
  inter_rows rows1 bools = rows2 ∧
  rectangle w h rows1 ∧
  rectangle w h bools ⇒
  rectangle w h rows2
Proof
  rw [] \\ gvs [inter_rows_def,rectangle_def]
  \\ gvs [EVERY_MEM,MAP2_MAP,MEM_MAP,PULL_EXISTS,MEM_ZIP]
  \\ gvs [MEM_EL,PULL_EXISTS]
QED

Theorem oEL_MAP_SOME:
  ∀xs f n y.
    oEL n (MAP f xs) = SOME y ⇔
    ∃x. oEL n xs = SOME x ∧ y = f x
Proof
  gvs [oEL_THM,EL_MAP,SF CONJ_ss] \\ metis_tac []
QED

Theorem oEL_MAP2_SOME:
  ∀xs ys f n z.
    oEL n (MAP2 f xs ys) = SOME z ⇔
    ∃x y. oEL n xs = SOME x ∧ oEL n ys = SOME y ∧ z = f x y
Proof
  Induct \\ gvs [oEL_def] \\ Cases_on ‘ys’ \\ gvs [oEL_def]
  \\ rw [] \\ eq_tac \\ gvs []
QED

Theorem inter_rows_lemma:
  rectangle w h rows1 ∧ rectangle w h bools ⇒
  from_rows (x,y) (MAP (MAP (eval env)) (inter_rows rows1 bools)) =
  from_rows (x,y) (MAP (MAP (eval env)) rows1) ∩
  from_rows (x,y) bools
Proof
  strip_tac
  \\ gvs [EXTENSION,FORALL_PROD,IN_from_rows,rectangle_def]
  \\ rw [inter_rows_def,oEL_MAP_SOME,PULL_EXISTS,oEL_MAP2_SOME]
  \\ eq_tac \\ strip_tac \\ gvs []
  \\ Cases_on ‘b’ \\ gvs []
QED

Theorem inter_rows_thm:
  bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F) ∧
  rectangle w h rows1 ∧
  simple_checks w h ins1 outs1 (rows : bexp list list) ∧
  set outs ⊆ set (ins1 ++ outs1) ⇒
  from_rows (-85,-85) (MAP (MAP (eval env))
                           (inter_rows rows1 (or_io_areas outs bools))) =
  from_rows (-85,-85) (MAP (MAP (eval env)) rows1) ∩
  circ_io_area (set (eval_io env outs))
Proof
  strip_tac
  \\ DEP_REWRITE_TAC [inter_rows_lemma] \\ gvs []
  \\ irule_at Any (or_io_areas_rectangle |> GEN_ALL |> SRULE [])
  \\ conj_tac >- gvs [rectangle_def]
  \\ AP_TERM_TAC
  \\ irule or_io_areas_eq
  \\ rpt $ first_x_assum $ irule_at Any
QED

Theorem diff_rows_rectangle:
  diff_rows rows1 bools = rows2 ∧
  rectangle w h rows1 ∧
  rectangle w h bools ⇒
  rectangle w h rows2
Proof
  rw [] \\ gvs [diff_rows_def,rectangle_def]
  \\ gvs [EVERY_MEM,MAP2_MAP,MEM_MAP,PULL_EXISTS,MEM_ZIP]
  \\ gvs [MEM_EL,PULL_EXISTS]
QED

Theorem diff_rows_lemma:
  rectangle w h rows1 ∧ rectangle w h bools ⇒
  from_rows (x,y) (MAP (MAP (eval env)) (diff_rows rows1 bools)) =
  from_rows (x,y) (MAP (MAP (eval env)) rows1) DIFF
  from_rows (x,y) bools
Proof
  strip_tac
  \\ gvs [EXTENSION,FORALL_PROD,IN_from_rows,rectangle_def]
  \\ rw [diff_rows_def,oEL_MAP_SOME,PULL_EXISTS,oEL_MAP2_SOME]
  \\ eq_tac \\ strip_tac \\ gvs []
  >- (Cases_on ‘b’ \\ gvs [])
  \\ Cases_on ‘LLOOKUP bools dy’ \\ gvs []
  \\ gvs [oEL_THM,EVERY_MEM,MEM_EL,PULL_EXISTS]
QED

Theorem diff_rows_thm:
  bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F) ∧
  rectangle w h rows1 ∧
  simple_checks w h ins1 outs1 (rows : bexp list list) ∧
  set outs ⊆ set (ins1 ++ outs1) ⇒
  from_rows (-85,-85) (MAP (MAP (eval env))
                           (diff_rows rows1 (or_io_areas outs bools))) =
  from_rows (-85,-85) (MAP (MAP (eval env)) rows1) DIFF
  circ_io_area (set (eval_io env outs))
Proof
  strip_tac
  \\ DEP_REWRITE_TAC [diff_rows_lemma] \\ gvs []
  \\ irule_at Any (or_io_areas_rectangle |> GEN_ALL |> SRULE [])
  \\ conj_tac >- gvs [rectangle_def]
  \\ AP_TERM_TAC
  \\ irule or_io_areas_eq
  \\ rpt $ first_x_assum $ irule_at Any
QED

Theorem diff_rectangle:
  rectangle w h xs ∧ rectangle w h ys ⇒ rectangle w h (diff xs ys)
Proof
  gvs [rectangle_def,diff_def,MAP2_MAP,EVERY_MAP]
  \\ gvs [EVERY_MEM,MEM_ZIP,PULL_EXISTS]
  \\ gvs [MEM_EL,PULL_EXISTS]
QED

Theorem or_rectangle:
  rectangle w h xs ∧ rectangle w h ys ⇒ rectangle w h (or xs ys)
Proof
  gvs [rectangle_def,or_def,MAP2_MAP,EVERY_MAP]
  \\ gvs [EVERY_MEM,MEM_ZIP,PULL_EXISTS]
  \\ gvs [MEM_EL,PULL_EXISTS]
QED

Theorem from_rows_or:
  ∀xs ys x y.
    LIST_REL (λx y. LENGTH x = LENGTH y) xs ys ⇒
    from_rows (x,y) (or xs ys) =
    from_rows (x,y) xs ∪ from_rows (x,y) ys
Proof
  gvs [EXTENSION,FORALL_PROD,IN_from_rows,or_def,oEL_THM,EL_MAP2,LIST_REL_EL_EQN]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs [EL_MAP2]
QED

Theorem from_rows_diff:
  ∀xs ys x y.
    LIST_REL (λx y. LENGTH x = LENGTH y) xs ys ⇒
    from_rows (x,y) (diff xs ys) =
    from_rows (x,y) xs DIFF from_rows (x,y) ys
Proof
  gvs [EXTENSION,FORALL_PROD,IN_from_rows,diff_def,oEL_THM,EL_MAP2,LIST_REL_EL_EQN]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs [EL_MAP2]
QED

Theorem make_base_area_thm:
  base_area (set (make_area w h)) =
  from_rows (-85,-85) (make_base_area w h)
Proof
  gvs [make_base_area_def,from_rows_add_margin]
  \\ gvs [EXTENSION] \\ PairCases
  \\ gvs [IN_from_rows,oEL_THM,base_area_def,make_area_def]
  \\ gvs [MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
  \\ gvs [EL_REPLICATE, SF CONJ_ss,box_def,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  >- (* why is the following slow? *)
   (qexists_tac ‘i + 150 * x'’
    \\ qexists_tac ‘j + 150 * y'’
    \\ intLib.COOPER_TAC)
  \\ rewrite_tac [intLib.COOPER_PROVE
        “-75 + & n = & (150 * m) - 75 + & i :int ⇔ n = 150 * m + i”]
  \\ qexists_tac ‘dy DIV 150’
  \\ qexists_tac ‘dx DIV 150’
  \\ qexists_tac ‘dx MOD 150’
  \\ qexists_tac ‘dy MOD 150’
  \\ gvs [DIV_LT_X]
  \\ ‘0 < 150:num’ by gvs []
  \\ drule DIVISION
  \\ disch_then $ assume_tac o GSYM \\ gvs []
QED

Theorem masks_thm:
  simple_checks w h ins outs (rows2 : bexp list list) ∧
  masks w h ins outs = (m1,m2) ⇒
  rectangle w h m1 ∧ rectangle w h m2 ∧
  from_rows (-85,-85) m1 =
  circ_area (set (make_area w h)) (set (eval_io env ins)) (set (eval_io env outs)) 0 ∧
  from_rows (-85,-85) m2 =
  circ_area (set (make_area w h)) (set (eval_io env ins)) (set (eval_io env outs)) 30
Proof
  gvs [masks_def]
  \\ qabbrev_tac ‘bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F)’
  \\ qabbrev_tac ‘sets1 = or_io_areas (FILTER is_ns ins ++ FILTER is_ew outs) bools’
  \\ qabbrev_tac ‘sets2 = or_io_areas (FILTER is_ew ins ++ FILTER is_ns outs) bools’
  \\ qabbrev_tac ‘dsets1 = diff (make_base_area w h) sets1’
  \\ qabbrev_tac ‘dsets2 = diff (make_base_area w h) sets2’
  \\ strip_tac \\ gvs []
  \\ ‘rectangle w h bools’ by gvs [rectangle_def,Abbr‘bools’]
  \\ ‘rectangle w h sets1 ∧ rectangle w h sets2’ by metis_tac [or_io_areas_rectangle]
  \\ ‘rectangle w h (make_base_area w h)’ by
   (gvs [rectangle_def,make_base_area_def,add_margin_def]
    \\ gvs [] \\ CASE_TAC
    >- gvs [rich_listTheory.REPLICATE_NIL,simple_checks_def]
    \\ Cases_on ‘150 * h’ \\ gvs [simple_checks_def])
  \\ ‘rectangle w h dsets1 ∧ rectangle w h dsets2’
    by metis_tac [diff_rectangle]
  \\ conj_tac >- metis_tac [or_rectangle]
  \\ conj_tac >- metis_tac [or_rectangle]
  \\ DEP_REWRITE_TAC [from_rows_or]
  \\ conj_tac >- gvs [rectangle_def,LIST_REL_EL_EQN,EVERY_EL]
  \\ once_rewrite_tac [UNION_COMM]
  \\ gvs [Abbr‘dsets1’,Abbr‘dsets2’]
  \\ DEP_REWRITE_TAC [from_rows_diff]
  \\ conj_tac >- gvs [rectangle_def,LIST_REL_EL_EQN,EVERY_EL]
  \\ gvs [circ_area_def,eval_io_def,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
  \\ gvs [make_base_area_thm]
  \\ rpt $ irule_at Any
       (METIS_PROVE [] “y1 = y2 ∧ z1 = z2 ⇒ (x DIFF y1) ∪ z1 = (x DIFF y2) ∪ z2”)
  \\ drule or_io_areas_eq \\ gvs [Abbr‘sets1’,Abbr‘sets2’]
  \\ disch_then (fn th => DEP_REWRITE_TAC [th])
  \\ conj_tac >- (gvs [SUBSET_DEF,MEM_FILTER] \\ rw [] \\ gvs [])
  \\ gvs [circ_io_area_def,eval_io_def,MEM_MAP,MEM_FILTER,PULL_EXISTS,EXISTS_PROD]
  \\ gvs [is_ns_def,is_ew_def] \\ gvs [SF DNF_ss]
  \\ gvs [EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
  \\ metis_tac []
QED

Theorem gol_checked_steps_1:
  gol_checked_steps 30 rows (shrink m1) = SOME rows1 ∧
  simple_checks w h ins outs (rows2 : bexp list list) ∧
  masks w h ins outs = (m1,m2) ∧
  rectangle w h rows ⇒
  steps (from_rows (-85,-85) (MAP (MAP (eval env)) rows))
        (circ_area (set (make_area w h)) (set (eval_io env ins)) (set (eval_io env outs)) 0)
        (from_rows (-85,-85) (MAP (MAP (eval env)) rows1))
Proof
  rw [] \\ irule gol_checked_steps_gen
  \\ last_x_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ drule_all masks_thm \\ gvs []
QED

Theorem gol_checked_steps_2:
  gol_checked_steps 30 rows (shrink m2) = SOME rows1 ∧
  simple_checks w h ins outs (rows2 : bexp list list) ∧
  masks w h ins outs = (m1,m2) ∧
  rectangle w h rows ⇒
  from_rows (-85,-85) (MAP (MAP (eval env)) rows) = x ∧
  from_rows (-85,-85) (MAP (MAP (eval env)) rows1) = y ⇒
  steps x (circ_area (set (make_area w h)) (set (eval_io env ins))
                     (set (eval_io env outs)) 30) y
Proof
  rw [] \\ irule gol_checked_steps_gen
  \\ last_x_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ drule_all masks_thm \\ gvs []
QED

Theorem simulation_ok_thm:
  simulation_ok w h ins outs rows ⇒
  (∀env.
    run_to 60
      (circ_mod (set (make_area w h))
                (set (eval_io env ins))
                (set (eval_io env outs))
                {})
      (from_rows (-85,-85) (MAP (MAP (eval env)) rows))
      (from_rows (-85,-85) (MAP (MAP (eval (age 1 env))) rows)))
Proof
  rw [] \\ gvs [simulation_ok_def] \\ gvs [opt_bool]
  \\ pairarg_tac \\ gvs []
  \\ ‘rectangle w h rows’ by gvs [simple_checks_def]
  \\ ‘rectangle w h rows1’ by imp_res_tac gol_checked_steps_rectangle
  \\ irule run_to_60_lemma \\ gvs [GSYM make_area_def]
  \\ qexists_tac ‘from_rows (-85,-85) (MAP (MAP (eval env)) rows1)’
  \\ qexists_tac ‘from_rows (-85,-85) (MAP (MAP (eval env)) rows2)’
  \\ conj_tac >- gvs [gol_checked_steps_1,SF SFY_ss]
  \\ qabbrev_tac ‘bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) F)’
  \\ qabbrev_tac ‘falses = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) False)’
  \\ qabbrev_tac ‘outs_ns = or_io_areas (FILTER is_ns outs) bools’
  \\ qabbrev_tac ‘outs_ew = or_io_areas (FILTER is_ew outs) bools’
  \\ qabbrev_tac ‘rows1a = diff_rows rows1 outs_ns’
  \\ qabbrev_tac ‘rows2a = diff_rows rows2 outs_ew’
  \\ irule_at Any gol_checked_steps_2
  \\ first_assum $ irule_at $ Pos hd \\ gvs []
  \\ first_assum $ irule_at $ Pos hd \\ gvs []
  \\ ‘rectangle w h bools ∧ rectangle w h falses’ by
        gvs [Abbr‘bools’,Abbr‘falses’,rectangle_def]
  \\ ‘rectangle w h outs_ns ∧ rectangle w h rows1a’ by
        metis_tac [or_io_areas_rectangle,diff_rows_rectangle]
  \\ ‘rectangle w h rowsA’ by metis_tac [or_lwss_rectangle]
  \\ ‘rectangle w h rows2’ by metis_tac [gol_checked_steps_rectangle]
  \\ ‘rectangle w h outs_ew ∧ rectangle w h rows2a’ by
        metis_tac [or_io_areas_rectangle,diff_rows_rectangle]
  \\ gvs [circ_io_lwss_def,set_INTER,FILTER_eval_io,lwss_29_59]
  \\ rpt $ dxrule or_lwss_imp
  \\ rpt $ disch_then $ drule_then assume_tac
  \\ rpt $ pop_assum drule
  \\ rpt (disch_then $ qspec_then ‘env’ mp_tac \\ impl_tac >-
           gvs [SUBSET_DEF,MEM_FILTER] \\ strip_tac)
  \\ ‘∀env. from_rows (-85,-85) (MAP (MAP (eval env)) falses) = {}’ by
    (gvs [Abbr‘falses’] \\ irule from_rows_EMPTY \\ gvs [Abbr‘bools’])
  \\ gvs [] \\ rpt disch_tac
  \\ gvs [MAP_MAP_inc_vars,circ_output_area_def,set_INTER,FILTER_eval_io]
  \\ ‘from_rows (-85,-85) (MAP (MAP (eval env)) rows1a) =
      from_rows (-85,-85) (MAP (MAP (eval env)) rows1) DIFF
         circ_io_area (set (eval_io env (FILTER is_ns outs)))’ by
    (unabbrev_all_tac \\ irule diff_rows_thm \\ gvs []
     \\ last_x_assum $ irule_at $ Pos last \\ gvs [SUBSET_DEF,MEM_FILTER])
  \\ ‘from_rows (-85,-85) (MAP (MAP (eval env)) rows2a) =
      from_rows (-85,-85) (MAP (MAP (eval env)) rows2) DIFF
         circ_io_area (set (eval_io env (FILTER is_ew outs)))’ by
    (unabbrev_all_tac \\ irule diff_rows_thm \\ gvs []
     \\ last_x_assum $ irule_at $ Pos last \\ gvs [SUBSET_DEF,MEM_FILTER])
  \\ ‘from_rows (-85,-85) (MAP (MAP (eval env)) (inter_rows rows1 outs_ns)) =
      from_rows (-85,-85) (MAP (MAP (eval env)) rows1) ∩
      circ_io_area (set (eval_io env (FILTER is_ns outs)))’ by
    (unabbrev_all_tac \\ irule inter_rows_thm \\ gvs []
     \\ last_x_assum $ irule_at $ Pos last \\ gvs [SUBSET_DEF,MEM_FILTER])
  \\ ‘from_rows (-85,-85) (MAP (MAP (eval env)) (inter_rows rows2 outs_ew)) =
      from_rows (-85,-85) (MAP (MAP (eval env)) rows2) ∩
      circ_io_area (set (eval_io env (FILTER is_ew outs)))’ by
    (unabbrev_all_tac \\ irule inter_rows_thm \\ gvs []
     \\ last_x_assum $ irule_at $ Pos last \\ gvs [SUBSET_DEF,MEM_FILTER])
  \\ gvs [AC UNION_COMM UNION_ASSOC]
QED

Theorem MEM_eval_io:
  MEM ((x,y),d,f) (eval_io env ins) ⇒
  ∃e. MEM ((x,y),d,e) ins ∧ f = (λn. eval (age n env) e)
Proof
  gvs [eval_io_def,MEM_MAP,EXISTS_PROD] \\ metis_tac []
QED

Triviality ALL_DISTINCT_MAP_FST:
  ALL_DISTINCT (MAP FST xs) ⇒
  MEM (x,y) xs ∧ MEM (x,z) xs ⇒ y = z
Proof
  Induct_on ‘xs’ \\ gvs [FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ metis_tac []
QED

Theorem simulation_ok_IMP_circuit:
  simulation_ok w h ins outs rows ⇒
  ∀env.
    circuit (make_area w h)
            (eval_io env ins)
            (eval_io env outs) []
            (from_rows (-85,-85) (MAP (MAP (eval env)) rows))
Proof
  strip_tac \\ gen_tac
  \\ irule imp_circuit
  \\ simp [PULL_FORALL] \\ gen_tac
  \\ irule_at Any simulation_ok_thm \\ simp []
  \\ ‘simple_checks w h ins outs rows’ by gvs [simulation_ok_def]
  \\ gvs [simple_checks_def,ALL_DISTINCT_APPEND]
  \\ gvs [circ_mod_wf_def,EVERY_MEM,FORALL_PROD]
  \\ conj_tac
  >- simp [make_area_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
  \\ rpt strip_tac
  \\ imp_res_tac MEM_eval_io \\ gvs []
  \\ gvs [SF SFY_ss]
  \\ gvs [MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ metis_tac [ALL_DISTINCT_MAP_FST,PAIR_EQ]
QED

val _ = export_theory();
