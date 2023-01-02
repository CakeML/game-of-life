(*
  Defines a coordinate system and tiles that cover GOL area.
*)
open preamble gol_rulesTheory;

val _ = new_theory "gol_tiles";

Overload L[local] = “15:num”;

Definition fromStrings_def:
  fromStrings i j [] = ([]:(int # int) list) ∧
  fromStrings i j (str :: strs) =
    FLAT (MAPi (λn c. if MEM c "  ." then [] else [(& n + i,j)]) str) ++
    fromStrings i (j+1) strs
End

Definition build_def:
  build i j strs =
    QSORT (λ(i1,j1) (i2,j2). if i1 = i2 then j1 ≤ j2 else i1 ≤ i2)
      (fromStrings i j strs)
End

Definition real_xy_def:
  real_xy (m,n) =
    (m * & L + n * & L : int,
     n * & L - m * & L : int)
End

Theorem real_xy_11:
  ∀a b. real_xy a = real_xy b ⇒ a = b
Proof
  fs [FORALL_PROD] \\ rpt gen_tac
  \\ rename [‘_ (m,n) = _ (m',n')’]
  \\ Cases_on ‘m = m'’ \\ gvs []
  \\ fs [real_xy_def] \\ intLib.COOPER_TAC
QED

Theorem real_xy_even:
  real_xy (m,n) = (x,y) ⇒
  ∃i j. x = i * &L ∧ y = j * &L ∧ (i+j) % 2 = 0
Proof
  rw [real_xy_def]
  \\ qexists_tac ‘m+n’
  \\ qexists_tac ‘n-m’
  \\ fs [integerTheory.INT_RDISTRIB,integerTheory.INT_SUB_RDISTRIB]
  \\ ‘(m + n + (n − m)) = 2 * n’ by intLib.COOPER_TAC \\ fs []
  \\ once_rewrite_tac [integerTheory.INT_MUL_COMM]
  \\ fs [integerTheory.INT_MOD_COMMON_FACTOR]
QED

val corner =
  “REVERSE (GENLIST (λy. (GENLIST (λx. (if y <= x then #"x" else #"."))) L) L)”
  |> EVAL |> concl |> rand
val half = “^corner ++ TL (REVERSE ^corner)” |> EVAL |> concl |> rand
val full = “MAP (λxs. xs ++ REVERSE xs) ^half” |> EVAL |> concl |> rand
val tile_tm = “build 0 (1 - &L) ^full” |> EVAL |> concl |> rand

Definition tile_def:
  tile = ^tile_tm
End

Definition translate_def:
  translate (i,j) = MAP (λ(x,y). (x+i:int,y+j:int))
End

Definition tile_at_def:
  tile_at (x,y) = translate (real_xy (x,y)) tile
End

Theorem tile_at_0:
  tile_at (0,0) = tile
Proof
  fs [tile_at_def,real_xy_def,translate_def,miscTheory.MAP_EQ_ID,FORALL_PROD]
QED

Theorem DISJOINT_set_set:
  DISJOINT (set xs) (set ys) = EVERY (λy. ~MEM y xs) ys
Proof
  fs [IN_DISJOINT,EVERY_MEM] \\ metis_tac []
QED

Theorem DISJOINT_prop:
  EVERY P xs ∧ EVERY (λx. ~P x) ys ⇒
  DISJOINT (set xs) (set ys)
Proof
  fs [IN_DISJOINT,EVERY_MEM] \\ metis_tac []
QED

Definition check_pairs_def:
  check_pairs [] = T ∧
  check_pairs ((x,y)::xs) =
    (ALL_DISTINCT (y :: MAP SND (FILTER (λ(a,b). a = x) xs)) ∧
     check_pairs (FILTER (λ(a,b). a ≠ x) xs))
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw [] \\ Induct_on ‘xs’ \\ rw [FORALL_PROD]
End

Theorem check_pairs_thm:
  ∀xs. check_pairs xs ⇔ ALL_DISTINCT xs
Proof
  ho_match_mp_tac check_pairs_ind
  \\ rw [check_pairs_def]
  \\ fs [MEM_MAP,EXISTS_PROD,MEM_FILTER]
  \\ Cases_on ‘MEM (x,y) xs’ \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on ‘xs’ \\ fs [FORALL_PROD] \\ rw []
  \\ fs [MEM_MAP,EXISTS_PROD,MEM_FILTER]
  \\ metis_tac []
QED

Theorem check_pairs_IMP_DISJOINT_set:
  check_pairs (xs ++ ys) ⇒
  DISJOINT (set xs) (set ys)
Proof
  fs [check_pairs_thm] \\ rw [DISJOINT_set_set,ALL_DISTINCT_APPEND]
  \\ fs [EVERY_MEM] \\ metis_tac []
QED

Theorem DISJOINT_tile_lemma[local]:
  a ≠ (0,0) ⇒ DISJOINT (set (tile_at a)) (set tile)
Proof
  PairCases_on ‘a’ \\ fs [tile_at_def]
  \\ Cases_on ‘real_xy (a0,a1)’
  \\ drule real_xy_even \\ rw []
  \\ Cases_on ‘2 <= i’
  THEN1
   (irule DISJOINT_prop
    \\ qexists_tac ‘λ(x,y). 2 * &L ≤ x’
    \\ EVAL_TAC \\ intLib.COOPER_TAC)
  \\ Cases_on ‘i <= -2’
  THEN1
   (irule DISJOINT_prop
    \\ qexists_tac ‘λ(x,y). x < 0’
    \\ EVAL_TAC \\ intLib.COOPER_TAC)
  \\ Cases_on ‘2 <= j’
  THEN1
   (irule DISJOINT_prop
    \\ qexists_tac ‘λ(x,y). &L ≤ y’
    \\ EVAL_TAC \\ intLib.COOPER_TAC)
  \\ Cases_on ‘j <= -2’
  THEN1
   (irule DISJOINT_prop
    \\ qexists_tac ‘λ(x,y). y < - & L’
    \\ EVAL_TAC \\ rw [] \\ TRY intLib.COOPER_TAC)
  \\ Cases_on ‘i=0’ THEN1
   (Cases_on ‘j = 0’
    THEN1 (gvs [real_xy_def] \\ ‘F’ by intLib.COOPER_TAC)
    \\ ‘j = 1 \/ j = -1’ by intLib.COOPER_TAC \\ gvs [])
  \\ Cases_on ‘j=0’ THEN1
   (‘i = 1 \/ i = -1’ by intLib.COOPER_TAC \\ gvs [])
  \\ ‘(j = 1 ∨ j = -1) ∧ (i = 1 ∨ i = -1)’ by
   (Cases_on ‘i=1’ THEN1 (gvs [] \\ intLib.COOPER_TAC)
    \\ Cases_on ‘i=-1’ THEN1 (gvs [] \\ intLib.COOPER_TAC)
    \\ Cases_on ‘i’ \\ fs [])
  \\ gvs []
  \\ irule check_pairs_IMP_DISJOINT_set
  \\ CONV_TAC (RAND_CONV EVAL) \\ EVAL_TAC
QED

Theorem DISJOINT_IMAGE:
  INJ (f:'a -> 'a) UNIV UNIV ∧ DISJOINT (IMAGE f s) (IMAGE f t) ⇒ DISJOINT s t
Proof
  rw [IN_DISJOINT,IN_IMAGE] \\ CCONTR_TAC \\ fs []
  \\ first_x_assum (qspec_then ‘f x’ mp_tac)
  \\ ‘∀x' y. f x' = f y ⇔ x' = y’ by metis_tac [INJ_DEF,IN_UNIV]
  \\ fs []
QED

Theorem DISJOINT_tile_at_add:
  DISJOINT (set (tile_at (a1+i,a2+j))) (set (tile_at (b1+i,b2+j)))
  ⇒ DISJOINT (set (tile_at (a1,a2))) (set (tile_at (b1,b2)))
Proof
  rw [] \\ irule DISJOINT_IMAGE
  \\ ‘∃ix iy. real_xy (i,j) = (ix,iy)’ by metis_tac [PAIR]
  \\ qexists_tac ‘λ(x,y). (x+ix,y+iy)’
  \\ reverse conj_tac THEN1 fs [INJ_DEF,FORALL_PROD]
  \\ last_x_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] “x = x1 ∧ y = y1 ⇒ a x y ⇒ a x1 y1”)
  \\ fs [GSYM LIST_TO_SET_MAP]
  \\ fs [tile_at_def,translate_def,real_xy_def,MAP_MAP_o,o_DEF,LAMBDA_PROD]
  \\ gvs [integerTheory.INT_RDISTRIB,integerTheory.INT_SUB_RDISTRIB]
  \\ rpt strip_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ rw [FUN_EQ_THM]
  \\ intLib.COOPER_TAC
QED

Theorem DISJOINT_tile:
  a ≠ b ⇒ DISJOINT (set (tile_at a)) (set (tile_at b))
Proof
  PairCases_on ‘a’ \\ PairCases_on ‘b’ \\ fs []
  \\ strip_tac
  \\ irule DISJOINT_tile_at_add
  \\ qexists_tac ‘-b0’
  \\ qexists_tac ‘-b1’
  \\ fs [tile_at_0]
  \\ irule DISJOINT_tile_lemma \\ fs []
  \\ intLib.COOPER_TAC
QED

val _ = export_theory();
