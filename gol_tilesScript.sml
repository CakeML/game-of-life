(*
  Defines a coordinate system and tiles that cover GOL area.
*)
open preamble gol_rulesTheory;

val _ = new_theory "gol_tiles";

Overload L[local] = “5:num”;

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

val tile_tm = “build (-2) 0
  [ "..x..";
    ".xxx.";
    "xxxxx";
    ".xxx.";
    "..x.."]” |> EVAL |> concl |> rand

Definition tile_def:
  tile =
    [                (-2,2);
             (-1,1); (-1,2); (-1,3);
      (0,0); ( 0,1); ( 0,2); ( 0,3); (0,4);
             ( 1,1); ( 1,2); ( 1,3);
                     ( 2,2);                 ] : (int # int) list
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

Theorem DISJOINT_tile_lemma[local]:
  a ≠ (0,0) ⇒ DISJOINT (set (tile_at a)) (set tile)
Proof
  PairCases_on ‘a’ \\ fs [tile_at_def]
  \\ Cases_on ‘real_xy (a0,a1)’
  \\ drule real_xy_even \\ rw []
  \\ Cases_on ‘2 <= j’
  THEN1 (fs [tile_def,translate_def] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘j <= -2’
  THEN1 (fs [tile_def,translate_def] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘2 <= i’
  THEN1 (fs [tile_def,translate_def] \\ Cases_on ‘i=0’ \\ gvs [] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘i <= -2’
  THEN1 (fs [tile_def,translate_def] \\ Cases_on ‘i=0’ \\ gvs [] \\ intLib.COOPER_TAC)
  \\ Cases_on ‘i=0’ THEN1
   (Cases_on ‘j = 0’
    THEN1 (gvs [real_xy_def] \\ ‘F’ by intLib.COOPER_TAC)
    \\ ‘j = 1 \/ j = -1’ by intLib.COOPER_TAC \\ gvs [])
  \\ Cases_on ‘j=0’ THEN1
   (‘i = 1 \/ i = -1’ by intLib.COOPER_TAC \\ gvs [])
  \\ fs [DISJOINT_set_set]
  \\ Cases_on ‘i=1’
  THEN1 (‘j = 1 \/ j = -1’ by intLib.COOPER_TAC \\ gvs [] \\ EVAL_TAC)
  \\ Cases_on ‘i=-1’
  THEN1 (‘j = 1 \/ j = -1’ by intLib.COOPER_TAC \\ gvs [] \\ EVAL_TAC)
  \\ Cases_on ‘i’ \\ fs []
QED

Theorem DISJOINT_tile_at_add:
  DISJOINT (set (tile_at (a1+i,a2+j))) (set (tile_at (b1+i,b2+j)))
  ⇒ DISJOINT (set (tile_at (a1,a2))) (set (tile_at (b1,b2)))
Proof
  fs [IN_DISJOINT,tile_at_def,tile_def,translate_def,real_xy_def]
  \\ fs [integerTheory.INT_RDISTRIB,integerTheory.INT_SUB_RDISTRIB]
  \\ rw []
  \\ PairCases_on ‘x’ \\ fs []
  \\ first_x_assum (qspec_then ‘(x0 + i * 5 + j * 5,x1 + j * 5 - i * 5)’ mp_tac)
  \\ fs [] \\ rpt strip_tac
  \\ ‘∀x0 a1 a2.
        x0 + i * 5 + j * 5 = a1 + i * 5 + (a2 + j * 5) ⇔ x0 = a1+a2’ by
        intLib.COOPER_TAC \\ fs []
  \\ ‘∀x0 a1 a2.
        x0 + j * 5 - i * 5 = a1 + j * 5 - (a2 + i * 5) ⇔ x0 = a1-a2’ by
        intLib.COOPER_TAC \\ fs []
  \\ ‘∀x0 a1 a2 k.
        x0 + j * 5 - i * 5 = k + (a1 + j * 5 - (a2 + i * 5)) ⇔ x0 = k+a1-a2’ by
        intLib.COOPER_TAC \\ fs []
  THEN1 (disj1_tac \\ CCONTR_TAC \\ fs [] \\ intLib.COOPER_TAC \\ fs [])
  \\ disj2_tac \\ CCONTR_TAC \\ fs [] \\ intLib.COOPER_TAC \\ fs []
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
