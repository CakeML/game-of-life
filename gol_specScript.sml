(*
  Definition of spec for writing specifications for GOL gates
*)
open preamble gol_rulesTheory integerTheory;

val _ = new_theory "gol_spec";

(* converting from pixel coordinates to 75x75 block coordinates *)

Definition pixel_xy_def:
  pixel_xy (i:int) (j:int) =
    (i / 75, Num (i % 75),
     j / 75, Num (j % 75))
End

Theorem pixel_xy_exists:
  pixel_xy i j = (ix,x,iy,y) ⇒
  i = 75 * ix + & x ∧ x < 75 ∧
  j = 75 * iy + & y ∧ y < 75
Proof
  strip_tac \\ gvs [pixel_xy_def]
  \\ assume_tac $ MATCH_MP INT_DIVISION (intLib.COOPER_PROVE “75 ≠ 0:int”)
  \\ first_assum $ qspec_then ‘i’ mp_tac
  \\ first_x_assum $ qspec_then ‘j’ mp_tac
  \\ strip_tac \\ strip_tac \\ fs []
  \\ intLib.COOPER_TAC
QED

(* interface info *)

Datatype:
  cell_owner = Sender
             | Receiver
             | Shared
             | Signal
End

Type interface_info = “:(cell_owner list list) # bool”
Type intrefaces = “:((int # int) # interface_info) list”

Definition xy_of_def:
  xy_of (ins:intrefaces) = { a | ALOOKUP ins a ≠ NONE } :(int # int) set
End

Definition el_el_def:
  el_el i j l =
    case LLOOKUP l j of
    | NONE => NONE
    | SOME xs => LLOOKUP xs i
End

Definition interface_pixel_def:
  interface_pixel (is:intrefaces) (a:cell_owner) (x,y) ⇔
    let (ib,i,jb,j) = pixel_xy x y in
      case ALOOKUP is (ib:int,jb:int) of
      | SOME (shape,b) => el_el i j shape = SOME a
      | _ => F
End

Definition comm_pixels_of_def:
  comm_pixels_of is (x,y) ⇔
    interface_pixel is Shared (x,y) ∨
    interface_pixel is Signal (x,y)
End

Definition signal_pixels_of_def:
  signal_pixels_of is (x,y) ⇔
    let (ib,i,jb,j) = pixel_xy x y in
      case ALOOKUP is (ib:int,jb:int) of
      | SOME (shape,b) => el_el i j shape = SOME Signal ∧ b
      | _ => F
End

(* taking 60 steps inside boundaries for borders *)

Definition steps_def:
  steps n x s1 s2 ⇔
    FUNPOW step n s1 = s2 ∧
    ∀k. k ≤ n ⇒ infl (FUNPOW step k s1) ⊆ x
End

Definition steps60_def:
  steps60 s0 x1 x2 x3 s3 ⇔
    ∃s1 s2.
      steps 20 x1 s0 s1 ∧
      steps 20 x2 s1 s2 ∧
      steps 20 x3 s2 s3
End

(* definition of spec *)

Definition int_even_def:
  int_even (i:int) = EVEN (Num (ABS i))
End

Definition set_every_def:
  set_every s p = ∀e. e ∈ s ⇒ p e
End

Definition area_ok_def:
  area_ok (area :(int # int) set) (borders:(int # int) set)
          (ins:intrefaces) (outs:intrefaces) ⇔
     set_every area (λ(x,y). int_even x ∧ int_even y) ∧
     set_every borders (λ(x,y). int_even x ≠ int_even y) ∧
     set_every (xy_of ins) (λ(x,y). int_even x ≠ int_even y) ∧
     set_every (xy_of outs) (λ(x,y). int_even x ≠ int_even y) ∧
     DISJOINT (xy_of ins) borders ∧ DISJOINT (xy_of outs) borders ∧
     (∀x y. ((x,y) ∈ area ⇎ (x+2,y) ∈ area) ⇒
            (x+1,y) ∈ (xy_of ins ∪ xy_of outs ∪ borders)) ∧
     (∀x y. ((x,y) ∈ area ⇎ (x,y+2) ∈ area) ⇒
            (x,y+1) ∈ (xy_of ins ∪ xy_of outs ∪ borders)) ∧
     ALL_DISTINCT (MAP FST ins) ∧ ALL_DISTINCT (MAP FST outs) ∧
     (∀x y i1 b1 i2 b2.
        MEM ((x,y),(i1,b1)) ins ∧ MEM ((x,y),(i2,b2)) outs ⇒ i1 = i2)
End

Definition decide_corner_def:
  decide_corner area ib i jb j =
    let x = (if i < 75 DIV 2 then ib else ib+1) in
    let y = (if j < 75 DIV 2 then jb else jb+1) in
      (x:int,y:int) ∈ area
End

Definition decide_border_area_def:
  decide_border_area area (ib:int) (i:num) (jb:int) (j:num) =
    if int_even ib then
      if j < 75 DIV 2 then (ib,jb-1) ∈ area else (ib,jb+1) ∈ area
    else (* we know: int_even jb *)
      if i < 75 DIV 2 then (ib-1,jb) ∈ area else (ib+1,jb) ∈ area
End

Definition core_pixels_of_def:
  core_pixels_of area ins outs comms (x,y) ⇔
    let (ib,i,jb,j) = pixel_xy x y in
      if int_even ib ∧ int_even jb then
        (ib,jb) ∈ area
      else if ~int_even ib ∧ ~int_even jb then
        decide_corner area ib i jb j
      else
        interface_pixel ins Receiver (x,y) ∨
        interface_pixel outs Sender (x,y) ∨
        interface_pixel comms Shared (x,y) ∨
        interface_pixel comms Signal (x,y) ∨
        (ALOOKUP (ins++outs) (ib,jb) = NONE ∧
         decide_border_area area ib i jb j)
End

Definition spec_def:
  spec (area :(int # int) set) (borders:(int # int) set)
       (s1:(int # int) set) (ins:intrefaces)
       (s2:(int # int) set) (outs:intrefaces) ⇔
    area_ok area borders ins outs ∧
    steps60 (s1 ∪ signal_pixels_of ins)
            (core_pixels_of area ins outs ins)
            (core_pixels_of area ins outs [])
            (core_pixels_of area ins outs outs)
            (s2 ∪ signal_pixels_of outs)
End

Theorem imp_spec_00_lemma[local]:
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  EVERY (λ(p,r). MEM p [(0,1);(0,-1);(1,0);(-1,0)]) (ins ++ outs) ∧
  steps60
     (s1 ∪ signal_pixels_of ins)
     (core_pixels_of {(0,0)} ins outs ins)
     (core_pixels_of {(0,0)} ins outs [])
     (core_pixels_of {(0,0)} ins outs outs)
     (s2 ∪ signal_pixels_of outs)
  ⇒
  spec {(0,0)} ({(0,1);(0,-1);(1,0);(-1,0)} DIFF (xy_of ins UNION (xy_of outs)))
    s1 ins s2 outs
Proof
  rewrite_tac [spec_def,ALL_DISTINCT_APPEND]
  \\ strip_tac
  \\ ‘set_every (xy_of ins) (λ(x,y). int_even x ⇎ int_even y) ∧
      set_every (xy_of outs) (λ(x,y). int_even x ⇎ int_even y)’ by
   (fs [EVERY_APPEND] \\ fs [EVERY_MEM,set_every_def,FORALL_PROD,xy_of_def]
    \\ fs [ALOOKUP_NONE,MEM_MAP,EXISTS_PROD]
    \\ rw [] \\ res_tac \\ fs [int_even_def])
  \\ asm_rewrite_tac [area_ok_def]
  \\ rpt strip_tac
  >- fs [set_every_def,int_even_def]
  >- (fs [set_every_def,int_even_def] \\ rw [] \\ fs [])
  >- (fs [IN_DISJOINT] \\ CCONTR_TAC \\ fs [] \\ gvs [])
  >- (fs [IN_DISJOINT] \\ CCONTR_TAC \\ fs [] \\ gvs [])
  >- (Cases_on ‘(x,y) ∈ {(0,0)}’ \\ gvs [] >- metis_tac []
      \\ ‘x = -2’ by intLib.COOPER_TAC \\ gvs [] \\ metis_tac [])
  >- (Cases_on ‘(x,y) ∈ {(0,0)}’ \\ gvs [] >- metis_tac []
      \\ ‘y = -2’ by intLib.COOPER_TAC \\ gvs [] \\ metis_tac [])
  >- (fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ res_tac \\ gvs [])
QED

Definition bool_grid_def:
  bool_grid (x:int) (y:int) w h p =
    GENLIST (λj. GENLIST (λi. p (x + &i, y + & j) : bool) w) h
End

Definition grid_to_set_def:
  grid_to_set x y ys (i,j) ⇔
    y ≤ j ∧ x ≤ i ∧
    ∃xs. LLOOKUP ys (Num (j - y)) = SOME xs ∧
         LLOOKUP xs (Num (i - x)) = SOME T
End

Triviality le_imp_add_exists:
  x ≤ y ⇒ ∃k. y = x + (& k) :int
Proof
  rw []
  \\ qexists_tac ‘Num (y-x)’
  \\ intLib.COOPER_TAC
QED

Theorem grid_to_set_bool_grid:
  set_every s (λ(i,j). x ≤ i ∧ i < x + & w ∧ y ≤ j ∧ j < y + & h) ⇒
  grid_to_set x y (bool_grid x y w h s) = s
Proof
  fs [EXTENSION,set_every_def,FORALL_PROD]
  \\ rw [] \\ eq_tac \\ rw []
  >-
   (gvs [IN_DEF,grid_to_set_def]
    \\ gvs [oEL_EQ_EL]
    \\ dxrule le_imp_add_exists
    \\ dxrule le_imp_add_exists
    \\ strip_tac \\ strip_tac \\ gvs []
    \\ gvs [bool_grid_def])
  \\ first_x_assum drule
  \\ gvs [IN_DEF] \\ rw [grid_to_set_def]
  \\ gvs [oEL_EQ_EL]
  \\ dxrule le_imp_add_exists
  \\ dxrule le_imp_add_exists
  \\ strip_tac \\ strip_tac \\ gvs []
  \\ fs [bool_grid_def]
QED

Theorem bounds_core_pixels_of:
  EVERY (λ(p,r). MEM p [(0,1);(0,-1);(1,0);(-1,0)]) (ins ++ outs ++ comms) ⇒
  set_every (core_pixels_of {(0,0)} ins outs comms)
    (λ(i,j). -75 ≤ i ∧ i < -75 + 225 ∧ -75 ≤ j ∧ j < -75 + 225)
Proof
  fs [set_every_def,FORALL_PROD]
  \\ fs [IN_DEF,core_pixels_of_def]
  \\ strip_tac \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ gvs []
  \\ IF_CASES_TAC >- fs []
  \\ IF_CASES_TAC >-
   (gvs [] \\ fs [decide_corner_def]
    \\ rw [] \\ intLib.COOPER_TAC)
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac
  \\ strip_tac
  >-
   (gvs [interface_pixel_def]
    \\ Cases_on ‘ALOOKUP ins (ib,jb)’ \\ fs []
    \\ imp_res_tac ALOOKUP_MEM \\ fs [EVERY_MEM]
    \\ res_tac \\ fs [] \\ intLib.COOPER_TAC)
  >-
   (gvs [interface_pixel_def]
    \\ Cases_on ‘ALOOKUP outs (ib,jb)’ \\ fs []
    \\ imp_res_tac ALOOKUP_MEM \\ fs [EVERY_MEM]
    \\ res_tac \\ fs [] \\ intLib.COOPER_TAC)
  >-
   (gvs [interface_pixel_def]
    \\ Cases_on ‘ALOOKUP comms (ib,jb)’ \\ fs []
    \\ imp_res_tac ALOOKUP_MEM \\ fs [EVERY_MEM]
    \\ res_tac \\ fs [] \\ intLib.COOPER_TAC)
  >-
   (gvs [interface_pixel_def]
    \\ Cases_on ‘ALOOKUP comms (ib,jb)’ \\ fs []
    \\ imp_res_tac ALOOKUP_MEM \\ fs [EVERY_MEM]
    \\ res_tac \\ fs [] \\ intLib.COOPER_TAC)
  \\ fs [decide_border_area_def]
  \\ every_case_tac \\ gvs [int_even_def]
  \\ intLib.COOPER_TAC
QED

Theorem bool_grid_add_height:
  bool_grid x y w (h1 + h2) p =
  bool_grid x y w h1 p ++ bool_grid x (y + & h1) w h2 p
Proof
  rewrite_tac [bool_grid_def, GENLIST_APPEND |> ONCE_REWRITE_RULE [ADD_COMM]]
  \\ fs [] \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM] \\ rw [] \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM] \\ rw [] \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ intLib.COOPER_TAC
QED

Theorem bool_grid_add_width:
  ∀h w1 w2 x y p.
    bool_grid x y (w1 + w2) h p =
    MAP2 $++ (bool_grid x y w1 h p) (bool_grid (x + & w1) y w2 h p)
Proof
  Induct >- fs [bool_grid_def]
  \\ fs [GENLIST_CONS,o_DEF,bool_grid_def] \\ rw []
  \\ rewrite_tac [GENLIST_APPEND |> ONCE_REWRITE_RULE [ADD_COMM]] \\ fs []
  \\ fs [GSYM integerTheory.INT_ADD,AC INT_ADD_ASSOC INT_ADD_COMM,ADD1]
  \\ first_x_assum $ qspecl_then [‘w1’,‘w2’,‘x’,‘y+1’,‘p’] mp_tac
  \\ rewrite_tac [GENLIST_APPEND |> ONCE_REWRITE_RULE [ADD_COMM]] \\ fs []
  \\ fs [GSYM integerTheory.INT_ADD,AC INT_ADD_ASSOC INT_ADD_COMM,ADD1]
QED

Theorem bool_grid_eq:
  bool_grid x y w h p = bool_grid x y w h q ⇔
  ∀i j. i < w ∧ j < h ⇒ p (x + &i, y + & j) = q (x + & i, y + & j)
Proof
  fs [bool_grid_def,listTheory.GENLIST_FUN_EQ] \\ metis_tac []
QED

Theorem alookup_filter:
  ∀xs x. ALOOKUP (FILTER (λ(p,q). p = x) xs) x = ALOOKUP xs x
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
QED

Theorem bool_grid_n:
  bool_grid 0 (-75) 75 75
    (core_pixels_of {(0,0)} ins outs comms) =
  bool_grid 0 (-75) 75 75
    (core_pixels_of {(0,0)}
      (FILTER (λ(p,x). (0,-1) = p) ins)
      (FILTER (λ(p,x). (0,-1) = p) outs)
      (FILTER (λ(p,x). (0,-1) = p) comms))
Proof
  fs [bool_grid_eq,core_pixels_of_def]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = 0 ∧ jb = -1’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ fs [interface_pixel_def]
  \\ fs [alookup_filter,ALOOKUP_APPEND]
QED

Theorem bool_grid_s:
  bool_grid 0 75 75 75
    (core_pixels_of {(0,0)} ins outs comms) =
  bool_grid 0 75 75 75
    (core_pixels_of {(0,0)}
      (FILTER (λ(p,x). (0,1) = p) ins)
      (FILTER (λ(p,x). (0,1) = p) outs)
      (FILTER (λ(p,x). (0,1) = p) comms))
Proof
  fs [bool_grid_eq,core_pixels_of_def]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = 0 ∧ jb = 1’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ fs [interface_pixel_def]
  \\ fs [alookup_filter,ALOOKUP_APPEND]
QED

Theorem bool_grid_w:
  bool_grid (-75) 0 75 75
    (core_pixels_of {(0,0)} ins outs comms) =
  bool_grid (-75) 0 75 75
    (core_pixels_of {(0,0)}
      (FILTER (λ(p,x). (-1,0) = p) ins)
      (FILTER (λ(p,x). (-1,0) = p) outs)
      (FILTER (λ(p,x). (-1,0) = p) comms))
Proof
  fs [bool_grid_eq,core_pixels_of_def]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = -1 ∧ jb = 0’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ fs [interface_pixel_def]
  \\ fs [alookup_filter,ALOOKUP_APPEND]
QED

Theorem bool_grid_e:
  bool_grid 75 0 75 75
    (core_pixels_of {(0,0)} ins outs comms) =
  bool_grid 75 0 75 75
    (core_pixels_of {(0,0)}
      (FILTER (λ(p,x). (1,0) = p) ins)
      (FILTER (λ(p,x). (1,0) = p) outs)
      (FILTER (λ(p,x). (1,0) = p) comms))
Proof
  fs [bool_grid_eq,core_pixels_of_def]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = 1 ∧ jb = 0’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ fs [interface_pixel_def]
  \\ fs [alookup_filter,ALOOKUP_APPEND]
QED

val bool_grid_split1 =
  “bool_grid (-75) (-75) w (75 + 75 + 75) p”
  |> REWRITE_CONV [bool_grid_add_height]
  |> SIMP_RULE std_ss [INT_ADD_CALCULATE];

val bool_grid_split2 =
  “bool_grid x y (75 + (75 + 75)) h p”
  |> REWRITE_CONV [bool_grid_add_width]
  |> SIMP_RULE std_ss [INT_ADD_CALCULATE];

Theorem bool_grid_225_225 =
  (“bool_grid (-75) (-75) 225 225 p”
   |> (REWRITE_CONV [bool_grid_split1] THENC
       REWRITE_CONV [bool_grid_split2])
   |> SIMP_RULE std_ss [INT_ADD_CALCULATE]);

local
  val lemma = EVAL “bool_grid (-75) (-75) 75 75 (core_pixels_of {(0,0)} ins outs comms)”
  val corner_nw_def = Define ‘corner_nw = ^(concl lemma |> rand)’
in
  val bool_grid_corner_nw = REWRITE_RULE [GSYM corner_nw_def] lemma;
end

local
  val lemma = EVAL “bool_grid 75 (-75) 75 75 (core_pixels_of {(0,0)} ins outs comms)”
  val corner_ne_def = Define ‘corner_ne = ^(concl lemma |> rand)’
in
  val bool_grid_corner_ne = REWRITE_RULE [GSYM corner_ne_def] lemma;
end

local
  val lemma = EVAL “bool_grid (-75) 75 75 75 (core_pixels_of {(0,0)} ins outs comms)”
  val corner_sw_def = Define ‘corner_sw = ^(concl lemma |> rand)’
in
  val bool_grid_corner_sw = REWRITE_RULE [GSYM corner_sw_def] lemma;
end

local
  val lemma = EVAL “bool_grid 75 75 75 75 (core_pixels_of {(0,0)} ins outs comms)”
  val corner_se_def = Define ‘corner_se = ^(concl lemma |> rand)’
in
  val bool_grid_corner_se = REWRITE_RULE [GSYM corner_se_def] lemma;
end

local
  val lemma = EVAL “bool_grid 0 0 75 75 (core_pixels_of {(0,0)} ins outs comms)”
  val middle_def = Define ‘middle = ^(concl lemma |> rand)’
in
  val bool_grid_middle = REWRITE_RULE [GSYM middle_def] lemma;
end

Theorem bool_grid_225_225_core =
  (bool_grid_225_225 |> GEN_ALL
   |> Q.SPEC ‘core_pixels_of {(0,0)} ins outs comms’
   |> REWRITE_RULE [bool_grid_middle,
                    bool_grid_corner_nw,bool_grid_corner_ne,
                    bool_grid_corner_sw,bool_grid_corner_se]
   |> ONCE_REWRITE_RULE [bool_grid_e,bool_grid_w,bool_grid_s,bool_grid_n])

Theorem border_n =
  EVAL “bool_grid 0 (-75) 75 75 (core_pixels_of {(0,0)} [] [] [])”;

Theorem border_w =
  EVAL “bool_grid (-75) 0 75 75 (core_pixels_of {(0,0)} [] [] [])”;

Theorem border_e =
  EVAL “bool_grid 75 0 75 75 (core_pixels_of {(0,0)} [] [] [])”;

Theorem border_s =
  EVAL “bool_grid 0 75 75 75 (core_pixels_of {(0,0)} [] [] [])”;

Definition good_interface_def:
  good_interface shape ⇔
    LENGTH shape = 75 ∧ EVERY (λl. LENGTH l = 75) shape
End

Triviality bool_grid_eq_map_map:
  ∀xs h w x y p q.
    LENGTH xs = h ∧ EVERY (λl. LENGTH l = w) xs ∧
    (∀i j. i < w ∧ j < h ⇒ q (EL i (EL j xs)) = p (x + &i, y + &j)) ⇒
    bool_grid x y w h p = MAP (MAP q) xs
Proof
  Induct using SNOC_INDUCT
  >- fs [bool_grid_def]
  \\ fs [LENGTH_SNOC,EVERY_SNOC]
  \\ rw [] \\ rewrite_tac [bool_grid_add_height]
  \\ match_mp_tac (METIS_PROVE [] “xs = ys ∧ xs1 = ys1 ⇒ xs ++ xs1 = ys ++ ys1”)
  \\ strip_tac
  >-
   (last_x_assum irule \\ fs []
    \\ rw []
    \\ first_x_assum $ qspecl_then [‘i’,‘j’] mp_tac
    \\ fs [SNOC_APPEND,EL_APPEND1])
  \\ simp [bool_grid_def]
  \\ simp [GENLIST_eq_MAP]
  \\ rw []
  \\ first_x_assum $ qspecl_then [‘i’,‘LENGTH xs’] mp_tac
  \\ fs [SNOC_APPEND,EL_APPEND2]
QED

Theorem shape_e:
  good_interface shape ⇒
  bool_grid 75 0 75 75 (core_pixels_of {(0,0)} [((1,0),shape,b)] [] []) =
  MAP (MAP (λx. x = Receiver)) shape ∧
  bool_grid 75 0 75 75 (core_pixels_of {(0,0)} [((1,0),shape,b)] [] [((1,0),shape,b)]) =
  MAP (MAP (λx. x = Receiver ∨ x = Shared ∨ x = Signal)) shape ∧
  bool_grid 75 0 75 75 (core_pixels_of {(0,0)} [] [((1,0),shape,b)] []) =
  MAP (MAP (λx. x = Sender)) shape ∧
  bool_grid 75 0 75 75 (core_pixels_of {(0,0)} [] [((1,0),shape,b)] [((1,0),shape,b)]) =
  MAP (MAP (λx. x = Sender ∨ x = Shared ∨ x = Signal)) shape
Proof
  rewrite_tac [good_interface_def]
  \\ rpt strip_tac
  \\ irule bool_grid_eq_map_map \\ fs []
  \\ fs [core_pixels_of_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = 1 ∧ jb = 0’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ gvs [interface_pixel_def,el_el_def,AllCaseEqs(),miscTheory.LLOOKUP_EQ_EL]
  \\ gvs [EVERY_EL]
QED

Theorem shape_w:
  good_interface shape ⇒
  bool_grid (-75) 0 75 75 (core_pixels_of {(0,0)} [((-1,0),shape,b)] [] []) =
  MAP (MAP (λx. x = Receiver)) shape ∧
  bool_grid (-75) 0 75 75 (core_pixels_of {(0,0)} [((-1,0),shape,b)] [] [((-1,0),shape,b)]) =
  MAP (MAP (λx. x = Receiver ∨ x = Shared ∨ x = Signal)) shape ∧
  bool_grid (-75) 0 75 75 (core_pixels_of {(0,0)} [] [((-1,0),shape,b)] []) =
  MAP (MAP (λx. x = Sender)) shape ∧
  bool_grid (-75) 0 75 75 (core_pixels_of {(0,0)} [] [((-1,0),shape,b)] [((-1,0),shape,b)]) =
  MAP (MAP (λx. x = Sender ∨ x = Shared ∨ x = Signal)) shape
Proof
  rewrite_tac [good_interface_def]
  \\ rpt strip_tac
  \\ irule bool_grid_eq_map_map \\ fs []
  \\ fs [core_pixels_of_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = -1 ∧ jb = 0’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ gvs [interface_pixel_def,el_el_def,AllCaseEqs(),miscTheory.LLOOKUP_EQ_EL]
  \\ gvs [EVERY_EL]
QED

Theorem shape_n:
  good_interface shape ⇒
  bool_grid 0 (-75) 75 75 (core_pixels_of {(0,0)} [((0,-1),shape,b)] [] []) =
  MAP (MAP (λx. x = Receiver)) shape ∧
  bool_grid 0 (-75) 75 75 (core_pixels_of {(0,0)} [((0,-1),shape,b)] [] [((0,-1),shape,b)]) =
  MAP (MAP (λx. x = Receiver ∨ x = Shared ∨ x = Signal)) shape ∧
  bool_grid 0 (-75) 75 75 (core_pixels_of {(0,0)} [] [((0,-1),shape,b)] []) =
  MAP (MAP (λx. x = Sender)) shape ∧
  bool_grid 0 (-75) 75 75 (core_pixels_of {(0,0)} [] [((0,-1),shape,b)] [((0,-1),shape,b)]) =
  MAP (MAP (λx. x = Sender ∨ x = Shared ∨ x = Signal)) shape
Proof
  rewrite_tac [good_interface_def]
  \\ rpt strip_tac
  \\ irule bool_grid_eq_map_map \\ fs []
  \\ fs [core_pixels_of_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists
  \\ strip_tac \\ fs []
  \\ ‘ib = 0 ∧ jb = -1’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ gvs [interface_pixel_def,el_el_def,AllCaseEqs(),miscTheory.LLOOKUP_EQ_EL]
  \\ gvs [EVERY_EL]
QED

Theorem shape_s:
  good_interface shape ⇒
  bool_grid 0 75 75 75 (core_pixels_of {(0,0)} [((0,1),shape,b)] [] []) =
  MAP (MAP (λx. x = Receiver)) shape ∧
  bool_grid 0 75 75 75 (core_pixels_of {(0,0)} [((0,1),shape,b)] [] [((0,1),shape,b)]) =
  MAP (MAP (λx. x = Receiver ∨ x = Shared ∨ x = Signal)) shape ∧
  bool_grid 0 75 75 75 (core_pixels_of {(0,0)} [] [((0,1),shape,b)] []) =
  MAP (MAP (λx. x = Sender)) shape ∧
  bool_grid 0 75 75 75 (core_pixels_of {(0,0)} [] [((0,1),shape,b)] [((0,1),shape,b)]) =
  MAP (MAP (λx. x = Sender ∨ x = Shared ∨ x = Signal)) shape
Proof
  rewrite_tac [good_interface_def]
  \\ rpt strip_tac
  \\ irule bool_grid_eq_map_map \\ fs []
  \\ fs [core_pixels_of_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ drule pixel_xy_exists \\ strip_tac \\ fs []
  \\ ‘ib = 0 ∧ jb = 1’ by intLib.COOPER_TAC
  \\ gvs [int_even_def]
  \\ gvs [interface_pixel_def,el_el_def,AllCaseEqs(),miscTheory.LLOOKUP_EQ_EL]
  \\ gvs [EVERY_EL]
QED

Theorem imp_spec_00_lemma2[local]:
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  EVERY (λ(p,r). MEM p [(0,1);(0,-1);(1,0);(-1,0)]) (ins ++ outs) ∧
  steps60
     (s1 ∪ signal_pixels_of ins)
     (grid_to_set (-75) (-75)
        (bool_grid (-75) (-75) 225 225 (core_pixels_of {(0,0)} ins outs ins)))
     (grid_to_set (-75) (-75)
        (bool_grid (-75) (-75) 225 225 (core_pixels_of {(0,0)} ins outs [])))
     (grid_to_set (-75) (-75)
        (bool_grid (-75) (-75) 225 225 (core_pixels_of {(0,0)} ins outs outs)))
     (s2 ∪ signal_pixels_of outs)
  ⇒
  spec {(0,0)} ({(0,1);(0,-1);(1,0);(-1,0)} DIFF (xy_of ins UNION (xy_of outs)))
    s1 ins s2 outs
Proof
  strip_tac
  \\ irule imp_spec_00_lemma \\ simp []
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC [MATCH_MP grid_to_set_bool_grid
                        (UNDISCH bounds_core_pixels_of) |> DISCH_ALL] \\ fs []
QED

Theorem imp_spec_00 =
  (imp_spec_00_lemma2
   |> REWRITE_RULE [bool_grid_225_225_core]
   |> Q.GENL [‘ins’,‘outs’]);

val _ = export_theory();
