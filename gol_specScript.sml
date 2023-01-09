(*
  Definition of spec for writing specifications for GOL gates
*)
open preamble gol_rulesTheory integerTheory gol_simulationTheory;

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
  signal_pixels_of [] = ∅ ∧
  signal_pixels_of (((x,y),(cs,b))::(xs:intrefaces)) =
    (signal_pixels_of xs ∪
     to_state (from_frame (75 * x) (75 * y)
       (MAP (MAP (λc. if c = Signal then SOME b else NONE)) cs)))
End

(* taking 60 steps inside boundaries for borders *)

Definition steps_def:
  steps n x s1 s2 ⇔
    FUNPOW step n s1 = s2 ∧
    ∀k. k < n ⇒ infl (FUNPOW step k s1) ⊆ x
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

Theorem steps_sim_frame_ok:
  ∀n xs ys. steps_sim w h policy n xs ys ⇒ frame_ok (w,h) ys
Proof
  Induct \\ rw []
  \\ pop_assum mp_tac
  >- (once_rewrite_tac [steps_sim_cases] \\ fs [])
  \\ simp [Once steps_sim_cases,ADD1]
  \\ rw [] \\ res_tac
  \\ drule_all frame_ok_next_sim
  \\ fs []
QED

Theorem steps_sim_FUNPOW_step:
  ∀n xs ys.
    steps_sim w h policy n xs ys ⇒
    FUNPOW step n (to_state (from_frame x y xs)) = to_state (from_frame x y ys)
Proof
  Induct \\ rw []
  \\ pop_assum mp_tac
  >- (once_rewrite_tac [steps_sim_cases] \\ fs [])
  \\ once_rewrite_tac [steps_sim_cases] \\ fs [GSYM ADD1]
  \\ rw [] \\ res_tac
  \\ fs [FUNPOW_SUC]
  \\ irule step_from_frame
  \\ fs []
  \\ imp_res_tac steps_sim_frame_ok
  \\ first_assum $ irule_at Any \\ fs []
QED

Theorem steps_sim_suc:
  ∀n w h policy xs zs.
    steps_sim w h policy (SUC n) xs zs ⇔
    ∃ys.
      frame_ok (w,h) xs ∧ frame_borders_none xs ∧ policy 0 xs ∧
      next_sim xs ys ∧ steps_sim w h (policy o SUC) n ys zs
Proof
  Induct
  >-
   (rw [] \\ once_rewrite_tac [steps_sim_cases] \\ fs [GSYM ADD1]
    \\ once_rewrite_tac [steps_sim_cases] \\ fs [GSYM ADD1]
    \\ rw [] \\ eq_tac \\ rw [] \\ imp_res_tac frame_ok_next_sim \\ fs [])
  \\ simp_tac std_ss [Once steps_sim_cases,GSYM ADD1,PULL_EXISTS]
  \\ pop_assum $ simp o single o Once
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  >- (simp [Once steps_sim_cases,GSYM ADD1,PULL_EXISTS] \\ metis_tac [])
  \\ fs [PULL_EXISTS]
  \\ pop_assum mp_tac
  \\ simp [Once steps_sim_cases,GSYM ADD1,PULL_EXISTS]
  \\ rw [] \\ metis_tac []
QED

Theorem steps_sim_imp_0:
  ∀n xs ys.
    steps_sim w h policy n xs ys ⇒
    steps_sim w h policy 0 xs xs
Proof
  Induct \\ rw []
  \\ pop_assum mp_tac
  >- (once_rewrite_tac [steps_sim_cases] \\ fs [])
  \\ simp [Once steps_sim_cases,ADD1]
  \\ rw [] \\ res_tac
QED

Theorem steps_sim_add:
  ∀m n xs ys policy.
    steps_sim w h policy (m + n) xs ys ⇒
    ∃zs.
      steps_sim w h policy m xs zs ∧
      steps_sim w h (λk. policy (k + m)) n zs ys
Proof
  Induct \\ fs [SF ETA_ss]
  >-
   (rw [] \\ first_assum (irule_at Any)
    \\ imp_res_tac steps_sim_imp_0 \\ fs [])
  \\ fs [] \\ rewrite_tac []
  \\ simp [GSYM ADD1,ADD_CLAUSES,PULL_EXISTS]
  \\ rpt strip_tac
  \\ simp [Once steps_sim_suc]
  \\ pop_assum mp_tac
  \\ simp [Once steps_sim_suc]
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ fs [combinTheory.o_DEF,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem steps_sim_bound:
  ∀n xs ys policy.
    steps_sim w h policy n xs ys ⇔
    steps_sim w h (λk. if k < n then policy k else ARB) n xs ys
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct \\ fs []
  \\ once_rewrite_tac [steps_sim_cases] \\ fs []
  \\ fs [GSYM ADD1,PULL_EXISTS]
  \\ pop_assum $ once_rewrite_tac o single o GSYM
  \\ fs []
QED

Definition check_mask_row_def:
  check_mask_row
    (b11::b12::b13::bs1)
    (b21::b22::b23::bs2)
    (b31::b32::b33::bs3) (r::rs) =
    (if (IS_SOME r ⇒ b11 ∧ b12 ∧ b13 ∧ b21 ∧ b22 ∧ b23 ∧ b31 ∧ b32 ∧ b33)
     then
       check_mask_row
        (b12::b13::bs1)
        (b22::b23::bs2)
        (b32::b33::bs3) rs
     else F) ∧
  check_mask_row _ _ _ _ = T
End

Definition check_mask_rows_def:
  check_mask_rows (x1::x2::x3::xs) (n::ns) =
    (check_mask_row x1 x2 x3 (TL n) ∧
     check_mask_rows (x2::x3::xs) ns) ∧
  check_mask_rows _ _ = T
End

Definition check_mask_def:
  check_mask xs [] = T ∧
  check_mask xs (r::rs) = check_mask_rows xs rs
End

Triviality to_state_nones_append:
  ∀ns x y. EVERY IS_NONE ns ⇒ to_state (from_row x y ns ++ xs) = to_state xs
Proof
  Induct \\ fs [from_row_def]
QED

Theorem to_state_append:
  ∀xs ys. to_state (xs ++ ys) = to_state xs ∪ to_state ys
Proof
  fs [to_state_def,EXTENSION]
QED

Theorem to_state_cons:
  to_state (((x,y),b)::xs) = (if b then {(x,y)} else {}) ∪ to_state xs
Proof
  fs [to_state_def,EXTENSION,FORALL_PROD] \\ rw [] \\ fs []
QED

Theorem grid_to_set_rw0:
  grid_to_set x y (z::ys) =
  grid_to_set x y [z] ∪ grid_to_set x (y+1) ys
Proof
  rw [grid_to_set_def,EXTENSION,FORALL_PROD]
  \\ fs [IN_DEF,grid_to_set_def,oEL_def,AllCaseEqs()]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ ‘Num (p_2 − (y + 1)) = Num (p_2 − y) − 1’ by intLib.COOPER_TAC \\ gvs []
  >- intLib.COOPER_TAC
  >- intLib.COOPER_TAC
  \\ Cases_on ‘Num (p_2 − y)’ \\ gvs []
  \\ ‘F’ by intLib.COOPER_TAC
QED

Theorem grid_to_set_rw1:
  grid_to_set x y (z::q::ys) =
  grid_to_set x y [z] ∪ grid_to_set x (y+1) (q::ys)
Proof
  simp [Once grid_to_set_rw0]
QED

Theorem grid_to_set_rw2:
  grid_to_set x y [a::xs] =
  (if a then {(x,y)} else {}) ∪ grid_to_set (x+1) y [xs]
Proof
  rw [grid_to_set_def,EXTENSION,FORALL_PROD]
  \\ fs [IN_DEF,grid_to_set_def,oEL_def,AllCaseEqs()]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  >- (CCONTR_TAC \\ fs [] \\ intLib.COOPER_TAC)
  >- (‘Num (p_1 − x) − 1 = Num (p_1 − (x + 1))’ by intLib.COOPER_TAC
      \\ fs [] \\ intLib.COOPER_TAC)
  >- intLib.COOPER_TAC
  >- (Cases_on ‘Num (p_1 − x)’ \\ fs []
      \\ ‘Num (p_1 − x) − 1 = Num (p_1 − (x + 1))’ by intLib.COOPER_TAC
      \\ gvs [])
  >- intLib.COOPER_TAC
  >- (‘Num (p_1 − x) − 1 = Num (p_1 − (x + 1))’ by intLib.COOPER_TAC \\ fs [])
  >- intLib.COOPER_TAC
  >- intLib.COOPER_TAC
  >- (‘Num (p_1 − x) − 1 = Num (p_1 − (x + 1))’ by intLib.COOPER_TAC \\ fs [])
QED

Triviality grid_to_set_add1:
  grid_to_set (x + 1) y [b::c::xs1; e::f::xs2; h::i::xs3] ⊆
  grid_to_set x y [a::b::c::xs1; d::e::f::xs2; g::h::i::xs3]
Proof
  rewrite_tac [grid_to_set_rw1]
  \\ CONV_TAC (RAND_CONV $ ONCE_REWRITE_CONV [grid_to_set_rw2])
  \\ rw [] \\ fs [SUBSET_DEF] \\ rw [] \\ fs []
QED

Triviality check_mask_row_thm:
  ∀n ts x y a.
    check_mask_row (GENLIST (λi. mask1 (x + &i,y)) n)
                   (GENLIST (λi. mask1 (x + &i,y + 1)) n)
                   (GENLIST (λi. mask1 (x + &i,y + 2)) n) ts ∧
    SUC (LENGTH ts) = n ∧
    LAST (a::ts) = NONE ⇒
    infl (to_state (from_row (x + 1) (y + 1) ts)) ⊆
    grid_to_set x y
          (GENLIST (λi. mask1 (x + &i,y)) n::
           GENLIST (λi. mask1 (x + &i,y + 1)) n::
           GENLIST (λi. mask1 (x + &i,y + 2)) n::[])
Proof
  simp [] \\ Induct_on ‘ts’ \\ fs []
  >- fs [from_row_def,to_state_def,infl_thm,SUBSET_DEF,FORALL_PROD]
  \\ Cases_on ‘ts’ \\ fs []
  >- fs [from_row_def,to_state_def,infl_thm,SUBSET_DEF,FORALL_PROD]
  \\ fs [GENLIST_CONS,combinTheory.o_DEF,ADD1]
  \\ fs [check_mask_row_def]
  \\ rw []
  \\ last_x_assum $ qspecl_then [‘x+1’,‘y’] mp_tac
  \\ impl_tac >-
   (fs [GSYM INT_ADD_ASSOC]
    \\ ‘∀a. y + (1 + &(a + 2)) = y + &(a + 3)’ by intLib.COOPER_TAC \\ fs [])
  \\ fs [GSYM INT_ADD_ASSOC]
  \\ ‘∀a. y + (1 + &(a + 2)) = y + &(a + 3)’ by intLib.COOPER_TAC \\ fs []
  \\ strip_tac
  \\ rename [‘from_row (x + 1) (y + 1) (hx::h::t)’]
  \\ Cases_on ‘hx’ \\ fs [from_row_def]
  \\ fs [GSYM INT_ADD_ASSOC]
  >-
   (irule SUBSET_TRANS
    \\ first_x_assum $ irule_at Any
    \\ irule grid_to_set_add1)
  \\ gvs []
  \\ rewrite_tac [to_state_cons,infl_union] \\ fs []
  \\ reverse conj_tac
  >-
   (irule SUBSET_TRANS
    \\ first_x_assum $ irule_at Any
    \\ irule grid_to_set_add1)
  \\ simp [SUBSET_DEF,FORALL_PROD,infl_thm]
  \\ IF_CASES_TAC \\ fs []
  \\ rw [] \\ fs []
  \\ gvs [grid_to_set_def,IN_DEF,integerTheory.INT_EQ_SUB_RADD]
  \\ ‘∀y. y + 1 + 1 − y = 2:int’ by intLib.COOPER_TAC \\ gvs []
  \\ fs [oEL_def]
  \\ intLib.COOPER_TAC
QED

Theorem check_mask_thm:
  frame_ok (w,h) xs1 ∧
  frame_borders_none xs1 ∧
  check_mask (bool_grid x y w h mask1) xs1 ⇒
  infl (to_state (from_frame x y xs1)) ⊆
  grid_to_set x y (bool_grid x y w h mask1)
Proof
  Cases_on ‘xs1’
  \\ fs [frame_ok_def,frame_borders_none_def] \\ rw []
  \\ fs [from_frame_def,to_state_nones_append,GSYM ADD1,check_mask_def]
  \\ qsuff_tac
    ‘∀ts (hs:(bool option) list) x y h mask1.
        check_mask_rows (bool_grid x y (LENGTH hs) (SUC (LENGTH ts)) mask1) ts ∧
        EVERY (λx. LENGTH x = LENGTH hs) ts ∧
        EVERY IS_NONE (LAST (h::ts)) ∧
        EVERY (IS_NONE ∘ HD) ts ∧
        EVERY (IS_NONE ∘ LAST) ts ⇒
        infl (to_state (from_frame x (y + 1) ts)) ⊆
        grid_to_set x y (bool_grid x y (LENGTH hs) (SUC (LENGTH ts)) mask1)’
  >- (disch_then drule_all \\ fs [])
  \\ rpt $ pop_assum kall_tac
  \\ Induct
  >- fs [from_frame_def,to_state_def,infl_def,SUBSET_DEF,infl_thm,FORALL_PROD]
  \\ fs []
  \\ Cases_on ‘ts’ \\ fs [from_frame_def]
  \\ fs [to_state_nones_append |> Q.INST [‘xs’|->‘[]’] |> SIMP_RULE std_ss [APPEND_NIL]]
  >- fs [from_frame_def,to_state_def,infl_def,SUBSET_DEF,infl_thm,FORALL_PROD]
  \\ fs [bool_grid_def,GENLIST_CONS]
  \\ fs [check_mask_rows_def,combinTheory.o_DEF,ADD1]
  \\ rpt gen_tac \\ strip_tac
  \\ last_x_assum $ qspecl_then [‘hs’,‘x’,‘y+1’,‘mask1’] mp_tac
  \\ impl_tac >-
   (fs [GSYM INT_ADD_ASSOC]
    \\ ‘∀a. y + (1 + &(a + 2)) = y + &(a + 3)’ by intLib.COOPER_TAC \\ fs [])
  \\ strip_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ simp [Once to_state_append,infl_union]
  \\ reverse conj_tac
  >-
   (irule SUBSET_TRANS
    \\ first_x_assum $ irule_at Any
    \\ fs [GSYM INT_ADD_ASSOC]
    \\ ‘∀a. y + (1 + &(a + 2)) = y + &(a + 3)’ by intLib.COOPER_TAC \\ fs []
    \\ CONV_TAC (RAND_CONV $ ONCE_REWRITE_CONV [grid_to_set_rw1])
    \\ simp [SUBSET_DEF])
  \\ Cases_on ‘h'’ \\ fs []
  >- fs [from_frame_def,to_state_def,infl_def,SUBSET_DEF,infl_thm,FORALL_PROD,from_row_def]
  \\ gvs [from_row_def]
  \\ irule SUBSET_TRANS
  \\ irule_at Any check_mask_row_thm
  \\ first_x_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
  \\ once_rewrite_tac [grid_to_set_rw0]
  \\ once_rewrite_tac [grid_to_set_rw0]
  \\ once_rewrite_tac [grid_to_set_rw0]
  \\ once_rewrite_tac [grid_to_set_rw0]
  \\ once_rewrite_tac [grid_to_set_rw0]
  \\ fs [SUBSET_DEF]
QED

Theorem steps_suc:
  steps (SUC n) x s1 s2 ⇔
  infl s1 ⊆ x ∧ steps n x (step s1) s2
Proof
  fs [steps_def,FUNPOW]
  \\ rw [] \\ eq_tac \\ rw []
  >- (pop_assum $ qspec_then ‘0’ mp_tac \\ fs [])
  >- (first_x_assum $ qspec_then ‘SUC k’ mp_tac \\ fs [FUNPOW])
  \\ Cases_on ‘k’ \\ fs []
  \\ fs [FUNPOW]
QED

Theorem steps_sim_check_mask:
  ∀n xs1 xs2.
    steps_sim w h (λk. check_mask (bool_grid x y w h mask1)) n xs1 xs2 ⇒
    steps n (grid_to_set x y (bool_grid x y w h mask1))
      (to_state (from_frame x y xs1)) (to_state (from_frame x y xs2))
Proof
  Induct
  >- (fs [steps_def] \\ simp [Once steps_sim_cases])
  \\ simp [steps_sim_suc] \\ rw []
  \\ fs [combinTheory.o_DEF]
  \\ simp [steps_suc]
  \\ drule_all step_from_frame
  \\ strip_tac \\ fs []
  \\ irule check_mask_thm \\ fs []
QED

Theorem steps_sim_steps60:
  steps_sim w h policy 60 xs ys ⇒
  policy = (λk. if k < 20 then check_mask (bool_grid x y w h mask1) else
                if k < 40 then check_mask (bool_grid x y w h mask2) else
                               check_mask (bool_grid x y w h mask3)) ⇒
  steps60
    (to_state (from_frame x y xs))
    (grid_to_set x y (bool_grid x y w h mask1))
    (grid_to_set x y (bool_grid x y w h mask2))
    (grid_to_set x y (bool_grid x y w h mask3))
    (to_state (from_frame x y ys))
Proof
  fs [steps60_def]
  \\ rewrite_tac [GSYM (EVAL “20+20+20:num”)]
  \\ strip_tac
  \\ dxrule steps_sim_add \\ strip_tac
  \\ dxrule steps_sim_add \\ strip_tac
  \\ fs [] \\ rpt $ pop_assum mp_tac
  \\ rename [‘steps_sim w h policy 20 xs1 xs2’,
             ‘steps_sim w h (λk. policy (k + 20)) 20 xs2 xs3’,
             ‘steps_sim w h (λk. policy (k + 40)) 20 xs3 xs4’]
  \\ rw []
  \\ qexists_tac ‘to_state (from_frame x y xs2)’
  \\ qexists_tac ‘to_state (from_frame x y xs3)’
  \\ rpt $ pop_assum mp_tac \\ fs []
  \\ once_rewrite_tac [steps_sim_bound] \\ fs []
  \\ simp [GSYM steps_sim_bound]
  \\ rw [] \\ irule steps_sim_check_mask \\ fs []
QED

Theorem imp_spec_00_lemma3:
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  EVERY (λ(p,r). MEM p [(0,1);(0,-1);(1,0);(-1,0)]) (ins ++ outs) ∧
  steps_sim 225 225
    (λk. if k < 20 then check_mask
           (bool_grid (-75) (-75) 225 225 (core_pixels_of {(0,0)} ins outs ins)) else
         if k < 40 then check_mask
           (bool_grid (-75) (-75) 225 225 (core_pixels_of {(0,0)} ins outs [])) else
         check_mask
           (bool_grid (-75) (-75) 225 225 (core_pixels_of {(0,0)} ins outs outs)))
    60 xs ys ∧
  to_state (from_frame (-75) (-75) xs) =
  to_state (from_frame (-75) (-75) xs1) ∪ signal_pixels_of ins ∧
  to_state (from_frame (-75) (-75) ys) =
  to_state (from_frame (-75) (-75) ys1) ∪ signal_pixels_of outs
  ⇒
  spec {(0,0)} ({(0,1);(0,-1);(1,0);(-1,0)} DIFF (xy_of ins UNION (xy_of outs)))
    (to_state (from_frame (-75) (-75) xs1)) ins
    (to_state (from_frame (-75) (-75) ys1)) outs
Proof
  strip_tac
  \\ irule imp_spec_00_lemma2
  \\ asm_rewrite_tac []
  \\ pop_assum $ mp_tac o GSYM
  \\ pop_assum $ mp_tac o GSYM
  \\ rpt strip_tac \\ asm_rewrite_tac []
  \\ irule steps_sim_steps60 \\ fs []
QED

Theorem imp_spec_00 =
  (imp_spec_00_lemma3
   |> REWRITE_RULE [bool_grid_225_225_core]
   |> Q.GENL [‘ins’,‘outs’,‘xs’,‘ys’,‘xs1’,‘ys1’]);

val _ = export_theory();
