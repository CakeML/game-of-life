(*
  Definition of spec for writing specifications for GOL gates
*)
open preamble gol_rulesTheory gol_composeTheory integerTheory;

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

Definition core_pixels_of_def:
  core_pixels_of area ins outs (x,y) ⇔
    let (ib,i,jb,j) = pixel_xy x y in
      if int_even ib ∧ int_even jb then
        (ib,jb) ∈ area
      else if ~int_even ib ∧ ~int_even jb then
        decide_corner area ib i jb j
      else
        interface_pixel ins Receiver (x,y) ∨
        interface_pixel outs Sender (x,y)
End

Definition spec_def:
  spec (area :(int # int) set) (borders:(int # int) set)
       (s1:(int # int) set) (ins:intrefaces)
       (s2:(int # int) set) (outs:intrefaces) ⇔
    area_ok area borders ins outs ∧
    steps60 (s1 ∪ comm_pixels_of ins)
            (core_pixels_of area ins outs ∪ signal_pixels_of ins)
            (core_pixels_of area ins outs)
            (core_pixels_of area ins outs ∪ signal_pixels_of outs)
            (s2 ∪ comm_pixels_of outs)
End

val _ = export_theory();
