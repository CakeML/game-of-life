local open HolKernel gol_simLib in
structure gol_sim_naiveLib = struct

fun check_mask1 [] [] = true
  | check_mask1 (a::xs) [] = false
  | check_mask1 [] (b::bs) = false
  | check_mask1 (a::xs) (b::bs) = (b orelse a = False) andalso check_mask1 xs bs

fun check_mask [] [] = true
  | check_mask (a::xs) [] = false
  | check_mask [] (b::bs) = false
  | check_mask (a::xs) (b::bs) = check_mask1 a b andalso check_mask xs bs

fun b2n true = 1
  | b2n false = 0

fun ALOOKUP [] a = NONE
  | ALOOKUP ((x,y)::xs) a = if a = x then SOME y else ALOOKUP xs a

fun eval_bexp env True      = true
  | eval_bexp env False     = false
  | eval_bexp env (Not x)   = not (eval_bexp env x)
  | eval_bexp env (And (x, y)) = (eval_bexp env x andalso eval_bexp env y)
  | eval_bexp env (Or (x, y))  = (eval_bexp env x orelse eval_bexp env y)
  | eval_bexp env (Var (v, n)) = case ALOOKUP env (v,n) of SOME b => b | NONE => false

fun eval_bexp8 env (y1,y2,y3,y4,y5,y6,y7,y8) =
  b2n (eval_bexp env y1) +
  b2n (eval_bexp env y2) +
  b2n (eval_bexp env y3) +
  b2n (eval_bexp env y4) +
  b2n (eval_bexp env y5) +
  b2n (eval_bexp env y6) +
  b2n (eval_bexp env y7) +
  b2n (eval_bexp env y8)

fun count_falses x (y1,y2,y3,y4,y5,y6,y7,y8) =
  b2n (x  = False) +
  b2n (y1 = False) +
  b2n (y2 = False) +
  b2n (y3 = False) +
  b2n (y4 = False) +
  b2n (y5 = False) +
  b2n (y6 = False) +
  b2n (y7 = False) +
  b2n (y8 = False)

fun bvar_lt (n1,g1) (n2,g2) =
  if n1 = n2 then g1 < g2 else n1 = 0

fun add_to_sorted [] v = [v]
  | add_to_sorted (x::xs) v =
  if bvar_lt x v then x :: add_to_sorted xs v else
  if x = v then x :: xs else v :: x :: xs

fun get_bvars False acc = acc
  | get_bvars True acc = acc
  | get_bvars (Not x) acc = get_bvars x acc
  | get_bvars (Or (x, y)) acc = get_bvars x (get_bvars y acc)
  | get_bvars (And (x, y)) acc = get_bvars x (get_bvars y acc)
  | get_bvars (Var (n, g)) acc = add_to_sorted acc (n,g)

fun get_bvars8 (y1,y2,y3,y4,y5,y6,y7,y8) =
  (get_bvars y1 $ get_bvars y2 $ get_bvars y3 $ get_bvars y4 $
    get_bvars y5 $ get_bvars y6 $ get_bvars y7 $ get_bvars y8 [])

fun build_Not x =
  case x of
    True => False
  | False => True
  | Not y => y
  | _ => Not x

fun build_If x y z =
  if y = z then y else
  if y = True andalso z = False then x else
  if y = False andalso z = True then build_Not x else
  if z = False then And (x, y) else
  if y = True then Or (x, z) else
  if z = True then Or (y, build_Not x) else
  if y = False then And (z, build_Not x) else
    Or (And (x, y), And (build_Not x, z))

fun to_bexp true = True
  | to_bexp false = False

(* val stat = ref (Array.fromList ([]:int list)) *)
fun gol_eval vars env x ys =
  case vars of
    ((n,g)::vs) =>
      build_If (Var (n, g))
        (gol_eval vs (((n,g),true)::env) x ys)
        (gol_eval vs (((n,g),false)::env) x ys)
  | [] => let
      val k = eval_bexp8 env ys
      val mid = eval_bexp env x
      in to_bexp (if mid then (k = 2 orelse k = 3) else (k = 3)) end

val count = ref Time.zeroTime
fun gol_cell x ys =
  if count_falses x ys >= 7 then False else let
    val vars = get_bvars x (get_bvars8 ys)
    (* val timer = Timer.startCPUTimer ()
    val _ = if length vars > 15 then
      (PolyML.print vars; ())
    else ()
    val _ = Array.update (!stat, length vars, Array.sub (!stat, length vars) + 1) *)
    val res = gol_eval vars [] x ys
    (* val {usr, ...} = Timer.checkCPUTimer timer *)
    (* val _ = count := !count + usr *)
    in res end

fun hd_or_false [] = False
  | hd_or_false (x::xs) = x

fun gol_row x0 (x1::xs)
        y0 (y1::ys)
        z0 (z1::zs) =
  gol_cell y1 (x0, x1, hd_or_false xs,
                y0,     hd_or_false ys,
                z0, z1, hd_or_false zs) ::
  gol_row x1 xs
          y1 ys
          z1 zs
  | gol_row _ _ _ _ _ _ = []

fun REPLICATE n v = List.tabulate (n, fn _ => v)

fun gol_rows prev (row :: rest) =
  gol_row False prev
          False row
          False (case rest of
                    [] => REPLICATE (length row) False
                  | r :: _ => r)
  :: gol_rows row rest
  | gol_rows prev [] = []

fun gol_step_rows [] = []
  | gol_step_rows (x::xs) = let
    (* val _ = (count := Time.zeroTime; stat := Array.array (30, 0)) *)
    val res = gol_rows (REPLICATE (length x) False) (x::xs)
    (* val _ = say ("gol_step_rows: " ^ time_to_string (!count) ^ "\n")
    val _ = PolyML.print (!stat) *)
    in res end

fun gol_checked_steps 0 rows mask = SOME rows
  | gol_checked_steps n rows mask =
    if n = 0 then SOME rows else (
      (* print "start\n"; *)
      if check_mask rows mask then let
        (* val _ = print "checked\n" *)
        val rows' = time gol_step_rows rows
        (* val _ = print "step\n" *)
        in gol_checked_steps (n - 1) rows' mask end
      else NONE)

fun or xss yss =
  map2 (fn xs => fn ys => map2 (fn x => fn y => x orelse y) xs ys) xss yss

fun add_margin fill n xss = let
  val ys = REPLICATE n fill
  val yss = map (fn xs => ys @ xs @ ys) xss
  val l = (case yss of (row::_) => length row | _ => n+n)
  val ts = REPLICATE n (REPLICATE l fill)
  in ts @ yss @ ts end

fun make_base_area w h = let
  val trues = REPLICATE (h * 150) (REPLICATE (w * 150) true)
  in add_margin false 10 trues end

fun or_box_row x w [] = []
  | or_box_row x w (r::rs) =
  if x = 0 then if w = 0 then r :: rs else true :: or_box_row x (w-1) rs
  else r :: or_box_row (x-1) w rs

fun or_box x y w h [] = []
  | or_box x y w h (r::rs) =
  if y = 0 then
    if h = 0 then r :: rs else
      or_box_row x w r :: or_box x y w (h-1) rs
  else
    r :: or_box x (y-1) w h rs

fun or_io_areas [] t = t
  | or_io_areas (((x,y),_,_)::rest) t =
  or_box (85 + 75 * x - 6) (85 + 75 * y - 6) 12 12
    (or_io_areas rest t)

fun diff (xss : bool list list) (yss : bool list list) =
  map2 (fn xs => fn ys => map2 (fn x => fn y => if y then false else x) xs ys) xss yss

fun masks w h ins outs = let
  val base_area_bools = make_base_area w h
  val bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) false)
  val sets1 = or_io_areas (filter is_ns ins @ filter is_ew outs) bools
  val sets2 = or_io_areas (filter is_ew ins @ filter is_ns outs) bools
  in
    (or sets2 (diff base_area_bools sets1),
      or sets1 (diff base_area_bools sets2))
  end

fun shrink_row (x1::x2::x3::xs)
              (y1::y2::y3::ys)
              (z1::z2::z3::zs) =
      (x1 andalso x2 andalso x3 andalso
        y1 andalso y2 andalso y3 andalso
        z1 andalso z2 andalso z3) :: shrink_row (x2::x3::xs) (y2::y3::ys) (z2::z3::zs)
  | shrink_row _ _ _ = []

fun shrink_all (r1::r2::r3::rest) =
    shrink_row r1 r2 r3 :: shrink_all (r2::r3::rest)
  | shrink_all _ = []

fun shrink xs = add_margin false 1 (shrink_all xs)

fun fromVector v = Vector.foldr (fn (a, r) => a :: r) [] v

fun simulation_test1 w h (ins:io_port list) (outs:io_port list) rows n = let
  val rows = map fromVector (fromVector rows)
  val (m1,m2) = masks w h ins outs
  val res = Option.valOf $ gol_checked_steps n rows (shrink m1)
  in Vector.fromList (map Vector.fromList res) end

fun diff_rows (rows : bexp list list) (bools: bool list list) =
  map2 (map2 (fn r => fn b => if b then False else r)) rows bools

fun inter_rows (rows : bexp list list) (bools: bool list list) =
  map2 (map2 (fn r => fn b => if b then r else False)) rows bools

fun build_Or x y =
  if x = True then True else
  if y = True then True else
  if x = False then y else
  if y = False then x else
    Or (x, y)

fun or_row x p [] = []
  | or_row x [] row = row
  | or_row x (p::pat) (r::row) =
      if x = 0 then build_Or p r :: or_row x pat row else
        r :: or_row (x-1) (p::pat) row

fun or_at x y pat [] = []
  | or_at x y [] (row::rows) = row::rows
  | or_at x y (p::pat) (row::rows) =
    if y = 0 then or_row x p row :: or_at x y pat rows else
      row :: or_at x (y-1) (p::pat) rows

fun io_gate E = [
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,true ,false,false,true ,false],
    [false,false,false,false,false,false,false,false,false,true ],
    [false,false,false,false,false,true ,false,false,false,true ],
    [false,false,false,false,false,false,true ,true ,true ,true ],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false]]
  | io_gate W = [
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [true ,true ,true ,true ,false,false,false,false,false,false],
    [true ,false,false,false,true ,false,false,false,false,false],
    [true ,false,false,false,false,false,false,false,false,false],
    [false,true ,false,false,true ,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false]]
  | io_gate N = [
    [false,false,true ,true ,true ,false,false,false,false,false],
    [false,true ,false,false,true ,false,false,false,false,false],
    [false,false,false,false,true ,false,false,false,false,false],
    [false,false,false,false,true ,false,false,false,false,false],
    [false,true ,false,true ,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false]]
  | io_gate S = [
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,false,false,false,false],
    [false,false,false,false,false,false,true ,false,true ,false],
    [false,false,false,false,false,true ,false,false,false,false],
    [false,false,false,false,false,true ,false,false,false,false],
    [false,false,false,false,false,true ,false,false,true ,false],
    [false,false,false,false,false,true ,true ,true ,false,false]]

fun or_lwss rows [] = SOME rows
  | or_lwss rows (((x,y),d,v)::rest) =
  case or_lwss rows rest of
    NONE => NONE
  | SOME rows1 =>
      SOME (or_at (x * 75 - 5 + 85) (y * 75 - 5 + 85)
              (map (map (fn b => if b then v else False)) (io_gate d)) rows1)

fun inc_vars rows = map (map inc) rows

fun simulation_ok w h (ins:io_port list) (outs:io_port list) rows = let
  val bools = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) false)
  val (m1,m2) = masks w h ins outs
  val del1 = or_io_areas (filter is_ns outs) bools
  val del2 = or_io_areas (filter is_ew outs) bools
  val ins1 = filter is_ns ins
  val ins2 = filter is_ew ins
  val outs1 = filter is_ns outs
  val outs2 = filter is_ew outs
  val empty = REPLICATE (150 * h + 20) (REPLICATE (150 * w + 20) False)
  in
    case gol_checked_steps 30 rows (shrink m1) of
      NONE => false
    | SOME rows1 =>
      if or_lwss empty outs1 <> SOME (inter_rows rows1 del1) then false else
        case or_lwss (diff_rows rows1 del1) ins1 of
          NONE => false
        | SOME rowsA =>
          case gol_checked_steps 30 rowsA (shrink m2) of
            NONE => false
          | SOME rows2 =>
              if or_lwss empty outs2 <> SOME (inter_rows rows2 del2) then false else
                case or_lwss (diff_rows rows2 del2) ins2 of
                  NONE => false
                | SOME rowsB =>
                    inc_vars rows = rowsB
  end

end
end
