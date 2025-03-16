structure gol_simLib :> gol_simLib =
struct
open HolKernel bossLib boolLib Parse

datatype bexp = False
              | True
              | Var of int * int
              | Not of bexp
              | And of bexp * bexp
              | Or of bexp * bexp

type bexp_env =
  { name : int, generation : int, value: bool }

type bvar =
  { name : int, generation : int }

type bexp8 =
  { y1: bexp, y2: bexp, y3: bexp, y4: bexp,
    y5: bexp, y6: bexp, y7: bexp, y8: bexp }

fun eval_bexp False (env: bexp_env list) = false
  | eval_bexp True env = true
  | eval_bexp (Not x) env = not (eval_bexp x env)
  | eval_bexp (And (x,y)) env = eval_bexp x env andalso eval_bexp y env
  | eval_bexp (Or (x,y)) env = eval_bexp x env orelse eval_bexp y env
  | eval_bexp (Var (s,g)) env =
      #value (first (fn {name=s1,generation=g1,...} =>
                        s = s1 andalso g = g1) env)

fun bvar_lt ({name=n1,generation=g1}:bvar)
            ({name=n2,generation=g2}:bvar) =
  n1 < n2 orelse (n1 = n2 andalso g1 < g2)

fun add_to_sorted [] (v:bvar) = [v]
  | add_to_sorted (x::xs) v =
      if bvar_lt x v then x :: add_to_sorted xs v else
      if x = v then x::xs else v :: x :: xs

fun get_bvars x acc =
  case x of
    False => acc
  | True => acc
  | Not(x) => get_bvars x acc
  | Or(x,y) => get_bvars x (get_bvars y acc)
  | And(x,y) => get_bvars x (get_bvars y acc)
  | Var(s,g) => add_to_sorted acc {name=s,generation=g}

fun build_Not x =
  case x of
    True => False
  | False => True
  | Not(y) => y
  | _ => Not(x)

fun build_If x y z =
  if y = z then y else
  if y = True andalso z = False then x else
  if y = False andalso z = True then build_Not x else
  if z = False then And(x,y) else
  if y = True then Or(x,z) else
  if z = True then Or(y,build_Not x) else
  if y = False then And(z,build_Not x) else
    Or(And(x,y),And(build_Not(x),z))

fun get_bvars8 ({ y1,y2,y3,y4,y5,y6,y7,y8 }:bexp8) =
  (get_bvars y1 o get_bvars y2 o get_bvars y3 o get_bvars y4 o
   get_bvars y5 o get_bvars y6 o get_bvars y7 o get_bvars y8) []

fun int_of_bool true = 1 | int_of_bool _ = 0

fun eval_bexp8 ({ y1,y2,y3,y4,y5,y6,y7,y8 }:bexp8) env =
  int_of_bool (eval_bexp y1 env) +
  int_of_bool (eval_bexp y2 env) +
  int_of_bool (eval_bexp y3 env) +
  int_of_bool (eval_bexp y4 env) +
  int_of_bool (eval_bexp y5 env) +
  int_of_bool (eval_bexp y6 env) +
  int_of_bool (eval_bexp y7 env) +
  int_of_bool (eval_bexp y8 env)

fun count_falses x ({ y1,y2,y3,y4,y5,y6,y7,y8 }:bexp8) =
  int_of_bool (x  = False) +
  int_of_bool (y1 = False) +
  int_of_bool (y2 = False) +
  int_of_bool (y3 = False) +
  int_of_bool (y4 = False) +
  int_of_bool (y5 = False) +
  int_of_bool (y6 = False) +
  int_of_bool (y7 = False) +
  int_of_bool (y8 = False)

fun gol_eval (vars : bvar list) env x ys =
  case vars of
    ({ name=n, generation=g }::vs) =>
      build_If (Var (n,g))
        (gol_eval vs ({ name=n, generation=g, value=true }::env) x ys)
        (gol_eval vs ({ name=n, generation=g, value=false }::env) x ys)
  | [] => let
            val k = eval_bexp8 ys env
            val mid = eval_bexp x env
            fun to_bexp true = True
              | to_bexp false = False
          in
            to_bexp (if mid then (k = 2 orelse k = 3) else (k = 3))
          end

fun gol_cell x ys =
  if count_falses x ys >= 7 then False else
    let
      val vars = get_bvars x (get_bvars8 ys)
    in
      gol_eval vars [] x ys
    end

fun init_from_rle rle startRow startCol fill grid =
  let
    val count = ref 0
    val row = ref startRow
    val col = ref startCol
    fun do_n_times 0 f = ()
      | do_n_times n f = (f (); do_n_times (n-1) f)
    fun set_grid r c =
      let
        val a = Array.sub(grid,r)
      in
        Array.update(a,c,fill)
      end handle Subscript => ();
    fun loop [] = ()
      | loop (c::cs) =
          if #"0" <= c andalso c <= #"9" then
            (count := (!count) * 10 + (ord c - ord #"0"); loop cs)
          else if c = #"o" then
            (do_n_times (Int.max(1,!count))
               (fn _ => (set_grid (!row) (!col);
                         col := (!col)+1));
             count := 0; loop cs)
          else if c = #"b" then
            (col := (!col)+Int.max(1,!count);
             count := 0; loop cs)
          else if c = #"$" then
            (row := (!row)+Int.max(1,!count);
             col := startCol;
             count := 0; loop cs)
          else if c = #"\n" then loop cs
          else if c = #"!" then ()
          else failwith ("Unknown rle input: " ^ implode [c])
  in
    loop (explode rle)
  end

fun toX x = x+75+10
fun toY y = y+75+10

fun delete_box x y w h grid =
  let
    fun tab k n f = if k < n then (f k; tab (k+1) n f) else ()
    val search = ref False
    fun del_cell r c =
      let
        val a = Array.sub(grid,r)
      in
        case Array.sub(a,c) of
          False => ()
        | v => (search := v; Array.update(a,c,False))
      end handle Subscript => ();
  in
    tab 0 w (fn i =>
      tab 0 h (fn j =>
        del_cell (toY(y+j)) (toX(x+i))));
    !search
  end

fun get_width_height grid =
  (Array.length (Array.sub(grid,0)), Array.length grid);

fun grid_to_svg grid filename =
  let
    val cell_size = 6
    val grid_rows = Array.length grid
    val grid_cols = Array.length (Array.sub(grid,0))
    val f = TextIO.openOut filename
    fun every_col row_arr row_index col_index h =
      if col_index < Array.length row_arr then
        (h col_index row_index (Array.sub(row_arr,col_index));
         every_col row_arr row_index (col_index+1) h)
      else ()
    fun every_row row_index h =
      if row_index < Array.length grid then
        (every_col (Array.sub(grid,row_index)) row_index 0 h;
         every_row (row_index+1) h)
      else ();
    fun fold_grid h = every_row 0 h
    val _ = TextIO.output(f,String.concat [
      "<svg width=\"", Int.toString (cell_size * grid_cols),
        "\" height=\"", Int.toString (cell_size * grid_rows),
        "\" xmlns=\"http://www.w3.org/2000/svg\">\n"])
    fun output_cell col row cell =
      let
        val color = if cell = False then "black" else
                    if cell = True then "white" else "purple"
        val x = Int.toString (col * cell_size)
        val y = Int.toString (row * cell_size)
        val cell_size_str = Int.toString cell_size
      in
        TextIO.output(f,String.concat
          ["<rect x=\"", x,
           "\" y=\"", y,
           "\" width=\"", cell_size_str,
           "\" height=\"", cell_size_str,
           "\" fill=\"", color, "\" stroke=\"black\" stroke-width=\"1\" />\n"])
      end
    val _ = fold_grid output_cell
    val _ = TextIO.output(f,"</svg>\n")
    val _ = TextIO.closeOut(f)
  in () end

fun for_loop i m f = if i < m then (f i; for_loop (i+1) m f) else ()

fun get_cell row col grid =
  Array.sub(Array.sub(grid,row),col) handle Subscript => False

fun update_cell row col grid new_v =
  Array.update(Array.sub(grid,row),col,new_v)

fun new_grid cols rows =
  Array.tabulate (rows, fn row => Array.tabulate (cols, fn col => False))

datatype dir = N | S | W | E

val dirToXY = fn E => (1,0) | S => (0,1) | W => (~1,0) | N => (0,~1)
val dirToRot = fn E => 0 | S => 1 | W => 2 | N => 3
val rotate_dir = fn E => S | S => W | W => N | N => E

type io_port = (int * int) * dir * bexp

fun mk_min init = let
  val mins = Array.array (2, init)
  fun smart_min i n = let
    val v = Array.sub (mins, i)
    in Array.update (mins, i, if v < 0 then n else Int.min(n, v)) end
  fun min_var (Not(x)) = min_var x
    | min_var (And(x,y)) = (min_var x ; min_var y)
    | min_var (Or(x,y)) = (min_var x ; min_var y)
    | min_var (Var(s,g)) = smart_min s g
    | min_var _ = ()
  fun sub_var (Not(x)) = Not(sub_var x)
    | sub_var (And(x,y)) = And(sub_var x, sub_var y)
    | sub_var (Or(x,y)) = Or(sub_var x, sub_var y)
    | sub_var (Var(s,g)) = Var(s, g - Array.sub (mins, s))
    | sub_var x = x
  in (mins, min_var, sub_var) end

fun snapshot gen_count ins outs grid = let
  val (cols, rows) = get_width_height grid
  val (mins, min_var, sub_var) = mk_min gen_count
  val _ = for_loop 0 rows (fn row =>
    for_loop 0 cols (fn col =>
      min_var (get_cell row col grid)))
  val grid =
    Vector.tabulate (rows, fn row =>
      Vector.tabulate (cols, fn col =>
        sub_var (get_cell row col grid)))
  fun mk_in i = Var (i, gen_count - Array.sub(mins, i))
  val ins = mapi (fn i => fn (p, d, _) => (p, d, mk_in i)) ins
  val _ = Array.modify (fn i => i - 1) mins
  val outs = mapi (fn i => fn ((p, d, _), r) => (p, d, sub_var (!r))) outs
  in ((ins, outs), grid) end

fun read_file filename = let
  val f = TextIO.openIn(filename)
  val res = TextIO.inputAll(f)
  val _ = TextIO.closeIn(f)
  in res end

datatype state = STATE of {
  step_count: int ref,
  gen_count: int ref,
  inputs: io_port list,
  outputs: (io_port * bexp ref) list,
  height: int,
  width: int,
  the_grid: bexp array array ref,
  the_next_grid: bexp array array ref
}

fun compute_next_state
  (STATE {step_count, gen_count, inputs, outputs, the_grid, the_next_grid, ...})
  ignore_input =
  let
    val grid = !the_grid
    val next_grid = !the_next_grid
    val (cols,rows) = get_width_height grid
    val _ = for_loop 0 rows (fn row =>
      for_loop 0 cols (fn col =>
        update_cell row col next_grid
          (gol_cell (get_cell row col grid)
            { y1 = get_cell (row-1) (col-1) grid ,
              y2 = get_cell (row-1) (col  ) grid ,
              y3 = get_cell (row-1) (col+1) grid ,
              y4 = get_cell (row  ) (col-1) grid ,
              y5 = get_cell (row  ) (col+1) grid ,
              y6 = get_cell (row+1) (col-1) grid ,
              y7 = get_cell (row+1) (col  ) grid ,
              y8 = get_cell (row+1) (col+1) grid })))

     val _ = if !step_count <> 59 then () else (
        List.app (fn (((x,y),dir,_),r) =>
          if dir = E orelse dir = W then
            r := delete_box (75*x-6) (75*y-6) 12 12 next_grid
          else ()) outputs;
        if ignore_input then () else
          appi (fn i => fn ((x,y),dir,_) =>
            if dir = E then
              init_from_rle "$5bo2bo$9bo$5bo3bo$6b4o!"
                (toY(75*y-5)) (toX(75*x-5))
                (Var (i, !gen_count)) next_grid
            else if dir = W then
              init_from_rle "5$4o$o3bo$o$bo2bo!"
                (toY(75*y-5)) (toX(75*x-5))
                (Var (i, !gen_count)) next_grid
            else ()) inputs;
        gen_count := !gen_count + 1)

     val _ = if !step_count <> 29 then () else (
        List.app (fn (((x,y),dir,_),r) =>
          if dir = N orelse dir = S then
            r := delete_box (75*x-6) (75*y-6) 12 12 next_grid
          else ()) outputs;
          if ignore_input then () else
            appi (fn i => fn ((x,y),dir,_) =>
              if dir = N then
                init_from_rle "2b3o$bo2bo$4bo$4bo$bobo!"
                  (toY(75*y-5)) (toX(75*x-5))
                  (Var (i, !gen_count)) next_grid
              else if dir = S then
                init_from_rle "5$6bobo$5bo$5bo$5bo2bo$5b3o!"
                  (toY(75*y-5)) (toX(75*x-5))
                  (Var (i, !gen_count)) next_grid
              else ()) inputs)

    val _ = step_count := ((!step_count) + 1) mod 60
  in
    the_grid := next_grid; the_next_grid := grid
  end

fun run_to_fixpoint (st as STATE {gen_count, the_grid, inputs, outputs, ...}) =
  let
    val _ = print "Rounds:"
    val prev = Vector.fromList[Vector.fromList([]:bexp list)]
    fun loop n prev =
      let
        val _ = print (" " ^ Int.toString n)
        val _ = for_loop 0 60 (fn i => compute_next_state st false);
        val snap = snapshot (!gen_count) inputs outputs (!the_grid)
      in
        if prev = #2 snap then snap else loop (n+1) (#2 snap)
      end
    val ((ins, outs), res) = loop 1 prev
    val _ = if (inputs, map #1 outputs) = (ins, outs) then print " done\n" else
      (print "\nIO mismatch\n";
      PolyML.print (inputs, map #1 outputs);
      PolyML.print (ins, outs);
      ());
  in
    {inputs = ins, outputs = outs, grid = res}
  end

type gate = {
  filename : string,
  stems : string list,
  inputs : io_port list,
  outputs : io_port list,
  height : int,
  width : int
}

type loaded_gate = {
  inputs: io_port list,
  outputs: io_port list,
  height: int,
  width: int,
  grid: unit -> bexp array array
}

fun prepare ({inputs, outputs, height, width, grid}: loaded_gate) =
  STATE {
    step_count = ref 0,
    gen_count = ref 0,
    height = height,
    width = width,
    inputs = inputs,
    outputs = map (fn d => (d, ref False)) outputs,
    the_grid = ref (grid ()),
    the_next_grid = ref (new_grid (width * 150 + 20) (height * 150 + 20))
  }

fun load ({filename, inputs, outputs, height, width, ...}: gate): loaded_gate = {
  height = height,
  width = width,
  inputs = inputs,
  outputs = outputs,
  grid = fn () => let
    val grid = new_grid (width * 150 + 20) (height * 150 + 20)
    val _ = init_from_rle (read_file ("gates/" ^ filename)) 10 10 True grid
    in grid end
}

fun inc (Var (n, g)) = Var (n, g+1)
  | inc (And (x, y)) = And (inc x, inc y)
  | inc (Or (x, y))  = Or (inc x, inc y)
  | inc (Not x)   = Not (inc x)
  | inc True      = True
  | inc False     = False

fun is_ns ((_,d,_):io_port) = (d = N orelse d = S)
fun is_ew ((_,d,_):io_port) = (d = E orelse d = W)

fun rotate_180
  ({grid = original_grid,
    inputs, outputs, width, height}: loaded_gate): loaded_gate = let
  fun flip ((x,y),d,r) =
    ((2*(width-1)-x, 2*(height-1)-y),rotate_dir (rotate_dir d), r)
  val inputs = map flip inputs
  val outputs = map flip outputs
  fun grid () = let
    val original_grid = original_grid ()
    val (cols, rows) = (width * 150 + 20, height * 150 + 20)
    val grid = new_grid cols rows
    val _ = for_loop 0 rows (fn i =>
      for_loop 0 cols (fn j =>
        update_cell i j grid
          (get_cell ((rows-1)-i) ((cols-1)-j) original_grid)))
    in grid end
  in
    { grid = grid,
      inputs = inputs,
      outputs = outputs,
      width = width,
      height = height }
  end

fun rotate_90
  ({grid = original_grid,
    inputs, outputs, width, height}: loaded_gate): loaded_gate = let
  val (mins, min_var, sub_var) = mk_min ~1
  fun rotport (port as ((x,y),d,r)) = let
    val r = if is_ns port then inc r else r
    val _ = min_var r
    in ((2*(height-1)-y,x),rotate_dir d, r) end
  val inputs = map rotport inputs
  val outputs = map rotport outputs
  val inputs = map (fn (p, d, r) => (p, d, sub_var r)) inputs
  val outputs = map (fn (p, d, r) => (p, d, sub_var r)) outputs
  fun grid () = let
    val original_grid = original_grid ()
    val (cols, rows) = (width * 150 + 20, height * 150 + 20)
    val grid = new_grid rows cols
    val _ = for_loop 0 cols (fn i =>
      for_loop 0 rows (fn j =>
        update_cell i j grid (get_cell ((rows-1)-j) i original_grid)))
    val st as STATE {the_grid, ...} = prepare {
      inputs = inputs,
      outputs = outputs,
      width = height,
      height = width,
      grid = K grid
    }
    val _ = for_loop 0 30 (fn i => compute_next_state st true)
    val _ = C List.app outputs (fn ((x,y),d,_) =>
      ignore $ delete_box (75*x-6) (75*y-6) 12 12 (!the_grid))
    in !the_grid end
  in
    { grid = grid,
      inputs = inputs,
      outputs = outputs,
      width = height,
      height = width }
  end

fun rotate 0 gate = gate
  | rotate 1 gate = rotate_90 gate
  | rotate n gate = rotate (n - 2) (rotate_180 gate)

fun fun_to_svg (rows, cols, g) filename =
  let
    val cell_size = 6
    val f = TextIO.openOut filename
    fun every_col row_index col_index h =
      if col_index < cols then
        (h col_index row_index (g row_index col_index);
         every_col row_index (col_index+1) h)
      else ()
    fun every_row row_index h =
      if row_index < rows then
        (every_col row_index 0 h;
         every_row (row_index+1) h)
      else ();
    fun fold_grid h = every_row 0 h
    val _ = TextIO.output(f,String.concat [
      "<svg width=\"", Int.toString (cell_size * cols),
        "\" height=\"", Int.toString (cell_size * rows),
        "\" xmlns=\"http://www.w3.org/2000/svg\">\n",
        "<rect x=\"0\" y=\"0",
        "\" width=\"", Int.toString (cell_size * cols),
        "\" height=\"", Int.toString (cell_size * rows),
        "\" fill=\"black\" />\n"])
    fun fmla cell = case cell of
        False => "\226\138\165"
      | True => "\226\138\164"
      | And(a, b) => "("^fmla a^" \226\136\167 "^fmla b^")"
      | Or(a, b) => "("^fmla a^" \226\136\168 "^fmla b^")"
      | Not(a) => "\194\172"^fmla a
      | Var(0, i) => "a"^Int.toString i
      | Var(1, i) => "b"^Int.toString i
      | Var _ => "*"
    fun output_cell _ _ False = ()
      | output_cell col row cell =
      let
        val color = case cell of
          True => "white"
        | Var (0, _) => "red"
        | Var (1, _) => "blue"
        | _ => "purple"
        val x = Int.toString (col * cell_size)
        val y = Int.toString (row * cell_size)
        val cell_size_str = Int.toString cell_size
      in
        TextIO.output(f,String.concat
          ["<rect x=\"", x,
           "\" y=\"", y,
           "\" width=\"", cell_size_str,
           "\" height=\"", cell_size_str,
           "\" fill=\"", color,
           "\" stroke=\"black\" stroke-width=\"1\"><title>", fmla cell,
           "</title></rect>\n"])
      end handle Match => ()
    val _ = fold_grid output_cell
    val _ = TextIO.output(f,"</svg>\n")
    val _ = TextIO.closeOut(f)
  in () end

fun array_to_svg grid =
  fun_to_svg (Array.length grid, Array.length (Array.sub(grid,0)),
    fn i => fn j => Array.sub(Array.sub(grid,i),j))

fun vector_to_svg grid =
  fun_to_svg (Vector.length grid, Vector.length (Vector.sub(grid,0)),
    fn i => fn j => Vector.sub(Vector.sub(grid,i),j))

fun make_abbrev name tm =
  let
    val v = mk_var(name,type_of tm)
    val th = new_definition(name^"_def",mk_eq(v,tm))
  in SYM th end

val gates = []

val terminator_e =
  { filename = "terminator-e.rle",
    stems    = ["terminator_e", "terminator_s", "terminator_w", "terminator_n"],
    inputs   = [((~1, 0), E, Var (0, 1))],
    outputs  = [],
    height   = 1,
    width    = 1 } : gate
val gates = terminator_e :: gates

val wire_e_e =
  { filename = "empty.rle",
    stems    = ["wire_e_e", "wire_s_s", "wire_w_w", "wire_n_n"],
    inputs   = [((~1, 0), E, Var (0, 5))],
    outputs  = [((1, 0), E, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = wire_e_e :: gates

val cross_es_es =
  { filename = "empty.rle",
    stems    = ["cross_es_es", "cross_sw_sw", "cross_wn_wn", "cross_ne_ne"],
    inputs   = [((~1, 0), E, Var (0, 5)), ((0, ~1), S, Var (1, 5))],
    outputs  = [((1, 0), E, Var (0, 0)), ((0, 1), S, Var (1, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = cross_es_es :: gates

val and_en_e =
  { filename = "and-en-e.rle",
    stems    = ["and_en_e", "and_se_s", "and_ws_w", "and_nw_n"],
    inputs   = [((~1, 0), E, Var (0, 5)), ((0, 1), N, Var (1, 5))],
    outputs  = [((1, 0), E, And (Var (0, 0), Var (1, 0)))],
    height   = 1,
    width    = 1 } : gate
val gates = and_en_e :: gates

val and_es_e =
  { filename = "and-es-e.rle",
    stems    = ["and_es_e", "and_sw_s", "and_wn_w", "and_ne_n"],
    inputs   = [((~1, 0), E, Var (0, 5)), ((0, ~1), S, Var (1, 5))],
    outputs  = [((1, 0), E, And (Var (0, 0), Var (1, 0)))],
    height   = 1,
    width    = 1 } : gate
val gates = and_es_e :: gates

val and_ew_n =
  { filename = "and-ew-n.rle",
    stems    = ["and_ew_n", "and_sn_e", "and_we_s", "and_ns_w"],
    inputs   = [((1, 0), W, Var (0, 6)), ((~1, 0), E, Var (1, 9))],
    outputs  = [((0, ~1), N, And (Var (0, 0), Var (1, 0)))],
    height   = 1,
    width    = 1 } : gate
val gates = and_ew_n :: gates

val or_en_e =
  { filename = "or-en-e.rle",
    stems    = ["or_en_e", "or_se_s", "or_ws_w", "or_nw_n"],
    inputs   = [((~1, 0), E, Var (0, 7)), ((0, 1), N, Var (1, 5))],
    outputs  = [((1, 0), E, Or (Var (0, 0), Var (1, 0)))],
    height   = 1,
    width    = 1 } : gate
val gates = or_en_e :: gates

val not_e_e =
  { filename = "not-e-e.rle",
    stems    = ["not_e_e", "not_s_s", "not_w_w", "not_n_n"],
    inputs   = [((~1, 0), E, Var (0, 8))],
    outputs  = [((1, 0), E, Not (Var (0, 1)))],
    height   = 1,
    width    = 1 } : gate
val gates = not_e_e :: gates

val turn_e_s =
  { filename = "turn-e-s.rle",
    stems    = ["turn_e_s", "turn_s_w", "turn_w_n", "turn_n_e"],
    inputs   = [((~1, 0), E, Var (0, 7))],
    outputs  = [((0, 1), S, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = turn_e_s :: gates

val fast_turn_e_s =
  { filename = "fast-turn-e-s.rle",
    stems    = ["fast_turn_e_s", "fast_turn_s_w", "fast_turn_w_n", "fast_turn_n_e"],
    inputs   = [((~1, 0), E, Var (0, 6))],
    outputs  = [((0, 1), S, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = fast_turn_e_s :: gates

val slow_turn_e_s =
  { filename = "slow-turn-e-s.rle",
    stems    = ["slow_turn_e_s", "slow_turn_s_w", "slow_turn_w_n", "slow_turn_n_e"],
    inputs   = [((~1, 0), E, Var (0, 8))],
    outputs  = [((0, 1), S, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = slow_turn_e_s :: gates

val turn_e_n =
  { filename = "turn-e-n.rle",
    stems    = ["turn_e_n", "turn_s_e", "turn_w_s", "turn_n_w"],
    inputs   = [((~1, 0), E, Var (0, 6))],
    outputs  = [((0, ~1), N, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = turn_e_n :: gates

val fork_e_es =
  { filename = "fork-e-es.rle",
    stems    = ["fork_e_es", "fork_s_sw", "fork_w_wn", "fork_n_ne"],
    inputs   = [((~1, 0), E, Var (0, 6))],
    outputs  = [((1, 0), E, Var (0, 1)), ((0, 1), S, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = fork_e_es :: gates

val fork_e_en =
  { filename = "fork-e-en.rle",
    stems    = ["fork_e_en", "fork_s_se", "fork_w_ws", "fork_n_nw"],
    inputs   = [((~1, 0), E, Var (0, 7))],
    outputs  = [((1, 0), E, Var (0, 2)), ((0, ~1), N, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = fork_e_en :: gates

val half_adder_ee_es =
  { filename = "half-adder-ee-es.rle",
    stems    = ["half_adder_ee_es", "half_adder_ss_sw", "half_adder_ww_wn", "half_adder_nn_ne"],
    inputs   = [((~1, 0), E, Var (0, 19)), ((~1, 2), E, Var (1, 18))],
    outputs  = [
      ((3, 0), E, Or (
        And (Var (0, 4), Or (
          And (Var (0, 7), Not (Var (1, 0))),
          And (Not (Var (0, 7)), And (Var (1, 3), Not (Var (1, 0)))))),
        And (Not (Var (0, 4)), Or (Var (0, 7), Var (1, 3))))),
      ((2, 3), S, And (Var (0, 0), Var (1, 1)))],
    height   = 2,
    width    = 2 } : gate
val gates = half_adder_ee_es :: gates

val half_adder_ee_ee =
  { filename = "half-adder-ee-ee.rle",
    stems    = ["half_adder_ee_ee", "half_adder_ss_ss", "half_adder_ww_ww", "half_adder_nn_nn"],
    inputs   = [((~1, 0), E, Var (0, 17)), ((~1, 2), E, Var (1, 18))],
    outputs  = [
      ((3, 0), E, Or (
        And (Var (0, 2), Or (
          And (Var (0, 5), Not (Var (1, 0))),
          And (Not (Var (0, 5)), And (Var (1, 3), Not (Var (1, 0)))))),
        And (Not (Var (0, 2)), Or (Var (0, 5), Var (1, 3))))),
      ((3, 2), E, And (Var (0, 0), Var (1, 3)))],
    height   = 2,
    width    = 2 } : gate
val gates = half_adder_ee_ee :: gates

val slow_wire_e_e =
  { filename = "slow-wire-e-e.rle",
    stems    = ["slow_wire_e_e", "slow_wire_s_s", "slow_wire_w_w", "slow_wire_n_n"],
    inputs   = [((~1, 0), E, Var (0, 9))],
    outputs  = [((1, 0), E, Var (0, 0))],
    height   = 1,
    width    = 1 } : gate
val gates = slow_wire_e_e :: gates

val slower_wire_e_e =
  { filename = "slower-wire-e-e.rle",
    stems    = ["slower_wire_e_e", "slower_wire_s_s", "slower_wire_w_w", "slower_wire_n_n"],
    inputs   = [((~1, 0), E, Var (0, 155))],
    outputs  = [((7, 0), E, Var (0, 0))],
    height   = 1,
    width    = 4 } : gate
val gates = slower_wire_e_e :: gates

val gates = rev gates

end
