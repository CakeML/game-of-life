structure gol_simLib :> gol_simLib =
struct
open HolKernel

datatype bexp = False
              | True
              | Var of string * int
              | Not of bexp
              | And of bexp * bexp
              | Or of bexp * bexp;

type bexp_env =
  { name : string, generation : int, value: bool };

type bvar =
  { name : string, generation : int };

type bexp8 =
  { y1: bexp, y2: bexp, y3: bexp, y4: bexp,
    y5: bexp, y6: bexp, y7: bexp, y8: bexp };

fun eval_bexp False (env: bexp_env list) = false
  | eval_bexp True env = true
  | eval_bexp (Not x) env = not (eval_bexp x env)
  | eval_bexp (And (x,y)) env = eval_bexp x env andalso eval_bexp y env
  | eval_bexp (Or (x,y)) env = eval_bexp x env orelse eval_bexp y env
  | eval_bexp (Var (s,g)) env =
      #value (first (fn {name=s1,generation=g1,...} =>
                        s = s1 andalso g = g1) env);

fun bvar_lt ({name=n1,generation=g1}:bvar)
            ({name=n2,generation=g2}:bvar) =
  n1 < n2 orelse (n1 = n2 andalso g1 < g2);

fun add_to_sorted [] (v:bvar) = [v]
  | add_to_sorted (x::xs) v =
      if bvar_lt x v then x :: add_to_sorted xs v else
      if x = v then x::xs else v :: x :: xs;

fun get_bvars x acc =
  case x of
    False => acc
  | True => acc
  | Not(x) => get_bvars x acc
  | Or(x,y) => get_bvars x (get_bvars y acc)
  | And(x,y) => get_bvars x (get_bvars y acc)
  | Var(s,g) => add_to_sorted acc {name=s,generation=g};

fun build_Not x =
  case x of
    True => False
  | False => True
  | Not(y) => y
  | _ => Not(x);

fun build_If x y z =
  if y = z then y else
  if y = True andalso z = False then x else
  if y = False andalso z = True then build_Not x else
  if z = False then And(x,y) else
  if y = True then Or(x,z) else
  if z = True then Or(y,build_Not x) else
  if y = False then And(z,build_Not x) else
    Or(And(x,y),And(build_Not(x),z));

fun get_bvars8 ({ y1,y2,y3,y4,y5,y6,y7,y8 }:bexp8) =
  (get_bvars y1 o get_bvars y2 o get_bvars y3 o get_bvars y4 o
   get_bvars y5 o get_bvars y6 o get_bvars y7 o get_bvars y8) [];

fun int_of_bool true = 1 | int_of_bool _ = 0;

fun eval_bexp8 ({ y1,y2,y3,y4,y5,y6,y7,y8 }:bexp8) env =
  int_of_bool (eval_bexp y1 env) +
  int_of_bool (eval_bexp y2 env) +
  int_of_bool (eval_bexp y3 env) +
  int_of_bool (eval_bexp y4 env) +
  int_of_bool (eval_bexp y5 env) +
  int_of_bool (eval_bexp y6 env) +
  int_of_bool (eval_bexp y7 env) +
  int_of_bool (eval_bexp y8 env) ;

fun count_falses x ({ y1,y2,y3,y4,y5,y6,y7,y8 }:bexp8) =
  int_of_bool (x  = False) +
  int_of_bool (y1 = False) +
  int_of_bool (y2 = False) +
  int_of_bool (y3 = False) +
  int_of_bool (y4 = False) +
  int_of_bool (y5 = False) +
  int_of_bool (y6 = False) +
  int_of_bool (y7 = False) +
  int_of_bool (y8 = False) ;

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
          end;

fun gol_cell x ys =
  if count_falses x ys >= 7 then False else
    let
      val vars = get_bvars x (get_bvars8 ys)
    in
      gol_eval vars [] x ys
    end;

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
  end;

fun toX x = x+75+10;
fun toY y = y+75+10;

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
  in () end;

fun for_loop i m f = if i < m then (f i; for_loop (i+1) m f) else ();

fun get_cell row col grid =
  Array.sub(Array.sub(grid,row),col) handle Subscript => False;

fun update_cell row col grid new_v =
  Array.update(Array.sub(grid,row),col,new_v);

fun new_grid cols rows =
  Array.tabulate (rows, fn row => Array.tabulate (cols, fn col => False))

datatype dir = N | S | W | E;

type io_port = (int * int) * dir;

fun snapshot gen_count ins outs grid =
  let
    val (cols,rows) = get_width_height grid
    val min_a = ref (~1);
    val min_b = ref (~1);
    fun smart_min var_ref n =
      (var_ref := (if !var_ref < 0 then n else Int.min(n, !var_ref)))
    fun min_var (Not(x)) = min_var x
      | min_var (And(x,y)) = (min_var x ; min_var y)
      | min_var (Or(x,y)) = (min_var x ; min_var y)
      | min_var (Var(s,g)) = (if s = "a" then smart_min min_a g else
                              if s = "b" then smart_min min_b g else ())
      | min_var _ = ()
    val _ = for_loop 0 rows (fn row =>
      for_loop 0 cols (fn col =>
        min_var (get_cell row col grid)))
    val gen_count = gen_count - !min_b
    val a = !min_a
    val b = !min_b
    fun sub_var (Not(x)) = Not(sub_var x)
      | sub_var (And(x,y)) = And(sub_var x, sub_var y)
      | sub_var (Or(x,y)) = Or(sub_var x, sub_var y)
      | sub_var (Var(s,g)) = (if s = "a" then Var(s,g-a) else
                              if s = "b" then Var(s,g-b) else Var(s,g))
      | sub_var x = x
    val grid =
      Vector.tabulate (rows, fn row =>
        Vector.tabulate (cols, fn col =>
          sub_var (get_cell row col grid)))
    fun mk_in 0 = Var ("a", gen_count + 1 - !min_a)
      | mk_in 1 = Var ("b", gen_count + 1 - !min_b)
      | mk_in _ = raise Fail "too many"
    val ins = mapi (fn i => fn d => (d, mk_in i)) ins
  in
    (ins, grid)
  end

fun read_file filename =
  let
    val f = TextIO.openIn(filename)
    val res = TextIO.inputAll(f)
    val _ = TextIO.closeIn(f)
  in
    res
  end;

(* --- state --- *)

(* val step_count = ref 0;
val gen_count = ref 0;
val inputs = ref ([] : io_port list);
val outputs = ref ([] : io_port list);
val the_grid = ref (new_grid 10 10);
val the_next_grid = ref (new_grid 10 10);
val block_height = ref 1;
val block_width = ref 1; *)

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
    val varnames = ["a","b","c"]
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
     val _ = if !step_count <> 59 then [] else
               let
                 val _ = List.app (fn (((x,y),dir),r) =>
                           if dir = E orelse dir = W then
                             r := delete_box (75*x-6) (75*y-6) 12 12 next_grid
                           else ()) outputs
               in
                 if ignore_input then [] else
                   mapi (fn i => fn ((x,y),dir) =>
                           if dir = E then
                             init_from_rle "$5bo2bo$9bo$5bo3bo$6b4o!"
                               (toY(75*y-5)) (toX(75*x-5))
                               (Var (List.nth(varnames,i), !gen_count)) next_grid
                           else if dir = W then
                             init_from_rle "5$4o$o3bo$o$bo2bo!"
                               (toY(75*y-5)) (toX(75*x-5))
                               (Var (List.nth(varnames,i), !gen_count)) next_grid
                           else ()) inputs
               end
     val _ = if !step_count <> 29 then [] else
               let
                 val _ = List.app (fn (((x,y),dir),r) =>
                           if dir = N orelse dir = S then
                             r := delete_box (75*x-6) (75*y-6) 12 12 next_grid
                           else ()) outputs
               in
                 if ignore_input then [] else
                   mapi (fn i => fn ((x,y),dir) =>
                           if dir = N then
                             init_from_rle "2b3o$bo2bo$4bo$4bo$bobo!"
                               (toY(75*y-5)) (toX(75*x-5))
                               (Var (List.nth(varnames,i), !gen_count)) next_grid
                           else if dir = S then
                             init_from_rle "5$6bobo$5bo$5bo$5bo2bo$5b3o!"
                               (toY(75*y-5)) (toX(75*x-5))
                               (Var (List.nth(varnames,i), !gen_count)) next_grid
                           else ()) inputs
               end
    val _ = (step_count := ((!step_count) + 1) mod 60)
    val _ = (if !step_count = 0 then (gen_count := (!gen_count) + 1) else ())
  in
    (the_grid := next_grid; the_next_grid := grid)
  end;

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
    val (ins, res) = loop 1 prev
    val _ = print " done\n"
  in
    {inputs = ins, outputs = map (fn (d, r) => (d, !r)) outputs, grid = res}
  end

type gate = {
  filename : string,
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
  grid: bexp array array
}

fun prepare ({inputs, outputs, height, width, grid}: loaded_gate) =
  STATE {
    step_count = ref 0,
    gen_count = ref 0,
    height = height,
    width = width,
    inputs = inputs,
    outputs = map (fn d => (d, ref False)) outputs,
    the_grid = ref grid,
    the_next_grid = ref (new_grid (width * 150 + 20) (height * 150 + 20))
  }

fun load ({filename, inputs, outputs, height, width}: gate): loaded_gate = let
  val grid = new_grid (width * 150 + 20) (height * 150 + 20)
  val _ = init_from_rle (read_file ("gates/" ^ filename)) 10 10 True grid
  in
    { height = height,
      width = width,
      inputs = inputs,
      outputs = outputs,
      grid = grid }
  end

fun rotate_dir E = S
  | rotate_dir S = W
  | rotate_dir W = N
  | rotate_dir N = E;

fun rotate
  ({grid = original_grid,
    inputs, outputs, width, height}: loaded_gate): loaded_gate = let
  val (cols,rows) = get_width_height original_grid
  val grid = new_grid rows cols
  val _ = for_loop 0 cols (fn i =>
    for_loop 0 rows (fn j =>
      update_cell i j grid (get_cell ((rows-1)-j) i original_grid)))
  val inputs = map (fn ((x,y),d) => ((2*(height-1)-y,x),rotate_dir d)) inputs
  val outputs = map (fn ((x,y),d) => ((2*(height-1)-y,x),rotate_dir d)) outputs
  val st = prepare {
    inputs = inputs,
    outputs = outputs,
    width = height,
    height = width,
    grid = grid
  }
  val _ = for_loop 0 30 (fn i => compute_next_state st true)
  val _ = C List.app outputs (fn ((x,y),d) =>
    ignore $ delete_box (75*x-6) (75*y-6) 12 12 grid)
  in
    { grid = (fn STATE {the_grid, ...} => !the_grid) st,
      inputs = inputs,
      outputs = outputs,
      width = height,
      height = width }
  end

val and_en_e =
  { filename = "and-en-e.rle" ,
    inputs   = [((~1,0),E),((0,1),N)] ,
    outputs  = [((1,0),E)] ,
    height   = 1 ,
    width    = 1 } : gate;

val and_es_e =
  { filename = "and-es-e.rle" ,
    inputs   = [((~1,0),E),((0,~1),S)] ,
    outputs  = [((1,0),E)] ,
    height   = 1 ,
    width    = 1 } : gate;

val and_ew_n =
  { filename = "and-ew-n.rle" ,
    inputs   = [((1,0),W),((~1,0),E)] ,
    outputs  = [((0,~1),N)] ,
    height   = 1 ,
    width    = 1 } : gate;

val or_en_e =
  { filename = "or-en-e.rle" ,
    inputs   = [((~1,0),E),((0,1),N)] ,
    outputs  = [((1,0),E)] ,
    height   = 1 ,
    width    = 1 } : gate;

val not_e_e =
  { filename = "not-e-e.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((1,0),E)] ,
    height   = 1 ,
    width    = 1 } : gate;

val half_adder_ee_es =
  { filename = "half-adder-ee-es.rle" ,
    inputs   = [((~1,0),E),((~1,2),E)] ,
    outputs  = [((3,0),E),((2,3),S)] ,
    height   = 2 ,
    width    = 2 } : gate;

val half_adder_ee_ee =
  { filename = "half-adder-ee-ee.rle" ,
    inputs   = [((~1,0),E),((~1,2),E)] ,
    outputs  = [((3,0),E),((3,2),E)] ,
    height   = 2 ,
    width    = 2 } : gate;

val turn_e_s =
  { filename = "turn-e-s.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((0,1),S)] ,
    height   = 1 ,
    width    = 1 } : gate;

val turn_e_n =
  { filename = "turn-e-n.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((0,~1),N)] ,
    height   = 1 ,
    width    = 1 } : gate;

val fork_e_es =
  { filename = "fork-e-es.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((1,0),E),((0,1),S)] ,
    height   = 1 ,
    width    = 1 } : gate;

val fork_e_en =
  { filename = "fork-e-en.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((1,0),E),((0,~1),N)] ,
    height   = 1 ,
    width    = 1 } : gate;

val wire_e_e =
  { filename = "empty.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((1,0),E)] ,
    height   = 1 ,
    width    = 1 } : gate;

val cross_es_es =
  { filename = "empty.rle" ,
    inputs   = [((~1,0),E),((0,~1),S)] ,
    outputs  = [((1,0),E),((0,1),S)] ,
    height   = 1 ,
    width    = 1 } : gate;

val cross_en_en =
  { filename = "empty.rle" ,
    inputs   = [((~1,0),E),((0,1),N)] ,
    outputs  = [((1,0),E),((0,~1),N)] ,
    height   = 1 ,
    width    = 1 } : gate;

val slow_wire_e_e =
  { filename = "slow-wire-e-e.rle" ,
    inputs   = [((~1,0),E)] ,
    outputs  = [((7,0),E)] ,
    height   = 1 ,
    width    = 4 } : gate;

end
