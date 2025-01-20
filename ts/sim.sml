
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
            (count := (!count) * 10 + (ord c - ord #"0"))
          else if c = #"o" then
            (do_n_times (Int.max(1,!count))
               (fn _ => (set_grid (!row) (!col);
                         col := (!col)+1));
             count := 0)
          else if c = #"b" then
            (col := (!col)+Int.max(1,!count);
             count := 0)
          else if c = #"$" then
            (row := (!row)+Int.max(1,!count);
             col := startCol;
             count := 0)
          else failwith ("Unknown rle input: " ^ implode [c])
  in
    loop (explode rle)
  end;

fun toX x = x+75+10;
fun toY y = y+75+10;

fun deleteBox x y w h grid =
  let
    fun tab k n f = if k < n then (f k; tab (k+1) n f) else ()
    fun del_cell r c =
      let
        val a = Array.sub(grid,r)
      in
        Array.update(a,c,False)
      end handle Subscript => ();
  in
    tab 0 w (fn i =>
      tab 0 h (fn j =>
        del_cell (toY(y+j)) (toX(x+i))))
  end










.
