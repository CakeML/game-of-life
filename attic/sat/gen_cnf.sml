
type clause = int list;

val clauses = ref ([]: clause list);

fun clear_clauses () = (clauses := []);

fun write_cnf filename = let
  val cs = !clauses
  (* TODO: check that distinct non-null numbers for each clause,
           cannot contain i and -i in one clause *)
  (* check for bad var name 0 and compute max var name *)
  fun max_list m [] = m
    | max_list m (x::xs) = if x = 0 then failwith "zero used as var name" else
                             let val k = if x < 0 then 0-x else x in
                               if m < k then k else m
                             end
  fun max_list_list m [] = m
    | max_list_list m (xs::xss) = max_list_list (max_list m xs) xss
  val max_var_name = max_list_list 1 cs
  val clause_count = length cs
  (* turn clause to string *)
  fun clause_to_str [] = ["0\n"]
    | clause_to_str (c::cs) =
        (if c < 0 then "-" ^ int_to_string (0-c) ^ " "
                  else       int_to_string c     ^ " ") :: clause_to_str cs
  (* generate SAT solver file *)
  val f = TextIO.openOut filename
  val header = "p cnf "^(int_to_string max_var_name)^" "^(int_to_string clause_count) ^ "\n"
  val _ = TextIO.output(f,header)
  val _ = app (curry TextIO.output f o concat o clause_to_str) cs
  val _ = TextIO.closeOut f
  in () end

fun emit_clause vs = (clauses := vs::(!clauses)(*; print "." *));

fun emit_assert v = emit_clause [v];

fun print_imp vs v = () (* let
  fun ints_to_str [] = ""
    | ints_to_str [i] = int_to_string i
    | ints_to_str (i::is) = int_to_string i ^ " ∧ " ^ ints_to_str is
  in print (ints_to_str vs ^ " ==> " ^ int_to_string v ^ "\n") end *)

fun emit_imp conjs v =
  (print_imp conjs v; emit_clause (v :: map (fn i => ~i) conjs));

fun emit_iff v w = (emit_imp [v] w; emit_imp [w] v);

fun cross [] xs = []
  | cross (y::ys) xs = map (fn x => (y,x)) xs :: cross ys xs

val sum = foldr (fn (x,y) => x+y) 0

local
  val xs = [0,1]
  val ys = xs
  val ys = flatten (cross xs ys)
  val ys = flatten (cross xs ys)
  val ys = flatten (cross xs ys)
  val ys = flatten (cross xs ys)
  val ys = flatten (cross xs ys)
  val ys = flatten (cross xs ys)
  val ys = flatten (cross xs ys)
  val zs = map (fn (x1,(x2,(x3,(x4,(x5,(x6,(x7,x8))))))) => [x1,x2,x3,x4,x5,x6,x7,x8]) ys
  (* sample inputs *)
  val new_middle = 55
  val var_names = [1,2,3,4,5,6,7,8,9]
in
  fun emit_gol_rules_for var_names new_middle = let
    val _ = length var_names = 9 orelse failwith "bad input emit_rules_for"
    val _ = app (fn i => (print (int_to_string i); print " ")) var_names
    val _ = print "\n"
    val old_middle = el 5 var_names
    val var_names2 = List.take (var_names,4) @ List.drop (var_names,5)
    (* any cell with four or more neighbours will cause dead cell *)
    val will_die = filter (fn xs => sum xs = 4) zs
                   |> map (zip var_names2)
                   |> map (filter (fn (x,y) => y <> 0))
                   |> map (map fst)
    val _ = app (fn vs => emit_imp vs (~new_middle)) will_die
    (* any cell with less than two neighbours will die *)
    val will_die2 = filter (fn xs => sum xs = 1) zs
                    |> map (zip var_names2)
                    |> map (filter (fn (x,y) => y <> 1))
                    |> map (map (fn (x,y) => ~x))
    val _ = app (fn vs => emit_imp vs (~new_middle)) will_die2
    (* exactly three live *)
    val three_on = filter (fn xs => sum xs = 3) zs
                        |> map (zip var_names2)
                        |> map (map (fn (x,y) => if y = 0 then ~x else x))
    val _ = app (fn vs => emit_imp vs new_middle) three_on
    (* exactly two live *)
    val two_on = filter (fn xs => sum xs = 2) zs
                        |> map (zip var_names2)
                        |> map (map (fn (x,y) => if y = 0 then ~x else x))
    val _ = app (fn vs => emit_imp (old_middle::vs) new_middle) two_on
    val _ = app (fn vs => emit_imp ((~old_middle)::vs) (~new_middle)) two_on
  in () end
end

(*
val frame_count = 3
val width = 3
val height = 3
*)

fun make_gol_frames frame_count width height = let
  val gens = List.tabulate (frame_count, fn i => i)
  val xs = List.tabulate (width, fn i => i)
  val ys = List.tabulate (height, fn i => i)
  val frame = cross ys xs |> map (map (fn (x,y) => (y,x)))
  val vars = let
    val r = ref 1
    fun next _ = let val v = !r in (r := (!r)+1; v) end
    in map (fn _ => map (map next) frame) gens end
  fun get_var_name (g,x,y) = el (x+1) (el (y+1) (el (g+1) vars))
  fun for_each_cell f =
    app (fn g => app (fn y => app (fn x => f (g,x,y)) xs) ys) gens
  fun for_each_border_cell f =
    for_each_cell (fn (g,x,y) =>
      if (x = 0 orelse x = width-1) orelse
         (y = 0 orelse y = height-1) then f (g,x,y) else ())
  fun for_each_nonborder_cell f =
    for_each_cell (fn (g,x,y) =>
      if (x = 0 orelse x = width-1) orelse
         (y = 0 orelse y = height-1) then () else f (g,x,y))
  fun for_each_edge_cell f =
    for_each_cell (fn (g,x,y) =>
      if ((x = 1 orelse x = width-2) andalso (y >= 1 andalso y <= height-2)) orelse
         ((y = 1 orelse y = height-2) andalso (x >= 1 andalso x <= width-2))
             then f (g,x,y) else ())
  (* border and edge cells must stay dead *)
  val _ = for_each_border_cell (fn (g,x,y) => emit_assert (~ (get_var_name (g, x, y))))
  val _ = for_each_edge_cell (fn (g,x,y) => emit_assert (~ (get_var_name (g, x, y))))
  (* all nonborder cells up until last gen must respect rules *)
  val _ = for_each_nonborder_cell (fn (g,x,y) =>
    if frame_count-1 <= g then () else
      emit_gol_rules_for
        (map get_var_name [(g,x-1,y-1),(g,x,y-1),(g,x+1,y-1),
                           (g,x-1,y  ),(g,x,y  ),(g,x+1,y  ),
                           (g,x-1,y+1),(g,x,y+1),(g,x+1,y+1)])
        (get_var_name (g+1, x, y)))
  in (vars,get_var_name) end;

fun print_bool_frame bool_frame = let
  val xs = map (fn bs =>
             implode (map (fn t => if t then #"o" else #"b") bs) ^ "$\n") bool_frame
  in print (concat (["\n\nx = 0, y = 0, rule = B3/S23\n"] @ xs @ ["!\n\n"])) end

datatype res = Unsat | Sat of (int list);


fun run_sat input_file = let
  val output_filename = "output.txt"
  val _ = OS.Process.system ("lingeling < " ^ input_file ^ " 2>&1 > " ^ output_filename)
  fun read_all f x =
    case f x of NONE => [] | SOME y => y :: read_all f x
  val f = TextIO.openIn output_filename
  val xs = read_all TextIO.inputLine f
  val _ = TextIO.closeIn f
  val chars = explode " \t\n v"
  val is_unsat = null (filter (String.isPrefix "s SATISFIABLE") xs)
  val assignments = filter (String.isPrefix "v ") xs
       |> map (String.tokens (fn c => mem c chars))
       |> flatten |> map string_to_int
  in if is_unsat then Unsat else Sat assignments end


val test = let
  val _ = clear_clauses ()
  val frame_count = 3
  val width = 9
  val height = 9
  val (vars,get_var_name) = make_gol_frames frame_count width height
  val _ = emit_assert (get_var_name (0,3,3))
  val _ = emit_assert (get_var_name (0,4,4))
  val _ = emit_assert (get_var_name (0,5,5))
  val _ = emit_assert (get_var_name (2,4,4))
  val input_file = "test.cnf"
  val _ = write_cnf input_file
  val Sat s = run_sat input_file
  val bool_frames = map (map (map (fn v => mem v s))) vars
  val _ = app print_bool_frame bool_frames
  in () end
