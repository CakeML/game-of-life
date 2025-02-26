structure gol_diagramLib :> gol_diagramLib =
struct
open HolKernel gol_simLib

type diag = string * string vector

val CSIZE = 21
val SIZE = CSIZE * 2 + 1

fun parse [QUOTE s]: diag = let
    val lines = String.fields (fn x => x = #"\n") s
    val (header, lines) = case lines of _::a::b => (a,b) | _ => raise Bind
    val lines = Vector.fromList (List.take (lines, length lines - 2))
    in (header, lines) end
  | parse _ = raise Bind

datatype small_gate = Node | SlowNode | AndG | OrG | NotG
datatype large_gate = HalfAddG | SlowWire

datatype sigil =
    Empty
  | Wire of dir
  | Wall of bool
  | Small of small_gate
  | Large of large_gate

fun coord ((_, lines):diag) (x, y) =
  case String.substring (Vector.sub (lines, y), 3 + 2 * x, 2) of
    "  " => Empty
  | "> " => Wire E
  | "v " => Wire S
  | "< " => Wire W
  | "^ " => Wire N
  | "| " => Wall true
  | "- " => Wall false
  | "o " => Small Node
  | "s " => Small SlowNode
  | "A " => Small AndG
  | "O " => Small OrG
  | "N " => Small NotG
  | "H " => Large HalfAddG
  | "S " => Large SlowWire
  | s => raise Fail s

fun sigil_to_string s = case s of
    Empty => "  "
  | Wire E => "> "
  | Wire S => "v "
  | Wire W => "< "
  | Wire N => "^ "
  | Wall true => "| "
  | Wall false => "- "
  | Small Node => "o "
  | Small SlowNode => "s "
  | Small AndG => "A "
  | Small OrG => "O "
  | Small NotG => "N "
  | Large HalfAddG => "H "
  | Large SlowWire => "S "

fun lineHeader line =
  (String.substring (line, 0, 3), String.extract (line, 3 + 2 * SIZE, NONE))

fun rotate_sigil s = case s of
    Wire dir => Wire (rotate_dir dir)
  | Wall b => Wall (not b)
  | s => s

fun rotate_diag (d as (header, lines):diag) = let
  val lines' = Vector.tabulate (SIZE, fn i => let
    val (left, right) = lineHeader (Vector.sub (lines, i))
    val body = List.tabulate (SIZE, fn j =>
      sigil_to_string $ rotate_sigil (coord d (i, SIZE-1-j)))
    in left ^ String.concat body ^ right end)
  in (header, lines') end

fun print_diag ((header, lines):diag) = (
  print (header^"\n");
  Vector.app (fn s => print (s^"\n")) lines;
  print (header^"\n"));

fun neighbors d (x, y) = let
  fun get a b = coord d (2*x+a, 2*y+b)
  in (get 1 1, (get 0 1, get 1 0, get 2 1, get 1 2)) end

fun smallNodePattern n = case n of
    Node => [
      (terminator_e, (Wire E, Empty, Empty, Empty)),
      (wire_e_e, (Wire E, Empty, Wire E, Empty)),
      (fast_turn_e_s, (Wire E, Empty, Empty, Wire S)),
      (turn_e_n, (Wire E, Wire N, Empty, Empty)),
      (fork_e_es, (Wire E, Empty, Wire E, Wire S)),
      (fork_e_en, (Wire E, Wire N, Wire E, Empty)),
      (cross_es_es, (Wire E, Wire S, Wire E, Wire S))]
  | SlowNode => [
    (slow_wire_e_e, (Wire E, Empty, Wire E, Empty)),
    (slow_turn_e_s, (Wire E, Empty, Empty, Wire S))]
  | NotG => [(not_e_e, (Wire E, Empty, Wire E, Empty))]
  | AndG => [
      (and_en_e, (Wire E, Empty, Wire E, Wire N)),
      (and_es_e, (Wire E, Wire S, Wire E, Empty)),
      (and_ew_n, (Wire E, Wire N, Wire W, Empty))]
  | OrG => [(or_en_e, (Wire E, Empty, Wire E, Wire N))]

type sigils = sigil * sigil * sigil * sigil
fun rotate_sigils (a,b,c,d) =
  (rotate_sigil d, rotate_sigil a, rotate_sigil b, rotate_sigil c)

type sigils22 = sigils * sigils * sigils * sigils
fun rotate_sigils22 (a,b,c,d) =
  (rotate_sigils d, rotate_sigils a, rotate_sigils b, rotate_sigils c)

type sigils31 = bool * sigils * sigils * sigils
fun rotate_sigils31 (false,a,b,c) =
    (true, rotate_sigils a, rotate_sigils b, rotate_sigils c)
  | rotate_sigils31 (true,a,b,c) =
    (false, rotate_sigils c, rotate_sigils b, rotate_sigils a)

fun match_with f pat nei = let
  exception Found of gate * int
  fun go 4 _ = ()
    | go i (gate, pat) =
      if nei = pat then raise Found (gate, i) else
      go (i+1) (gate, f pat)
  in
    (app (go 0) pat; raise Match)
    handle Found out => out
  end

type gates = ((int * int) * (gate * int)) list

fun recognize d = let
  val gates = ref []
  val _ = for_loop 0 CSIZE (fn y =>
    for_loop 0 CSIZE (fn x => let
      fun push (x, y) (gate, i) = gates := ((x, y), (gate, i)) :: !gates
      val r = neighbors d (x, y)
      fun nn p = #2 (neighbors d p)
      in
        (case r of
          (Empty, (Empty, Empty, Empty, Empty)) => ()
        | (Small n, nei) => push (x, y) (match_with rotate_sigils (smallNodePattern n) nei)
        | (Large n, nei) =>
          if #1 (neighbors d (x-1, y)) = Large n orelse
             #1 (neighbors d (x, y-1)) = Large n then () else
          (case n of
            HalfAddG => push (x, y) $ match_with rotate_sigils22
              [(half_adder_ee_es, (
                (Wire E, Empty, Wall false, Wall true),
                (Wall false, Empty, Wire E, Wall true),
                (Wall false, Wall true, Empty, Wire S),
                (Wire E, Wall true, Wall false, Empty))),
              (half_adder_ee_ee, (
                (Wire E, Empty, Wall false, Wall true),
                (Wall false, Empty, Wire E, Wall true),
                (Wall false, Wall true, Wire E, Empty),
                (Wire E, Wall true, Wall false, Empty)))]
              (nei, nn (x+1, y), nn (x+1, y+1), nn (x, y+1))
          | SlowWire => push (x, y) $ match_with rotate_sigils31
              [(slow_wire_e_e, (false,
                (Wire E, Empty, Wall false, Empty),
                (Wall false, Empty, Wall false, Empty),
                (Wall false, Empty, Wire E, Empty)))]
              (if #3 nei = Wall false then
                (false, nn (x, y), nn (x+1, y), nn (x+2, y))
              else (true, nn (x, y), nn (x, y+1), nn (x, y+2))))
        | _ => (PolyML.print ((x, y), r); raise Fail "unknown node type"))
        handle Match => (PolyML.print ((x, y), r); raise Fail "unknown connection pattern")
      end))
  in !gates end

end
