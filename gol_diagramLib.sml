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
type teleport = (int * int) * dir

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
  val teleports = ref []
  val _ = for_loop 0 CSIZE (fn n => (
    case (coord d (0, 2*n+1), coord d (2*CSIZE, 2*n+1)) of
      (Wire E, Wire E) => teleports := ((2*CSIZE-1, 2*n), E) :: !teleports
    | (Wire W, Wire W) => teleports := ((~1, 2*n), W) :: !teleports
    | (Empty, Empty) => ()
    | r => (PolyML.print r; raise Fail "unmatched teleport");
    case (coord d (2*n+1, 0), coord d (2*n+1, 2*CSIZE)) of
      (Wire S, Wire S) => teleports := ((2*n, 2*CSIZE-1), S) :: !teleports
    | (Wire N, Wire N) => teleports := ((2*n, ~1), N) :: !teleports
    | (Empty, Empty) => ()
    | r => (PolyML.print r; raise Fail "unmatched teleport")))
  in (!gates, !teleports) end

fun toString (s: unit frag list) = let
  val lines = case s of [QUOTE s] => s | _ => raise Bind
  val lines = String.fields (fn x => x = #"\n") lines
  in String.concatWith "\n" (tl lines) end

Quote svg_header = toString:
  <style>
    text {
      font-family: Arial, sans-serif;
    }
  </style>
  <defs>
    <path id="wire" style="fill: black" d="
      M -.51 .1 H -.1 L 0 0 -.1 -.1 H -.51
      M 0 .1 H .51 V -.1 H 0 L .1 0" />
    <g id="slow-wire">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: black" />
      <rect x="-.4" y="-.15" width=".8" height=".3" style="fill: white" />
      <path style="stroke-width: .07; stroke: black; fill: none" d="
        M -.4 -.1 V .15 H .25 V 0 H -.25 V -.15 H .4 V .1" />
    </g>
    <path id="cross" style="stroke-width: .2; stroke: black" d="
      M -.51 0 H .51 M 0 -.51 V -.15 M 0 .15 V .51" />
    <g id="terminator">
      <line x1="-.51" y1="0" x2="0" y2="0" style="stroke-width: .2; stroke: black" />
      <line x1="0" y1="-.3" x2="0" y2=".3" style="stroke-width: .1; stroke: black" />
    </g>
    <g id="and-en-e">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: black" />
      <line x1="0" y1=".51" x2="0" y2="0" style="stroke-width: .2; stroke: black" />
      <path id="and-base" style="stroke-width: .07; stroke: black; fill: white" d="
        M -.3 -.25 L .05 -.25 A .25 .25 180 0 1 .05 .25 L .05 .25 L -.3 .25 Z" />
    </g>
    <use id="and-es-e" href="#and-en-e" transform="scale(1 -1)" />
    <g id="and-ew-n">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: black" />
      <line x1="0" y1="-.51" x2="0" y2="0" style="stroke-width: .2; stroke: black" />
      <use href="#and-base" transform="rotate(-90)" />
    </g>
    <text id="and-text" text-anchor="middle" dominant-baseline="central" font-size=".4">&amp;</text>
    <g id="or-en-e">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: black" />
      <line x1="0" y1=".51" x2="0" y2="0" style="stroke-width: .2; stroke: black" />
      <path style="stroke-width: .07; stroke: black; fill: white" d="
        M 0 -.25 Q .25 -.25 .4 0 Q .25 .25 .0 .25 L -.3 .25 A .5 .5 0 0 0 -.3 -.25 Z" />
    </g>
    <text id="or-text" text-anchor="middle" dominant-baseline="central" font-size=".4">∨</text>
    <g id="not">
      <line x1="-.51" y1="0" x2="0" y2="0" style="stroke-width: .2; stroke: black" />
      <line x1=".3" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: black" />
      <path style="stroke-width: .07; stroke: black; fill: white" d="
        M -.25 -.3 L .25 0 -.25 .3 Z" />
      <circle cx=".3" cy="0" r=".1" style="stroke-width: .04; stroke: black; fill: white" />
      <!--
      <text x="-.07" text-anchor="middle" dominant-baseline="central" font-size=".4">¬</text>
      -->
    </g>
    <path id="turn-e-s" style="stroke-width: .2; stroke: black; fill: none" d="
      M -.51 0 H -.4 A .4 .4 90 0 1 0 .4 V .51" />
    <use id="turn-e-n" href="#turn-e-s" transform="scale(1 -1)" />
    <g id="slow-turn-e-s">
      <path style="stroke-width: .2; stroke: black; fill: none" d="
        M -.51 0 H -.5 C -.3 0 -.05 -.45 .2 -.2 S 0 .3 0 .5 V .51" />
      <!--
      <use href="#turn-e-s" />
      <path style="stroke-width: .05; stroke: black; fill: white" d="
        M -.4 -.15 A .55 .55 90 0 1 .15 .4 H -.15 A .25 .25 90 0 0 -.4 .15 Z" />
      <path style="stroke-width: .05; stroke: black; fill: none" d="M 0 -.15 L .15 .03 0 .15"
        transform="translate(-.4 .4) rotate(30) translate(-.05 -.4)" />
      <path style="stroke-width: .05; stroke: black; fill: none" d="M 0 -.15 L .15 .03 0 .15"
        transform="translate(-.4 .4) rotate(60) translate(-.05 -.4)" />
      -->
    </g>
    <g id="fork-e-es">
      <use href="#turn-e-s" />
      <path id="wire" style="fill: black" d="
        M -.51 .1 H .05 L .15 0 .05 -.1 H -.51
        M .15 .1 H .51 V -.1 H .15 L .25 0" />
    </g>
    <use id="fork-e-en" href="#fork-e-es" transform="scale(1 -1)" />
    <g id="half-adder-ee-ee">
      <path style="stroke-width: .2; stroke: black" d="
        M -1.01 .5 H -.5 M .5 .5 H 1.01
        M -1.01 -.5 H -.5 M .5 -.5 H 1.01" />
      <rect x="-.8" y="-.8" width="1.6" height="1.6" style="stroke-width: .07; stroke: black; fill: white" />
      <text x=".5" y="-.5" text-anchor="middle" dominant-baseline="central" font-size=".4">⊕</text>
      <!--
      <text x=".5" y=".5" text-anchor="middle" dominant-baseline="central" font-size=".4">&amp;</text>
      -->
    </g>
    <g id="half-adder-ee-es">
      <path style="stroke-width: .2; stroke: black" d="
        M -1.01 .5 H -.5 M .5 .5 V 1.01
        M -1.01 -.5 H -.5 M .5 -.5 H 1.01" />
      <rect x="-.8" y="-.8" width="1.6" height="1.6" style="stroke-width: .07; stroke: black; fill: white" />
      <text x=".5" y="-.5" text-anchor="middle" dominant-baseline="central" font-size=".4">⊕</text>
      <!--
      <text x=".5" y=".5" text-anchor="middle" dominant-baseline="central" font-size=".4">&amp;</text>
      -->
    </g>
    <text id="half-adder-text" text-anchor="middle" dominant-baseline="central" font-size=".4">H-A</text>
    <g id="teleport-out">
      <line x1="-.51" y1="0" x2="-.4" y2="0" style="stroke-width: .2; stroke: black" />
      <path id="wire" style="fill: black; stroke-width: .07; stroke: black" d="
        M -.4 0 L -.45 .2 -.1 0 -.45 -.2 Z" />
    </g>
    <g id="teleport-in">
      <line x1=".51" y1="0" x2=".05" y2="0" style="stroke-width: .2; stroke: black" />
      <path id="wire" style="fill: black; stroke-width: .07; stroke: black" d="
        M -.2 0 L -.25 .2 .1 0 -.25 -.2 Z" transform="translate(0.45 0)" />
    </g>
  </defs>
End

fun diag_to_svg (gates, teleports) filename = let
  val cell_size = 50
  val margin = 0.5
  val f = TextIO.openOut filename
  fun realToString r = if r < 0.0 then "-"^Real.toString (~r) else Real.toString r
  val _ = TextIO.output (f, String.concat [
    "<svg viewBox=\"", realToString (~margin - 0.5),
      " ", realToString (~margin - 0.5),
      " ", realToString (Real.fromInt CSIZE + 2.0 * margin),
      " ", realToString (Real.fromInt CSIZE + 2.0 * margin),
      "\" xmlns=\"http://www.w3.org/2000/svg\"",
      " width=\"100%\" height=\"100%\"",
      " style=\"stroke-width: 0px; background-color: white\">\n",
      svg_header,
      "  <rect x=\"-.5\" y=\"-.5\" width=\"",
      Int.toString CSIZE, "\" height=\"",
      Int.toString CSIZE, "\" fill=\"white\"",
      " stroke-dashoffset=\".09\" stroke-dasharray=\".18 .32\"",
      " style=\"stroke-width: .05; stroke: black\" />\n"])
  fun use_obj name (tx, ty) rot =
    TextIO.output(f,String.concat
      ["  <use href=\"#", name,
      "\" transform=\"translate(", realToString tx,
      " ", realToString ty,
      ") rotate(", Int.toString (rot * 90), ")\" />\n"])
  fun gate ((x, y), (g:gol_simLib.gate, rot)) = let
    val (id, text) = case hd (#stems g) of
        "terminator_e" => ("terminator", NONE)
      | "wire_e_e" => ("wire", NONE)
      | "cross_es_es" => ("cross", NONE)
      | "and_en_e" => ("and-en-e", SOME "and-text")
      | "and_es_e" => ("and-es-e", SOME "and-text")
      | "and_ew_n" => ("and-ew-n", SOME "and-text")
      | "or_en_e" => ("or-en-e", SOME "or-text")
      | "not_e_e" => ("not", NONE)
      | "fast_turn_e_s" => ("turn-e-s", NONE)
      | "slow_turn_e_s" => ("slow-turn-e-s", NONE)
      | "turn_e_n" => ("turn-e-n", NONE)
      | "fork_e_es" => ("fork-e-es", NONE)
      | "fork_e_en" => ("fork-e-en", NONE)
      | "half_adder_ee_es" => ("half-adder-ee-es", SOME "half-adder-text")
      | "half_adder_ee_ee" => ("half-adder-ee-ee", SOME "half-adder-text")
      | "slow_wire_e_e" => ("slow-wire", NONE)
      | _ => raise Fail "unsupported gate kind"
    val tx = Real.fromInt x + 0.5 * Real.fromInt (#width g - 1)
    val ty = Real.fromInt y + 0.5 * Real.fromInt (#height g - 1)
    val _ = use_obj id (tx, ty) rot
    val _ = case text of NONE => () | SOME text => (
      use_obj text (tx, ty) 0;
      if text = "half-adder-text" then let
        val (a,b) = funpow rot (fn (x,y) => (~y,x)) (0.5, 0.5)
        in use_obj "and-text" (tx + a, ty + b) 0 end
      else ())
    in () end
  fun teleport ((wx, wy), dir) = let
    val (a,b) = dirToXY dir
    val rot = dirToRot dir
    val _ = PolyML.print ("teleport-out", ((wx + a) div 2, (wy + b) div 2));
    val _ = use_obj "teleport-out" (pair_map Real.fromInt
      ((wx + a) div 2, (wy + b) div 2)) rot
    val _ = PolyML.print ("teleport-in", ((wx - a) div 2 - CSIZE * a, (wy - b) div 2 - CSIZE * b));
    val _ = use_obj "teleport-in" (pair_map Real.fromInt
      ((wx - a) div 2 - CSIZE * a, (wy - b) div 2 - CSIZE * b)) rot
    in () end
  val _ = app gate gates
  val _ = app teleport teleports
  val _ = TextIO.output (f,"</svg>\n")
  in TextIO.closeOut f end

end
