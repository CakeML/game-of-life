open HolKernel bossLib boolLib Parse;
open gol_simLib gol_diagramLib gol_in_gol_paramsLib gol_in_gol_circuitLib;

val _ = new_theory "gol_svg";

fun dropUntil tk s = let
  val lines = String.fields (fn x => x = tk) s
  in String.concatWith (String.str tk) (tl lines) end

fun toString (s: string frag list) = let
  val lines = String.concat (map (fn QUOTE s => dropUntil #")" s | ANTIQUOTE s => s) s)
  in dropUntil #"\n" lines end

fun intToString i = if i < 0 then "-"^(Int.toString (~i)) else Int.toString i
fun realToString r = if r < 0.0 then "-"^Real.toString (~r) else Real.toString r

(* circuit diagrams *)

fun svg_header main_color = let
Quote s = toString:
  <style>
    text {
      font-family: Arial, sans-serif;
    }
  </style>
  <defs>
    <path id='wire' style='fill: ^main_color;' d='
      M -.51 .1 H -.1 L 0 0 -.1 -.1 H -.51
      M 0 .1 H .51 V -.1 H 0 L .1 0' />
    <g id='slow-wire'>
      <line x1='-.51' y1='0' x2='.51' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <rect x='-.4' y='-.15' width='.8' height='.3' style='fill: white' />
      <path style='stroke-width: .07; stroke: ^main_color; fill: none' d='
        M -.4 -.1 V .15 H .25 V 0 H -.25 V -.15 H .4 V .1' />
    </g>
    <path id='cross' style='stroke-width: .2; stroke: ^main_color;' d='
      M -.51 0 H .51 M 0 -.51 V -.15 M 0 .15 V .51' />
    <g id='terminator'>
      <line x1='-.51' y1='0' x2='0' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <line x1='0' y1='-.3' x2='0' y2='.3' style='stroke-width: .1; stroke: ^main_color;' />
    </g>
    <g id='and-en-e'>
      <line x1='-.51' y1='0' x2='.51' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <line x1='0' y1='.51' x2='0' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <path id='and-base' style='stroke-width: .07; stroke: ^main_color; fill: white' d='
        M -.3 -.25 L .05 -.25 A .25 .25 180 0 1 .05 .25 L .05 .25 L -.3 .25 Z' />
    </g>
    <use id='and-es-e' href='#and-en-e' transform='scale(1 -1)' />
    <g id='and-ew-n'>
      <line x1='-.51' y1='0' x2='.51' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <line x1='0' y1='-.51' x2='0' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <use href='#and-base' transform='rotate(-90)' />
    </g>
    <text id='and-text' text-anchor='middle' dominant-baseline='central' font-size='.4'>&amp;</text>
    <g id='or-en-e'>
      <line x1='-.51' y1='0' x2='.51' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <line x1='0' y1='.51' x2='0' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <path style='stroke-width: .07; stroke: ^main_color; fill: white' d='
        M 0 -.25 Q .25 -.25 .4 0 Q .25 .25 .0 .25 L -.3 .25 A .5 .5 0 0 0 -.3 -.25 Z' />
    </g>
    <text id='or-text' text-anchor='middle' dominant-baseline='central' font-size='.4'>∨</text>
    <g id='not'>
      <line x1='-.51' y1='0' x2='0' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <line x1='.3' y1='0' x2='.51' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <path style='stroke-width: .07; stroke: ^main_color; fill: white' d='
        M -.25 -.3 L .25 0 -.25 .3 Z' />
      <circle cx='.3' cy='0' r='.1' style='stroke-width: .04; stroke: ^main_color; fill: white' />
      <!--
      <text x='-.07' text-anchor='middle' dominant-baseline='central' font-size='.4'>¬</text>
      -->
    </g>
    <path id='turn-e-s' style='stroke-width: .2; stroke: ^main_color; fill: none' d='
      M -.51 0 H -.4 A .4 .4 90 0 1 0 .4 V .51' />
    <use id='turn-e-n' href='#turn-e-s' transform='scale(1 -1)' />
    <g id='slow-turn-e-s'>
      <path style='stroke-width: .2; stroke: ^main_color; fill: none' d='
        M -.51 0 H -.5 C -.3 0 -.05 -.45 .2 -.2 S 0 .3 0 .5 V .51' />
      <!--
      <use href='#turn-e-s' />
      <path style='stroke-width: .05; stroke: var(- -main-color); fill: white' d='
        M -.4 -.15 A .55 .55 90 0 1 .15 .4 H -.15 A .25 .25 90 0 0 -.4 .15 Z' />
      <path style='stroke-width: .05; stroke: var(- -main-color); fill: none' d='M 0 -.15 L .15 .03 0 .15'
        transform='translate(-.4 .4) rotate(30) translate(-.05 -.4)' />
      <path style='stroke-width: .05; stroke: var(- -main-color); fill: none' d='M 0 -.15 L .15 .03 0 .15'
        transform='translate(-.4 .4) rotate(60) translate(-.05 -.4)' />
      -->
    </g>
    <g id='fork-e-es'>
      <use href='#turn-e-s' />
      <path id='wire' style='fill: ^main_color;' d='
        M -.51 .1 H .05 L .15 0 .05 -.1 H -.51
        M .15 .1 H .51 V -.1 H .15 L .25 0' />
    </g>
    <use id='fork-e-en' href='#fork-e-es' transform='scale(1 -1)' />
    <g id='half-adder-ee-ee'>
      <path style='stroke-width: .2; stroke: ^main_color;' d='
        M -1.01 .5 H -.5 M .5 .5 H 1.01
        M -1.01 -.5 H -.5 M .5 -.5 H 1.01' />
      <rect x='-.8' y='-.8' width='1.6' height='1.6' style='stroke-width: .07; stroke: ^main_color; fill: white' />
      <text x='.5' y='-.5' text-anchor='middle' dominant-baseline='central' font-size='.4'>⊕</text>
      <!--
      <text x='.5' y='.5' text-anchor='middle' dominant-baseline='central' font-size='.4'>&amp;</text>
      -->
    </g>
    <g id='half-adder-ee-es'>
      <path style='stroke-width: .2; stroke: ^main_color;' d='
        M -1.01 .5 H -.5 M .5 .5 V 1.01
        M -1.01 -.5 H -.5 M .5 -.5 H 1.01' />
      <rect x='-.8' y='-.8' width='1.6' height='1.6' style='stroke-width: .07; stroke: ^main_color; fill: white' />
      <text x='.5' y='-.5' text-anchor='middle' dominant-baseline='central' font-size='.4'>⊕</text>
      <!--
      <text x='.5' y='.5' text-anchor='middle' dominant-baseline='central' font-size='.4'>&amp;</text>
      -->
    </g>
    <text id='half-adder-text' text-anchor='middle' dominant-baseline='central' font-size='.4'>H-A</text>
    <g id='teleport-out'>
      <line x1='-.51' y1='0' x2='-.4' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <path id='wire' style='fill: ^main_color; stroke-width: .07; stroke: ^main_color;' d='
        M -.4 0 L -.45 .2 -.1 0 -.45 -.2 Z' />
    </g>
    <g id='teleport-in'>
      <line x1='.51' y1='0' x2='.05' y2='0' style='stroke-width: .2; stroke: ^main_color;' />
      <path id='wire' style='fill: ^main_color; stroke-width: .07; stroke: ^main_color;' d='
        M -.2 0 L -.25 .2 .1 0 -.25 -.2 Z' transform='translate(0.45 0)' />
    </g>
  </defs>
End
in s end

type diag_opts = {
  period: real, speed: real,
  wires: ((int * int) * (string * int) list) list}

val (gates, teleports) = recognize diag

fun diag_to_svg (wires:diag_opts option) grid callout_back filename = let
  val cell_size = 50
  val margin = 0.5
  val f = TextIO.openOut filename
  val _ = TextIO.output (f, String.concat [
    "<svg viewBox=\"0 0 ", realToString (Real.fromInt tile + 2.0 * margin),
    " ", realToString (Real.fromInt tile + 2.0 * margin),
    "\" xmlns=\"http://www.w3.org/2000/svg\"",
    " width=\"1600\" height=\"1600\"",
    " style=\"stroke-width: 0px; background-color: white\">\n",
    svg_header (case wires of NONE => "black" | SOME _ => "#ccc"),
    "  <g transform=\"translate(", realToString (margin + 0.5),
    " ", realToString (margin + 0.5), ")\">\n",
    callout_back])
  val _ = if grid then let
    val path = String.concatWith " " $
      List.tabulate (tile - 1, fn i => String.concat [
        "M ", intToString (i+1), " 0 V ", intToString tile]) @
      List.tabulate (tile - 1, fn i => String.concat [
        "M 0 ", intToString (i+1), " H ", intToString tile])
    val _ = TextIO.output (f, String.concat [
        "    <path",
        " stroke-dashoffset=\".09\" stroke-dasharray=\".18 .82\"",
        " style='stroke-width: .05; stroke: black; stroke-opacity: 0.2; fill: none'",
        " transform='translate(-0.5 -0.5)' d='", path, "' />\n"])
    in () end
  else ()
  val _ = TextIO.output (f, String.concat [
    "    <rect x=\"-.5\" y=\"-.5\" width=\"",
    Int.toString tile, "\" height=\"",
    Int.toString tile, "\" fill=\"none\"",
    " stroke-dashoffset=\".09\" stroke-dasharray=\".18 .32\"",
    " style=\"stroke-width: .05; stroke: black\" />\n"])
  fun use_obj name (tx, ty) rot =
    TextIO.output (f, String.concat
      ["    <use href=\"#", name,
      "\" transform=\"translate(", realToString tx,
      " ", realToString ty,
      ") rotate(", Int.toString (rot * 90), ")\" />\n"])
  val _ = C app gates (fn ((x, y), (g, rot)) => let
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
    in () end)
  val _ = C app teleports (fn ((wx, wy), dir) => let
    val (a,b) = dirToXY dir
    val rot = dirToRot dir
    val _ = use_obj "teleport-out" (pair_map Real.fromInt
      ((wx + a) div 2, (wy + b) div 2)) rot
    val _ = use_obj "teleport-in" (pair_map Real.fromInt
      ((wx - a) div 2 - tile * a, (wy - b) div 2 - tile * b)) rot
    in () end)
  val _ = case wires of
    NONE => ()
  | SOME {speed, period, wires} => C app wires (fn ((wx, wy), vs) =>
    TextIO.output (f, String.concat [
      "    <circle cx=\"", realToString (Real.fromInt wx / 2.0),
      "\" cy=\"", realToString (Real.fromInt wy / 2.0),
      "\" r=\".11\" style=\"stroke-width: .01; stroke: black\">\n",
      "      <animate attributeName=\"fill\"",
      " values=\"", String.concatWith ";" (map fst vs), "\"",
      " dur=\"", realToString (period / speed), "s\" keyTimes=\"",
      String.concatWith ";" (map (fn (_, r) => realToString (Real.fromInt r / period)) vs),
      "\" repeatCount=\"indefinite\" />\n",
      "    </circle>\n"]))
  val _ = TextIO.output (f,"  </g>\n</svg>\n")
  in TextIO.closeOut f end

fun diag_to_svg_with_wires {speed, fade, offset} filename = let
  val wires = build (recognize diag) params nolog
  val period = #period params
  val dur = 2 * period
  fun trim ls = let
    val ls = filter (fn (_, n) => 0 <= n andalso n <= dur) ls
    val (ls0, lsN) = (hd ls, last ls)
    val ls1 = if snd ls0 = 0 then [] else [(fst ls0, 0)]
    val ls2 = if snd lsN = dur then [] else [(fst lsN, dur)]
    in ls1 @ ls @ ls2 end
  fun clock (off, on, off', on') n = [
    (off', n - period), (on', n + fade - period),
    (on', n + pulse - period), (off, n + pulse + fade - period),
    (off, n), (on, n + fade),
    (on, n + pulse), (off', n + pulse + fade),
    (off', n + period), (on', n + period + fade),
    (on', n + period + pulse), (off, n + period + pulse + fade),
    (off, n + dur), (on, n + dur + fade),
    (on, n + dur + pulse), (off', n + dur + pulse + fade)]
  fun reg (off, on, off', on') n = [
    (off', offset+Int.min (fade, n)-period), (off', n+offset-period),
    (on', n+offset+fade-period), (on', offset),
    (off, offset+Int.min (fade, n)), (off, n+offset),
    (on, n+offset+fade), (on, period+offset),
    (off', period+offset+Int.min (fade, n)), (off', period + n+offset),
    (on', period + n+fade+offset), (on', dur+offset),
    (off, dur+offset+Int.min (fade, n)), (off, dur + n+offset),
    (on, dur + n+fade+offset)]
  fun oklab (a, b) (i, j) = String.concat [
    "oklab(", realToString (0.6 + 0.2 * Real.fromInt i),
    " ", realToString a,
    " ", realToString (b + 0.1 * Real.fromInt j), ")"]
  val red = oklab (0.15, 0.1)
  val blue = oklab (~0.1, ~0.2)
  val wires = C map (Redblackmap.listItems wires) $ apsnd (trim o (fn
    Approx (n, Cell p) => reg ("#ccc", red p, "#ccc", blue p) n
  | Approx (n, v) =>
      if v = nextCell then reg ("#ccc", blue (0,0), "#ccc", red (0,0)) n
      else reg ("#ccc", "purple", "#ccc", "green") n
  | Exact (n, v) => let
    val (off, on, off', on') = case v of
      Clock => ("white", "black", "white", "black")
    | NotClock => ("black", "white", "black", "white")
    | ThisCell => (blue (0,0), red (0,0), red (0,0), blue (0,0))
    | ThisCellClock => ("white", red (0,0), "white", blue (0,0))
    | ThisCellNotClock => (blue (0,0), "white", red (0,0), "white")
    in clock (off, on, off', on') (n + offset) end))
  val w = {period = Real.fromInt dur, speed = speed, wires = wires}
  in diag_to_svg (SOME w) false filename end


Quote callout = toString:
    <rect x='10.5' y='3.5' width='2' height='2' rx='.3' fill='#ff6' style='stroke-width: .05; stroke: grey' />
End
val _ = diag_to_svg NONE true callout "mega-cell.svg";
val _ = diag_to_svg_with_wires {speed = 25.0, fade = 4, offset = ~4} "" "propagation.svg";

(* gate diagrams *)

val red = "#a00"
val yellow = "#aa0"
val blue = "#00c"
val purple = "#c0c"
val lightred = "#fcc"
val lightblue = "#ccf"
val lightpurple = "#faf"

(*
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
    fn i => fn j => Vector.sub(Vector.sub(grid,i),j)) *)

Quote svg_header = toString:
  <defs>
    <pattern id="grid" viewBox="0 0 1 1" x="-.05" y="-.05" width="1" height="1" patternUnits="userSpaceOnUse">
      <path style="stroke-width: .1; stroke: #ccc; fill: none" d="M .05 1.1 V .05 H 1.1" />
    </pattern>
    <linearGradient id="grad0" gradientUnits="userSpaceOnUse" x1="-5" y1="0" x2="15" y2="0">
      <stop offset="0" style='stop-color:^lightred; stop-opacity:0' />
      <stop offset="1" style='stop-color:^lightred; stop-opacity:1' />
    </linearGradient>
    <linearGradient id="grad1" gradientUnits="userSpaceOnUse" x1="-5" y1="0" x2="15" y2="0">
      <stop offset="0" style='stop-color:^lightblue; stop-opacity:0' />
      <stop offset="1" style='stop-color:^lightblue; stop-opacity:1' />
    </linearGradient>
    <linearGradient id="gradO" gradientUnits="userSpaceOnUse" x1="-5" y1="0" x2="15" y2="0">
      <stop offset="0" style='stop-color:^lightpurple; stop-opacity:0' />
      <stop offset="1" style='stop-color:^lightpurple; stop-opacity:1' />
    </linearGradient>
    <path id="arrow-in" d="M -5 -5 H 15 V -8 L 28 0 15 8 V 5 H -5 Z" />
    <path id="arrow-out" d="M -5 -5 H 15 V -8 L 28 0 15 8 V 5 H -5 Z" transform="translate(-25 0)" />
  </defs>
End

fun grid_to_svg (g: gate) env filename =
  let
    val {grid, inputs, outputs} = run_to_fixpoint (prepare (load g))
    val io = map (fn x => (x, false)) inputs @ map (fn x => (x, true)) outputs
    fun mk_paths ph2 = let
      fun getIO x = Option.map (fn (p, out) => (p, if (is_ew p = out) = ph2 then 1 else ~1)) $
        List.find (fn (p, _) => #1 p = x) io
      fun on_ports lo hi f g = for_loop lo hi ((fn i => Option.app (g i) (getIO i)) o f)
      val outer = ref ["M -75 -75 "]
      val inner = ref ["M -74 -74 "]
      fun write' r s l = r := String.concat (map (fn i => intToString i ^ " ") l) :: s :: !r
      fun write s l = (write' outer s (map fst l); write' inner s (map (op +) l))
      val _ = on_ports 0 (#width g) (fn i => (2*i, ~1))
        (fn (x, y) => fn (v, out) => (
          write "H " [(~6 + 75*x, out)]; write "V " [(75*y - out*6, 1)];
          write "H " [(6 + 75*x, ~out)]; write "V " [(75*y, 1)]))
      val _ = write "H " [(150 * #width g - 75, ~1)];
      val _ = on_ports 0 (#height g) (fn i => (2 * #width g - 1, 2*i))
        (fn (x,y) => fn (v, out) => (
          write "V " [(~6 + 75*y, out)]; write "H " [(75*x + out*6, ~1)];
          write "V " [(6 + 75*y, ~out)]; write "H " [(75*x, ~1)]))
      val _ = write "V " [(150 * #height g - 75, ~1)];
      val _ = on_ports 0 (#height g) (fn i => (2*(#height g - 1 - i), 2 * #height g - 1))
        (fn (x,y) => fn (v, out) => (
          write "H " [(6 + 75*x, ~out)]; write "V " [(75*y + out*6, ~1)];
          write "H " [(~6 + 75*x, out)]; write "V " [(75*y, ~1)]))
      val _ = write "H " [(~75, 1)];
      val _ = on_ports 0 (#width g) (fn i => (~1, 2*(#width g - 1 - i)))
        (fn (x,y) => fn (v, out) => (
          write "V " [(6 + 75*y, ~out)]; write "H " [(75*x - out*6, 1)];
          write "V " [(~6 + 75*y, out)]; write "H " [(75*x, 1)]))
      in (String.concat $ rev (!outer), String.concat $ rev (!inner)) end
    val margin = 7.0
    val f = TextIO.openOut filename
    val _ = TextIO.output(f, String.concat [
      "<svg viewBox=\"0 0 ", realToString (150.0 * Real.fromInt (#width g) + 2.0 * margin),
        " ", realToString (150.0 * Real.fromInt (#height g) + 2.0 * margin),
        "\" xmlns=\"http://www.w3.org/2000/svg\"",
        " width=\"100%\" height=\"100%\"",
        " style=\"stroke-width: 0px; background-color: white\">\n",
        svg_header,
        "  <g transform='translate(", realToString (margin + 75.0),
        " ", realToString (margin + 75.0), ")'>\n"])
    val _ = C app io (fn (((x, y), d, v), out) =>
      TextIO.output(f, String.concat [
        "    <use href='#", if out then "arrow-out" else "arrow-in",
        "' fill='url(#grad", case v of Var (i, _) => intToString i | _ => "O",
        ")' transform='translate(", intToString (75 * x), " ", intToString (75 * y),
        ") rotate(", intToString (90 * dirToRot d), ")' />\n"]))
    val depth = map (fn (_,_,Var (_, i)) => Real.fromInt i | _ => raise Match) (#inputs g)
    val env = Option.map (fn ls => fn (n, _) => List.nth (ls, n) <> 0) env
    val _ = for_loop 0 (Vector.length grid) (fn y => let
      val row = Vector.sub (grid, y)
      val _ = for_loop 0 (Vector.length row) (fn x => let
        val cell = Vector.sub (row, x)
        val cell = case env of
          NONE => cell
        | SOME env =>
          if eval_bexp cell env then
            subst_bexp cell (fn v => if env v then Var v else False)
          else False
        fun write color =
          TextIO.output(f, String.concat [
            "    <rect x=\"", intToString (x-85), "\" y=\"", intToString (y-85),
            "\" width=\"1\" height=\"1\" fill=\"", color, "\" />\n"])
        fun oklab n depth (a, b) = String.concat [
          "oklab(", realToString (~0.25 + 1.5 * Real.fromInt n / depth),
          " ", realToString a, " ", realToString b, ")"]
        val _ = case cell of
          False => ()
        | True => write "black"
        (* | Var (0, n) => write $ oklab n (List.nth (depth, 0)) (0.15, 0.1)
        | Var (1, n) => write $ oklab n (List.nth (depth, 0)) (~0.1, ~0.2) *)
        | Var (0, _) => write red
        | Not (Var (1, _)) => write yellow
        | Var (1, _) => write blue
        | _ => write purple
        in () end)
      in () end)
    val (outer, inner) = mk_paths false
    val _ = TextIO.output(f, String.concat [
      "    <path fill=\"none\" style=\"stroke-width: .1; stroke: black\" d=\"\n",
      "    ", outer, "Z\" />\n",
      (* "  <path fill=\"url(#grid)\" style=\"stroke-width: .1; stroke: url(#grid)\" d=\"\n",
      "    ", inner, "Z\" />\n", *)
      "  </g>\n",
      "</svg>\n"])
    val _ = TextIO.closeOut(f)
  in () end;

val _ = grid_to_svg and_en_e NONE "and-en-e.svg";
val _ = grid_to_svg and_en_e (SOME [0, 0]) "and-en-e-00.svg";
val _ = grid_to_svg and_en_e (SOME [0, 1]) "and-en-e-01.svg";
val _ = grid_to_svg and_en_e (SOME [1, 0]) "and-en-e-10.svg";
val _ = grid_to_svg and_en_e (SOME [1, 1]) "and-en-e-11.svg";
val _ = grid_to_svg cross_es_es NONE "cross-es-es.svg";
val _ = grid_to_svg half_adder_ee_ee NONE "half-adder-ee-ee.svg";

fun new_grid cols rows =
  Array.tabulate (rows, fn row => Array.tabulate (cols, fn col => False))

(* gol simulation diagrams *)

fun simple_sim rows cols color filename (init: string list) =
  let
    val grid = Array.fromList $ C map init (fn s =>
      Array.fromList $ C map (String.explode s) (fn
          #" " => False
        | #"." => True
        | #"a" => Var(0,0)
        | #"b" => Var(1,0)
        | _ => raise Bind))
    val height = Array.length grid
    val width = Array.length (Array.sub (grid, 0))
    val spacing = 1.5
    val margin = 1.0
    val f = TextIO.openOut filename
    val diffW = Real.fromInt width + spacing
    val diffH = Real.fromInt height + spacing
    val imgWidth = Real.fromInt cols * diffW - spacing + 2.0 * margin
    val imgHeight = Real.fromInt rows * diffH - spacing + 2.0 * margin
    val scale = 1600.0 / imgWidth
    val path = String.concatWith " " $
      List.tabulate (width - 1, fn i => String.concat [
        "M ", intToString (i+1), " 0 V ", intToString height]) @
      List.tabulate (height - 1, fn i => String.concat [
        "M 0 ", intToString (i+1), " H ", intToString width])
    val _ = TextIO.output(f, String.concat [
      "<svg viewBox=\"0 0 ", realToString imgWidth, " ", realToString imgHeight,
        "\" xmlns=\"http://www.w3.org/2000/svg\"",
        " width=\"", realToString (scale * imgWidth),
        "\" height=\"", realToString (scale * imgHeight),
        "\">\n",
        "  <defs>\n",
        "    <g id='box'>\n",
        "      <path style='stroke-width: .1; stroke: #ccc; fill: none' d='", path, "' />\n",
        "      <rect width='", intToString width, "' height='", intToString height,
        "' style='stroke-width: .1; stroke: black; fill: none' />\n",
        "    </g>\n",
        "  </defs>\n"])
    val grids = ref (grid, new_grid width height)
    val _ = for_loop 0 rows (fn j => for_loop 0 cols (fn i => let
      val grid = fst (!grids)
      val _ = TextIO.output(f, String.concat [
        "  <g transform=\"translate(", realToString (Real.fromInt i * diffW + margin),
        " ", realToString (Real.fromInt j * diffH + margin), ")\">\n"])
      val _ = for_loop 0 height (fn y => let
        val row = Array.sub (grid, y)
        val _ = for_loop 0 width (fn x => let
          val cell = Array.sub (row, x)
          fun write color =
            TextIO.output(f, String.concat [
              "    <rect x=\"", intToString x, "\" y=\"", intToString y,
              "\" width=\"1\" height=\"1\" fill=\"", color, "\" />\n"])
          fun oklab n depth (a, b) = String.concat [
            "oklab(", realToString (~0.25 + 1.5 * Real.fromInt n / depth),
            " ", realToString a, " ", realToString b, ")"]
          val _ = case cell of
            False => ()
          | True => write (case color of SOME f => f (x, y) | _ => "black")
          (* | Var (0, n) => write $ oklab n (List.nth (depth, 0)) (0.15, 0.1)
          | Var (1, n) => write $ oklab n (List.nth (depth, 0)) (~0.1, ~0.2) *)
          | Var (0, _) => write red
          | Var (1, _) => write blue
          | _ => write purple
          in () end)
        in () end)
      val _ = TextIO.output(f, String.concat [
        "    <use href=\"#box\" />\n",
        "  </g>\n"])
      in grids := (fn (old, new) => (raw_step old new; (new, old))) (!grids) end))
    val _ = TextIO.output(f, String.concat [
      "</svg>\n"])
    val _ = TextIO.closeOut(f)
  in () end;

fun spaceshipColor (x, _) = if x < 6 then red else blue
val _ = simple_sim 1 5 (SOME spaceshipColor) "spaceships.svg" [
  "            ",
  "            ",
  "            ",
  "       ...  ",
  "      .  .  ",
  "         .  ",
  " ...     .  ",
  "   .  . .   ",
  "  .         ",
  "            "]

val _ = simple_sim 1 5 (SOME spaceshipColor) "collision.svg" [
  "            ",
  "            ",
  "            ",
  "       ...  ",
  "      .  .  ",
  "         .  ",
  "         .  ",
  "  ... . .   ",
  "    .       ",
  "   .        ",
  "            "]

Quote svg_header = toString:
  <style>
    text {
      font-family: Arial, sans-serif;
    }
  </style>
  <defs>
    <linearGradient id="grad" gradientUnits="userSpaceOnUse" x1="-5" y1="0" x2="15" y2="0">
      <stop offset="0" style='stop-color:#ccc; stop-opacity:0' />
      <stop offset="1" style='stop-color:#ccc; stop-opacity:1' />
    </linearGradient>
    <path id="lwss" d="M 0 -3 L 6 0 L 0 3 Z" />
    <path id="glider" d="M -1 2 L 3 4 L -1 6 Z" />
    <g id="and-pop">
      <use href="#lwss" fill="#a00" transform="translate(-75 0)" />
      <use href="#lwss" fill="#a00" transform="translate(-45 0)" />
      <use href="#lwss" fill="#a00" transform="translate(-15 0)" />
      <use href="#lwss" fill="#00c" transform="translate(0 60) rotate(-90)" />
      <use href="#lwss" fill="#00c" transform="translate(0 30) rotate(-90)" />
      <use href="#lwss" fill="#c0c" transform="translate(15 0)" />
      <use href="#lwss" fill="#c0c" transform="translate(45 0)" />
      <use href="#glider" fill="#aa0" transform="translate(-10 5) rotate(-135)" />
      <use href="#glider" fill="black" transform="translate(5 20) rotate(-135)" />
      <use href="#glider" fill="black" transform="translate(20 35) rotate(-135)" />
    </g>
    <g id="wire-pop">
      <use href="#lwss" fill="#c0c" transform="translate(-75 0)" />
      <use href="#lwss" fill="#c0c" transform="translate(-45 0)" />
      <use href="#lwss" fill="#c0c" transform="translate(-15 0)" />
      <use href="#lwss" fill="#c0c" transform="translate(15 0)" />
      <use href="#lwss" fill="#c0c" transform="translate(45 0)" />
    </g>
    <path id="arrow-in" d="M -5 -5 H 15 V -8 L 28 0 15 8 V 5 H -5 Z" />
    <path id="arrow-out" d="M -5 -5 H 15 V -8 L 28 0 15 8 V 5 H -5 Z" transform="translate(-25 0)" />
    <g id="and-gate">
      <path fill="none" style="stroke-width: .05; stroke: black" d="
        M -2 -2 H 2 V -.5 H 1.5 V .5 H 2 V 2 H .5 V 1.5 H -.5 V 2 H -2 V .5 H -2.5 V -.5 H -2 Z" />
      <g id="and-gate-arrows">
        <g transform="translate(-2 -2) scale(.02666 .02666) translate(75 75)">
          <use href='#arrow-in' fill='url(#grad)' transform='translate(-75 0) rotate(0) scale(2 2)' />
          <use href='#arrow-in' fill='url(#grad)' transform='translate(0 75) rotate(270) scale(2 2)' />
          <use href='#arrow-out' fill='url(#grad)' transform='translate(75 0) rotate(0) scale(2 2)' />
          <use href='#and-pop' />
        </g>
        <text x="0" y="-1" id='and-text' text-anchor='middle' dominant-baseline='central' font-size='1'>&amp;</text>
      </g>
    </g>
    <g id="comp1" transform="translate(2 2)">
      <use href="#and-gate" />
      <g transform="translate(5 0)">
        <path fill="none" style="stroke-width: .05; stroke: black" d="
          M -2 -2 H 2 V -.5 H 1.5 V .5 H 2 V 2 H -2 V .5 H -2.5 V -.5 H -2 Z" />
        <g id="wire-arrows">
          <g transform="translate(-2 -2) scale(.02666 .02666) translate(75 75)">
            <use href='#arrow-in' fill='url(#grad)' transform='translate(-75 0) rotate(0) scale(2 2)' />
            <use href='#arrow-out' fill='url(#grad)' transform='translate(75 0) rotate(0) scale(2 2)' />
            <use href='#wire-pop' />
          </g>
          <path id="wire-sym" style='fill: black;' transform="translate(0 -1) scale(.8 .8)" d='
            M -.51 .1 H -.1 L 0 0 -.1 -.1 H -.51
            M 0 .1 H .51 V -.1 H 0 L .1 0' />
        </g>
      </g>
    </g>
    <g id="comp2" transform="translate(2.5 2)">
      <ellipse cx='2' cy='0' rx='1.53' ry='.8' fill='#ff6' style='stroke-width: .02; stroke: grey' />
      <path fill="none" style="stroke-width: .03; stroke: #ccc" d="M 2 -2 V -.5 H 1.5 V .5 H 2 V 2" />
      <path id="merged" fill="none" style="stroke-width: .05; stroke: black" d="
        M -2 -2 H 6 V -.5 H 5.5 V .5 H 6 V 2 H .5 V 1.5 H -.5 V 2 H -2 V .5 H -2.5 V -.5 H -2 Z" />
      <use href="#and-gate-arrows" />
      <use href="#wire-arrows" transform="translate(4 0)" />
    </g>
    <g id="comp3" transform="translate(2.5 2)">
      <use href="#merged" />
      <g transform="translate(-2 -2) scale(.02666 .02666) translate(75 75)">
        <use href='#arrow-in' fill='url(#grad)' transform='translate(-75 0) rotate(0) scale(2 2)' />
        <use href='#arrow-in' fill='url(#grad)' transform='translate(0 75) rotate(270) scale(2 2)' />
        <use href='#and-pop' />
      </g>
      <use href='#and-text' />
      <g transform="translate(4 0)">
        <g transform="translate(-2 -2) scale(.02666 .02666) translate(75 75)">
          <use href='#arrow-out' fill='url(#grad)' transform='translate(75 0) rotate(0) scale(2 2)' />
          <use href='#wire-pop' />
        </g>
        <use href='#wire-sym' />
      </g>
    </g>
  </defs>
End

fun composition_diag d filename =
  let
    val margin = 0.6
    val spacing = 1.0
    val f = TextIO.openOut filename
    val imgWidth = 8.0 + spacing + 2.0 * margin
    val diff = 4.0 + spacing
    val imgHeight = diff * (case d of NONE => 3.0 | _ => 1.0) - spacing + 2.0 * margin
    val scale = 60.0
    val _ = TextIO.output(f, String.concat [
      "<svg viewBox=\"0 0 ", realToString imgWidth, " ", realToString imgHeight,
      "\" xmlns=\"http://www.w3.org/2000/svg\"",
      " width=\"", realToString (scale * imgWidth),
      "\" height=\"", realToString (scale * imgHeight),
      "\">\n",
      svg_header])
    val _ = case d of
      SOME d => TextIO.output(f, String.concat [
      "  <use href='#", d,
      "' transform='translate(", realToString margin, " ", realToString margin, ")' />\n"])
    | NONE => TextIO.output(f, String.concat [
      "  <g transform='translate(", realToString margin, " ", realToString margin, ")'>\n",
      "    <use href='#comp1' />\n",
      "    <use href='#comp2' transform='translate(0 ", realToString diff, ")' />\n",
      "    <use href='#comp3' transform='translate(0 ", realToString (2.0 * diff), ")' />\n",
      "  </g>\n"])
    val _ = TextIO.output(f, "</svg>\n")
    val _ = TextIO.closeOut(f)
  in () end;

val _ = composition_diag (SOME "comp1") "composition1.svg";
val _ = composition_diag (SOME "comp2") "composition2.svg";
val _ = composition_diag (SOME "comp3") "composition3.svg";
val _ = composition_diag NONE "composition.svg";

val _ = export_theory();
