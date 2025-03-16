open HolKernel bossLib boolLib Parse;
open gol_simLib gol_diagramLib gol_in_gol_paramsLib gol_in_gol_circuitLib;

val _ = new_theory "gol_svg";

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
    <path id="wire" style="fill: var(--main-color)" d="
      M -.51 .1 H -.1 L 0 0 -.1 -.1 H -.51
      M 0 .1 H .51 V -.1 H 0 L .1 0" />
    <g id="slow-wire">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <rect x="-.4" y="-.15" width=".8" height=".3" style="fill: white" />
      <path style="stroke-width: .07; stroke: var(--main-color); fill: none" d="
        M -.4 -.1 V .15 H .25 V 0 H -.25 V -.15 H .4 V .1" />
    </g>
    <path id="cross" style="stroke-width: .2; stroke: var(--main-color)" d="
      M -.51 0 H .51 M 0 -.51 V -.15 M 0 .15 V .51" />
    <g id="terminator">
      <line x1="-.51" y1="0" x2="0" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <line x1="0" y1="-.3" x2="0" y2=".3" style="stroke-width: .1; stroke: var(--main-color)" />
    </g>
    <g id="and-en-e">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <line x1="0" y1=".51" x2="0" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <path id="and-base" style="stroke-width: .07; stroke: var(--main-color); fill: white" d="
        M -.3 -.25 L .05 -.25 A .25 .25 180 0 1 .05 .25 L .05 .25 L -.3 .25 Z" />
    </g>
    <use id="and-es-e" href="#and-en-e" transform="scale(1 -1)" />
    <g id="and-ew-n">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <line x1="0" y1="-.51" x2="0" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <use href="#and-base" transform="rotate(-90)" />
    </g>
    <text id="and-text" text-anchor="middle" dominant-baseline="central" font-size=".4">&amp;</text>
    <g id="or-en-e">
      <line x1="-.51" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <line x1="0" y1=".51" x2="0" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <path style="stroke-width: .07; stroke: var(--main-color); fill: white" d="
        M 0 -.25 Q .25 -.25 .4 0 Q .25 .25 .0 .25 L -.3 .25 A .5 .5 0 0 0 -.3 -.25 Z" />
    </g>
    <text id="or-text" text-anchor="middle" dominant-baseline="central" font-size=".4">∨</text>
    <g id="not">
      <line x1="-.51" y1="0" x2="0" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <line x1=".3" y1="0" x2=".51" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <path style="stroke-width: .07; stroke: var(--main-color); fill: white" d="
        M -.25 -.3 L .25 0 -.25 .3 Z" />
      <circle cx=".3" cy="0" r=".1" style="stroke-width: .04; stroke: var(--main-color); fill: white" />
      <!--
      <text x="-.07" text-anchor="middle" dominant-baseline="central" font-size=".4">¬</text>
      -->
    </g>
    <path id="turn-e-s" style="stroke-width: .2; stroke: var(--main-color); fill: none" d="
      M -.51 0 H -.4 A .4 .4 90 0 1 0 .4 V .51" />
    <use id="turn-e-n" href="#turn-e-s" transform="scale(1 -1)" />
    <g id="slow-turn-e-s">
      <path style="stroke-width: .2; stroke: var(--main-color); fill: none" d="
        M -.51 0 H -.5 C -.3 0 -.05 -.45 .2 -.2 S 0 .3 0 .5 V .51" />
      <!--
      <use href="#turn-e-s" />
      <path style="stroke-width: .05; stroke: var(- -main-color); fill: white" d="
        M -.4 -.15 A .55 .55 90 0 1 .15 .4 H -.15 A .25 .25 90 0 0 -.4 .15 Z" />
      <path style="stroke-width: .05; stroke: var(- -main-color); fill: none" d="M 0 -.15 L .15 .03 0 .15"
        transform="translate(-.4 .4) rotate(30) translate(-.05 -.4)" />
      <path style="stroke-width: .05; stroke: var(- -main-color); fill: none" d="M 0 -.15 L .15 .03 0 .15"
        transform="translate(-.4 .4) rotate(60) translate(-.05 -.4)" />
      -->
    </g>
    <g id="fork-e-es">
      <use href="#turn-e-s" />
      <path id="wire" style="fill: var(--main-color)" d="
        M -.51 .1 H .05 L .15 0 .05 -.1 H -.51
        M .15 .1 H .51 V -.1 H .15 L .25 0" />
    </g>
    <use id="fork-e-en" href="#fork-e-es" transform="scale(1 -1)" />
    <g id="half-adder-ee-ee">
      <path style="stroke-width: .2; stroke: var(--main-color)" d="
        M -1.01 .5 H -.5 M .5 .5 H 1.01
        M -1.01 -.5 H -.5 M .5 -.5 H 1.01" />
      <rect x="-.8" y="-.8" width="1.6" height="1.6" style="stroke-width: .07; stroke: var(--main-color); fill: white" />
      <text x=".5" y="-.5" text-anchor="middle" dominant-baseline="central" font-size=".4">⊕</text>
      <!--
      <text x=".5" y=".5" text-anchor="middle" dominant-baseline="central" font-size=".4">&amp;</text>
      -->
    </g>
    <g id="half-adder-ee-es">
      <path style="stroke-width: .2; stroke: var(--main-color)" d="
        M -1.01 .5 H -.5 M .5 .5 V 1.01
        M -1.01 -.5 H -.5 M .5 -.5 H 1.01" />
      <rect x="-.8" y="-.8" width="1.6" height="1.6" style="stroke-width: .07; stroke: var(--main-color); fill: white" />
      <text x=".5" y="-.5" text-anchor="middle" dominant-baseline="central" font-size=".4">⊕</text>
      <!--
      <text x=".5" y=".5" text-anchor="middle" dominant-baseline="central" font-size=".4">&amp;</text>
      -->
    </g>
    <text id="half-adder-text" text-anchor="middle" dominant-baseline="central" font-size=".4">H-A</text>
    <g id="teleport-out">
      <line x1="-.51" y1="0" x2="-.4" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <path id="wire" style="fill: var(--main-color); stroke-width: .07; stroke: var(--main-color)" d="
        M -.4 0 L -.45 .2 -.1 0 -.45 -.2 Z" />
    </g>
    <g id="teleport-in">
      <line x1=".51" y1="0" x2=".05" y2="0" style="stroke-width: .2; stroke: var(--main-color)" />
      <path id="wire" style="fill: var(--main-color); stroke-width: .07; stroke: var(--main-color)" d="
        M -.2 0 L -.25 .2 .1 0 -.25 -.2 Z" transform="translate(0.45 0)" />
    </g>
  </defs>
End

fun realToString r = if r < 0.0 then "-"^Real.toString (~r) else Real.toString r

type diag_opts = {
  period: real, speed: real,
  wires: ((int * int) * (string * int) list) list}

val (gates, teleports) = recognize diag

fun diag_to_svg (wires:diag_opts option) filename = let
  val cell_size = 50
  val margin = 0.5
  val f = TextIO.openOut filename
  val _ = TextIO.output (f, String.concat [
    "<svg viewBox=\"", realToString (~margin - 0.5),
      " ", realToString (~margin - 0.5),
      " ", realToString (Real.fromInt CSIZE + 2.0 * margin),
      " ", realToString (Real.fromInt CSIZE + 2.0 * margin),
      "\" xmlns=\"http://www.w3.org/2000/svg\"",
      " width=\"100%\" height=\"100%\"",
      " style=\"stroke-width: 0px; background-color: white\">\n",
      "  <style>:root { --main-color: ",
      case wires of NONE => "black" | SOME _ => "#ccc",
      "; }</style>\n",
      svg_header,
      "  <rect x=\"-.5\" y=\"-.5\" width=\"",
      Int.toString CSIZE, "\" height=\"",
      Int.toString CSIZE, "\" fill=\"white\"",
      " stroke-dashoffset=\".09\" stroke-dasharray=\".18 .32\"",
      " style=\"stroke-width: .05; stroke: black\" />\n"])
  fun use_obj name (tx, ty) rot =
    TextIO.output (f, String.concat
      ["  <use href=\"#", name,
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
      ((wx - a) div 2 - CSIZE * a, (wy - b) div 2 - CSIZE * b)) rot
    in () end)
  val _ = case wires of
    NONE => ()
  | SOME {speed, period, wires} => C app wires (fn ((wx, wy), vs) =>
    TextIO.output (f, String.concat [
      "  <circle cx=\"", realToString (Real.fromInt wx / 2.0),
      "\" cy=\"", realToString (Real.fromInt wy / 2.0),
      "\" r=\".11\" style=\"stroke-width: .01; stroke: black\">\n",
      "    <animate attributeName=\"fill\"",
      " values=\"", String.concatWith ";" (map fst vs), "\"",
      " dur=\"", realToString (period / speed), "s\" keyTimes=\"",
      String.concatWith ";" (map (fn (_, r) => realToString (Real.fromInt r / period)) vs),
      "\" repeatCount=\"indefinite\" />\n",
      "  </circle>\n"]))
  val _ = TextIO.output (f,"</svg>\n")
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
  val red = (0.15, 0.1)
  val blue = (~0.1, ~0.2)
  fun oklab (a, b) (i, j) = String.concat [
    "oklab(", realToString (0.6 + 0.2 * Real.fromInt i),
    " ", realToString a,
    " ", realToString (b + 0.1 * Real.fromInt j), ")"]
  val wires = C map (Redblackmap.listItems wires) $ apsnd (trim o (fn
    Regular (n, Cell p) =>
    reg ("#ccc", oklab red p, "#ccc", oklab blue p) n
  | Regular (n, v) =>
      if v = nextCell then reg ("#ccc", oklab blue (0,0), "#ccc", oklab red (0,0)) n
      else reg ("#ccc", "purple", "#ccc", "green") n
  | Exact (n, v) => let
    val (off, on, off', on') = case v of
      Clock => ("white", "black", "white", "black")
    | NotClock => ("black", "white", "black", "white")
    | ThisCell => (oklab blue (0,0), oklab red (0,0), oklab red (0,0), oklab blue (0,0))
    | ThisCellClock => ("white", oklab red (0,0), "white", oklab blue (0,0))
    | ThisCellNotClock => (oklab blue (0,0), "white", oklab red (0,0), "black")
    in clock (off, on, off', on') (n + offset) end))
  val w = {period = Real.fromInt dur, speed = speed, wires = wires}
  in diag_to_svg (SOME w) filename end

val _ = diag_to_svg NONE "diag.svg";
val _ = diag_to_svg_with_wires {speed = 25.0, fade = 4, offset = ~4} "propagation.svg";

val _ = export_theory();
