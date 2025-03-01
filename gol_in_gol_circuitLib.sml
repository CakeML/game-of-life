structure gol_in_gol_circuitLib :> gol_in_gol_circuitLib =
struct
open HolKernel bossLib boolLib
open Abbrev gol_simLib gol_diagramLib
open sortingTheory gol_in_gol_circuit2Theory listTheory pairSyntax
     gol_simSyntax listSyntax

val int2cmp = pair_compare (Int.compare, Int.compare)
val int3cmp = pair_compare (int2cmp, Int.compare)

datatype rvalue =
    Cell of int * int
  | RAnd of rvalue * rvalue
  | ROr of rvalue * rvalue
  | RNot of rvalue
  | RXor of rvalue * rvalue

datatype evalue =
    Clock
  | NotClock
  | ThisCell
  | ThisCellClock
  | ThisCellNotClock

datatype value = Regular of int * rvalue | Exact of int * evalue

fun mk_ROr p = case p of
    (RAnd (a1, ROr (RAnd (a2, RNot b1), RAnd (RNot a3, RAnd (b2, RNot b3)))),
     RAnd (RNot a4, ROr (a5, b4))) =>
    if (a1,a1,a1,a1,b1,b1,b1)=(a2,a3,a4,a5,b2,b3,b4) then RXor (a1, b1)
    else ROr p
  | _ => ROr p

fun delay d (Regular (d', v)) = Regular (d + d', v)
  | delay d (Exact (d', v)) = Exact (d + d', v)

val nextCell = let
  val e1 = RXor (Cell (0, 1), Cell (~1, 1))
  val e2 = RXor (Cell (1, 0), Cell (1, 1))
  val e3 = RXor (Cell (0, ~1), Cell (1, ~1))
  val e4 = RXor (Cell (~1, 0), Cell (~1, ~1))
  val e5 = RAnd (Cell (0, 1), Cell (~1, 1))
  val e6 = RAnd (Cell (0, ~1), Cell (1, ~1))
  val e7 = RAnd (Cell (~1, 0), Cell (~1, ~1))
  val e8 = RAnd (Cell (1, 0), Cell (1, 1))
  val e9 = (e1, RXor (e2, RXor (e3, e4)))
  val e10 = ROr (RAnd (e2, RXor (e3, e4)), e8)
  val e11 = ROr (RAnd e9, e5)
  val e12 = (ROr (RAnd (e3, e4), e6), e7)
  val e13 = (e11, RXor (e10, RXor e12))
  in
    RAnd (ROr (Cell (0, 0), RXor e9), RAnd (RXor e13,
      RNot (ROr (RAnd e13, ROr (RAnd (e10, RXor e12), RAnd e12)))))
  end

type io_port = (int * int) * dir * value

fun wpos ((x,y),(a,b)) = (2*x+a, 2*y+b)

type 'a log = {
  newIn: 'a * (int * int) * int * (int * value) vector -> unit,
  newGate: 'a * (int * int) * int -> unit,
  gateKey: gate * int * loaded_gate -> 'a,
  teleport: teleport -> unit
}
val nolog = { gateKey = K (), newGate = K (), newIn = K (), teleport = K () }

type wires = (int * int, value) Redblackmap.dict
type params = {period: int, pulse: int, asserts: io_port list}
fun build (gates, teleport) ({period, pulse, asserts}:params) (log:'a log) = let
  val gateData = ref (Redblackmap.mkDict String.compare)
  fun getGateData (gate, i) = let
    val key = List.nth (#stems gate, i)
    in
      (key, case Redblackmap.peek (!gateData, key) of
        SOME v => v
      | NONE => let
        val res as {inputs, outputs, ...} = gol_simLib.rotate i (load gate)
        val value = (#gateKey log (gate, i, res),
          case (#stems gate, (inputs, outputs)) of
            ("cross_es_es" :: _,
              ([(a1,a2,Var(_,a3)),(b1,b2,Var(_,b3))],
              [(o1,o2,Var(_,o3)),(p1,p2,Var(_,p3))])) =>
              [([(a1,a2,Var(0,a3))],[(o1,o2,Var(0,o3))]),
              ([(b1,b2,Var(0,b3))],[(p1,p2,Var(0,p3))])]
          | (_, v) => [v])
        in gateData := Redblackmap.insert (!gateData, key, value); value end)
    end
  datatype target = Gate of (int * int) * int | Teleport of dir
  val wireIn = ref $ foldl
    (fn ((win, d), map) => Redblackmap.insert (map, win, Teleport d))
    (Redblackmap.mkDict int2cmp) teleport
  val gates = ref (foldl
    (fn ((p, gate), map) => let
      val (g, (a, ls)) = getGateData gate
      in #2 $ foldl
        (fn (data, (i, map)) => (
          C app (#1 data) (fn (x, _, _) =>
            wireIn := Redblackmap.insert (!wireIn,
              wpos (p, x), Gate (p, i)));
          (i+1, Redblackmap.insert (map, (p, i), (ref false, a, data)))))
        (0, map) ls end)
    (Redblackmap.mkDict int3cmp) gates)
  val queue = ref []
  val wires = ref (Redblackmap.mkDict int2cmp)
  fun isMissingWire p port = not (Redblackmap.inDomain (!wires, wpos (p, #1 port)))
  fun runGate (missing, (p,i), g, ins, outs) deep = let
    val ins = Vector.fromList $ C map ins (fn
        (x, _, Var (_, delay)) => (delay, Redblackmap.find (!wires, wpos (p, x)))
      | _ => raise Match)
    val _ = if deep then #newGate log (g, p, i) else #newIn log (g, p, i, ins)
    fun evalExp (Var (i, d')) = let
        val (d, value) = Vector.sub (ins, i)
        in delay (d - d') value end
      | evalExp (Or (e1, e2)) = (case (evalExp e1, evalExp e2) of
          (Regular (d1, v1), Regular (d2, v2)) =>
          Regular (Int.max (d1, d2), mk_ROr (v1, v2))
        | (Exact (d1, ThisCell), Regular (d2, v2)) =>
          Regular (Int.max (d1, d2), mk_ROr (Cell (0, 0), v2))
        | (Exact (d1, ThisCellClock), Exact (d2, ThisCellNotClock)) => (
          if d1 = d2 then () else (PolyML.print ("clock timing 1", d2, d1); ());
          Exact (d1, ThisCell))
        | r => (PolyML.print (ins, Or (e1, e2), r); raise Fail "evalExp Or"))
      | evalExp (And (e1, e2)) = (case (evalExp e1, evalExp e2) of
          (Regular (d1, v1), Regular (d2, v2)) =>
          Regular (Int.max (d1, d2), RAnd (v1, v2))
        | (Exact (d1, ThisCell), Exact (d2, NotClock)) => (
          if d2 <= d1 andalso d1 <= d2+pulse then () else
            (PolyML.print ("clock timing 2", d2, d1, d2+pulse); ());
          Exact (d2, ThisCellNotClock))
        | (Exact (d1, Clock), Regular (d2, v2)) => (
          if v2 = nextCell then () else (PolyML.print "calculated wrong function"; ());
          if d2 <= d1 + period andalso d1 <= ~pulse then () else
            (PolyML.print ("clock timing 3", d2-period, d1, d1+pulse, 0); ());
          Exact (d1, ThisCellClock))
        | r => (PolyML.print (ins, And (e1, e2), r); raise Fail "evalExp And"))
      | evalExp (Not e1) = (case evalExp e1 of
          Regular (d1, v1) => Regular (d1, RNot v1)
        | Exact (d1, Clock) => Exact (d1, NotClock)
        | _ => raise Fail "evalExp Not")
      | evalExp bv = (PolyML.print (ins, bv); raise Fail "evalExp other")
    in
      app (fn (x, d, bv) =>
        processWire (wpos (p, x), evalExp bv) (if deep then 2 else 0)) outs
    end
  and processQueue (missing, (p,i), r, g, ins, outs) depth =
    if !r then true else
    if depth = 0 then (queue := (missing, (p,i), r, g, ins, outs) :: !queue; false) else
    case filter (isMissingWire p) missing of
      [] => (r := true; runGate (missing, (p,i), g, ins, outs) (depth > 1); true)
    | missing => (queue := (missing, (p,i), r, g, ins, outs) :: !queue; false)
  and processWire (w, value) depth =
    case Redblackmap.peek (!wires, w) of
      SOME old => (case (value, old) of
        (Exact (n1, Clock), Exact (n2, Clock)) =>
          if n1 = n2 + period then () else
          (PolyML.print ("clock period mismatch", period, n1 - n2); ())
      | (Exact (n1, ThisCell), Exact (n2, ThisCell)) =>
        if n1 = n2 then () else
          (PolyML.print ("thiscell mismatch", n1, n2); ())
      | (e1, e2) => if e1 = e2 then () else
          (PolyML.print ("cycle mismatch", w, value, old); ()))
    | NONE => let
      val (wireIn', tgt) = Redblackmap.remove (!wireIn, w)
      val _ = wireIn := wireIn'
      val _ = wires := Redblackmap.insert (!wires, w, value)
      in
        case tgt of
          Gate p => let
          val (r, g, (ins, outs)) = Redblackmap.find (!gates, p)
          in (processQueue (ins, p, r, g, ins, outs) depth; ()) end
        | Teleport dir => let
          val (a,b) = dirToXY dir
          val wout = (fst w - 2*CSIZE*a, snd w - 2*CSIZE*b)
          val (d, (x, y)) = case value of
              Regular (d, Cell p) => (d, p)
            | Exact (d, ThisCell) => (
              if 0 <= d then () else (PolyML.print ("exact signal too early", d); ());
              (d, (0, 0)))
            | _ => raise Fail "bad signal on teleport"
          val _ = #teleport log (w, dir)
          in processWire (wout, Regular (d, Cell (x - a, y - b))) depth end
      end
  val _ = app (fn (w,d,v) => processWire (wpos (w, dirToXY d), v) 1) asserts
  fun loop () = case !queue of
    [] => ()
  | q =>
    if foldl (fn (x, r) => processQueue x 2 orelse r) (queue := []; false) q then
      loop ()
    else raise Fail "queue stuck"
  val _ = loop ()
  (* val (header, lines) = d
  val lines' = Vector.tabulate (SIZE, fn y => let
    val (left, right) = lineHeader (Vector.sub (lines, y))
    val body = List.tabulate (SIZE, fn x =>
      case coord d (x, y) of
        w as Wire _ =>
        if Redblackmap.inDomain (!wires, (x-1, y-1)) then "* " else ". "
      | w =>
        if List.exists ((fn (a,b) => (x, y) = (2*a+1,2*b+1)) o #1 o #2) (!queue) then
          "% "
        else
          (* "+ " *)
        sigil_to_string w
        )
    in left ^ String.concat body ^ right end)
  val _ = print' (header, lines') *)
  in !wires end

fun getWire res p dir = Redblackmap.find (res, wpos (p, dirToXY dir))

local

val Cell_tm  = prim_mk_const {Name = "Cell",  Thy = "gol_in_gol_circuit2"}
val RAnd_tm  = prim_mk_const {Name = "RAnd",  Thy = "gol_in_gol_circuit2"}
val ROr_tm   = prim_mk_const {Name = "ROr",   Thy = "gol_in_gol_circuit2"}
val RNot_tm  = prim_mk_const {Name = "RNot",  Thy = "gol_in_gol_circuit2"}
val RXor_tm  = prim_mk_const {Name = "RXor",  Thy = "gol_in_gol_circuit2"}

val Clock_tm    = prim_mk_const {Name = "Clock",    Thy = "gol_in_gol_circuit2"}
val NotClock_tm = prim_mk_const {Name = "NotClock", Thy = "gol_in_gol_circuit2"}
val ThisCell_tm = prim_mk_const {Name = "ThisCell", Thy = "gol_in_gol_circuit2"}
val ThisCellClock_tm =
  prim_mk_const {Name = "ThisCellClock", Thy = "gol_in_gol_circuit2"}
val ThisCellNotClock_tm =
  prim_mk_const {Name = "ThisCellNotClock", Thy = "gol_in_gol_circuit2"}

val Reg_tm   = prim_mk_const {Name = "Reg",   Thy = "gol_in_gol_circuit2"}
val Exact_tm = prim_mk_const {Name = "Exact", Thy = "gol_in_gol_circuit2"}

fun ERR x = mk_HOL_ERR "gol_in_gol_circuitLib" x ""

in

val from_int = intSyntax.term_of_int o Arbint.fromInt

fun tr_rvalue (Cell p)  = mk_binop Cell_tm $ pair_map from_int p
  | tr_rvalue (RNot v)  = mk_monop RNot_tm $ tr_rvalue v
  | tr_rvalue (RAnd vs) = mk_binop RAnd_tm $ pair_map tr_rvalue vs
  | tr_rvalue (ROr vs)  = mk_binop ROr_tm $ pair_map tr_rvalue vs
  | tr_rvalue (RXor vs) = mk_binop ROr_tm $ pair_map tr_rvalue vs

fun tr_evalue Clock = Clock_tm
  | tr_evalue NotClock = NotClock_tm
  | tr_evalue ThisCell = ThisCell_tm
  | tr_evalue ThisCellClock = ThisCellClock_tm
  | tr_evalue ThisCellNotClock = ThisCellNotClock_tm

fun tr_value (Regular (n, v)) = mk_binop Reg_tm (numSyntax.term_of_int n, tr_rvalue v)
  | tr_value (Exact (n, v)) = mk_binop Exact_tm (from_int n, tr_evalue v)

end

fun pull_perm1 f ls = let
  val (a, ls') = listSyntax.dest_cons ls
  in
    if f a then ISPEC ls PERM_REFL
    else SPEC a (MATCH_MP pull_perm1_tl (pull_perm1 f ls'))
  end

fun pull_perm [] ls = ISPEC ls pull_perm_nil
  | pull_perm (f::l) ls = let
    val th = pull_perm1 f ls
    val ls' = rand $ rand $ concl th
    in MATCH_MP pull_perm_cons $ CONJ th (pull_perm l ls') end

val (append_nil, append_cons) = CONJ_PAIR APPEND_def
fun append_conv tm =
  ((REWR_CONV append_cons THENC RAND_CONV append_conv) ORELSEC REWR_CONV append_nil) tm

fun floodfill diag params = let
  datatype gate_kind = Regular of thm | Crossover of thm list
  fun gateKey ((gate, i, lgate): gate * int * loaded_gate) = let
    val g = List.nth (#stems gate, i)
    val g0 = List.nth (#stems gate, 0)
    val genth = g ^ "_gate_gen"
    val thm = fetch "gol_gates" (g ^ "_thm")
    val res = if g0 = "cross_es_es" then let
      val thm1 = MATCH_MP blist_simulation_ok_imp_crossover thm
      val thm2 = MATCH_MP crossover_symm thm1
      in Crossover [save_thm (genth, thm1), save_thm (genth^"_rev", thm2)] end
    else let
      val (ins, outs) = apfst rand $ dest_comb $ rator $ concl thm
      val (ins', outs') =
        pair_map (map (apsnd dest_pair o dest_pair) o fst o dest_list) (ins, outs)
      val vars = List.take ([``a:value``, ``b:value``], length ins')
      val env = map2 (fn (_,(_,d)) => fn a => (snd (dest_Var d), a)) ins' vars
      val env = case env of
          [(da, a)] => [da, da, a, a]
        | [(da, a), (db, b)] => [da, db, a, b]
        | _ => raise Match
      val thm = SPECL env (MATCH_MP blist_simulation_ok_imp_gate thm)
      val thm = CONV_RULE (RATOR_CONV (BINOP_CONV (EVAL THENC SCONV []))) thm
      val thm = case g0 of
          "half_adder_ee_ee" => MATCH_MP half_adder_weaken thm
        | "half_adder_ee_es" => MATCH_MP half_adder_weaken thm
        | _ => thm
      in Regular (save_thm (genth, GENL vars thm)) end
    in (lgate, genth, res) end
  val thm = ref floodfill_start
  fun newIn ((_, s, g), (x', y'), _, ins) = let
    val gth = case g of Regular g => g | _ => raise Match
    val gth = SPECL (Vector.foldr (fn ((_, v), r) => tr_value v :: r) [] ins) gth
    val thm' = MATCH_MP floodfill_add_ins (CONJ (!thm) gth)
    val (x, y) = pair_map from_int (2*x', 2*y')
    val (x', y') = pair_map numSyntax.term_of_int (x', y')
    val thm' = SPECL [x, y, x', y'] thm'
    val thm' = SRULE [] $ MATCH_MP thm' $ EQT_ELIM $ EVAL $ lhand $ concl thm'
    in thm := thm' end
  fun newGate ((lg:loaded_gate, s, g), (x', y'), i) = let
    val (x, y) = (2*x', 2*y')
    val ins = map (mk_pair o pair_map from_int o (fn ((a,b),_,_) => (x+a, y+b))) (#inputs lg)
    val thm' = case g of
      Regular gth => let
      val permth = pull_perm
        (map (fn a => term_eq a o fst o dest_pair o fst o dest_pair) ins)
        (lhand $ rator $ concl (!thm))
      val del = fst $ dest_list $ lhand $ rand $ concl permth
      val gth = SPECL (map (snd o dest_pair) del) gth
      val thm' = case (#width lg, #height lg) of
        (1, 1) => let
        val thm' = floodfill_add_small_gate
        val thm' = MATCH_MP thm' $ CONJ (!thm) $ CONJ gth permth
        val (x, y) = pair_map from_int (x, y)
        val (x', y') = pair_map numSyntax.term_of_int (x', y')
        val thm' = SPECL [x, y, x', y'] thm'
        val thm' = MATCH_MP thm' $ EQT_ELIM $ SCONV [] $ lhand $ concl thm'
        val thm' = CONV_RULE (RATOR_CONV $ LAND_CONV (LAND_CONV EVAL THENC append_conv)) thm'
        in thm' end
      | (2, 2) => let
        val thm' = floodfill_add_gate
        val thm' = MATCH_MP thm' $ CONJ (!thm) $ CONJ gth permth
        val (x, y) = pair_map from_int (x, y)
        val (x', y') = pair_map numSyntax.term_of_int (x', y')
        val thm' = SPECL [x, y, x', y'] thm'
        val conv = RAND_CONV (REWR_CONV make_area_2_2) THENC SCONV []
        val thm' = MATCH_MP thm' $ EQT_ELIM $ conv $ lhand $ concl thm'
        fun conv c = LAND_CONV c THENC append_conv
        val thm' = CONV_RULE (RATOR_CONV $ RATOR_CONV $
          COMB2_CONV (LAND_CONV (conv EVAL), conv (SCONV [v_xor_def]))) thm'
        in thm' end
      | _ => raise Match
      in thm' end
    | Crossover gths => let
      val (x, y) = (2*x', 2*y')
      val ins = map (mk_pair o pair_map from_int o (fn ((a,b),_,_) => (x+a, y+b))) (#inputs lg)
      val inp = List.nth (ins, i)
      val f1 = term_eq inp o fst o dest_pair
      val f2 = f1 o fst o dest_pair
      val (outs, crosses) = apfst rand $ dest_comb $ rator $ concl (!thm)
      val (first, permth) = (false, pull_perm1 f1 crosses) handle _ => (true, pull_perm1 f2 outs)
      val (conv, thm') = if first then let
        val gth = List.nth (gths, i)
        val thm' = MATCH_MP floodfill_add_crossover $ CONJ (!thm) $ CONJ gth permth
        val (x, y) = pair_map from_int (x, y)
        val (x', y') = pair_map numSyntax.term_of_int (x', y')
        val thm' = SPECL [x, y, x', y'] thm'
        val thm' = MATCH_MP thm' $ EQT_ELIM $ SCONV [] $ lhand $ concl thm'
        in (BINOP_CONV, thm') end
      else let
        val permth2 = pull_perm1 f2 outs
        val thm' = MATCH_MP floodfill_finish_crossover $ CONJ (!thm) $ CONJ permth2 permth
        in (LAND_CONV, thm') end
      in CONV_RULE (RATOR_CONV $ conv $ LAND_CONV (SCONV [])) thm' end
    in thm := thm' end
  fun teleport ((ix, iy), d) = let
    val inp = mk_pair $ pair_map from_int (ix, iy)
    val f = term_eq inp o fst o dest_pair o fst o dest_pair
    val (outs, crosses) = apfst rand $ dest_comb $ rator $ concl (!thm)
    val permth = pull_perm1 f outs
    val thm' = MATCH_MP floodfill_teleport $ CONJ (!thm) permth
    val (dx, dy) = dirToXY d
    val thm' = SPECL [from_int (~dx), from_int (~dy)] thm'
    val thm' = CONV_RULE (RATOR_CONV $ LAND_CONV $ LAND_CONV (SCONV [v_teleport_def])) thm'
    in thm := thm' end
  val _ = build (recognize diag) params
    {gateKey = gateKey, newGate = newGate, newIn = newIn, teleport = teleport}
  val thm = CONV_RULE (COMB2_CONV (LAND_CONV (SCONV []), make_abbrev "main_circuit")) (!thm)
  val (f, args) = strip_comb (concl thm)
  val x = mk_var ("area", type_of (hd args))
  in EXISTS (boolSyntax.mk_exists (x, list_mk_comb (f, x :: tl args)), hd args) thm end

end
