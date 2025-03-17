signature gol_simLib =
sig

include Abbrev

datatype bexp = False
              | True
              | Var of int * int
              | Not of bexp
              | And of bexp * bexp
              | Or of bexp * bexp

val eval_bexp: bexp -> (int * int -> bool) -> bool

datatype dir = N | S | W | E

val dirToXY: dir -> int * int
val dirToRot: dir -> int

type io_port = (int * int) * dir * bexp

type gate = {
  filename : string,
  stems : string list,
  inputs : io_port list,
  outputs : io_port list,
  height : int,
  width : int
}

type state
type loaded_gate = {
  inputs: io_port list,
  outputs: io_port list,
  height: int,
  width: int,
  grid: unit -> bexp array array
}
val load: gate -> loaded_gate
val prepare: loaded_gate -> state
val rotate: int -> loaded_gate -> loaded_gate
val run_to_fixpoint: state ->
  { inputs: io_port list,
    outputs: io_port list,
    grid: bexp vector vector }

val for_loop: int -> int -> (int -> unit) -> unit
val rotate_dir: dir -> dir
val inc: bexp -> bexp
val is_ew: io_port -> bool
val is_ns: io_port -> bool

val make_abbrev: string -> term -> thm

val and_en_e: gate
val and_es_e: gate
val and_ew_n: gate
val or_en_e: gate
val not_e_e: gate
val half_adder_ee_es: gate
val half_adder_ee_ee: gate
val turn_e_s: gate
val turn_e_n: gate
val fast_turn_e_s: gate
val slow_turn_e_s: gate
val fork_e_es: gate
val fork_e_en: gate
val wire_e_e: gate
val cross_es_es: gate
val slow_wire_e_e: gate
val slower_wire_e_e: gate
val terminator_e: gate
val gates: gate list

end;
