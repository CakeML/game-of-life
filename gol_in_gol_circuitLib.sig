signature gol_in_gol_circuitLib =
sig
  include Abbrev

  type rvalue = gol_in_gol_paramsLib.rvalue
  type evalue = gol_in_gol_paramsLib.evalue
  type value = gol_in_gol_paramsLib.value

  val mk_ROr: rvalue * rvalue -> rvalue
  val delay: int -> value -> value
  val nextCell: rvalue

  val tr_evalue: evalue -> term
  val tr_rvalue: rvalue -> term
  val tr_value: value -> term

  type dir = gol_simLib.dir
  type io_port = (int * int) * dir * value
  type teleport = (int * int) * dir

  type 'a log = {
    newIn: 'a * (int * int) * int * (int * value) vector -> unit,
    newGate: 'a * (int * int) * int -> unit,
    gateKey: gol_simLib.gate * int * gol_simLib.loaded_gate -> 'a,
    teleport: teleport -> unit,
    weaken: (int * int) * value -> unit
  }

  type wires = (int * int, value) Redblackmap.dict
  type params = {period: int, pulse: int, asserts: io_port list, weaken: ((int * int) * dir) list}
  val build: gol_diagramLib.gates * teleport list -> params -> 'b log -> wires
  val nolog: unit log
  val getWire: wires -> int * int -> dir -> value

  val floodfill: gol_diagramLib.diag -> params -> thm

end
