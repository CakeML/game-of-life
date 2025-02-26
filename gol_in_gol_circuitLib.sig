signature gol_in_gol_circuitLib =
sig
  include Abbrev

  datatype rvalue =
    Cell of int * int
  | RAnd of rvalue * rvalue
  | RNot of rvalue
  | ROr of rvalue * rvalue
  | RXor of rvalue * rvalue

  datatype evalue =
      Clock
    | NextCell
    | NotClock
    | ThisCell
    | ThisCellUntilClock of int

  datatype value = Exact of int * evalue | Regular of int * rvalue

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
    teleport: teleport -> unit
  }

  type wires
  val build: gol_diagramLib.gates -> int -> int ->
    io_port list * teleport list -> 'b log -> wires
  val getWire: wires -> int * int -> dir -> value

  val floodfill: gol_diagramLib.diag -> int -> int ->
    teleport list -> io_port list -> thm
end
