signature gol_diagramLib =
sig
  type dir = gol_simLib.dir
  type gate = gol_simLib.gate

  val tile: int
  val tile2: int

  datatype small_gate = AndG | Node | NotG | OrG | SlowNode
  datatype large_gate = HalfAddG | SlowWire

  datatype sigil =
    Empty
  | Large of large_gate
  | Small of small_gate
  | Wall of bool
  | Wire of gol_simLib.dir

  type diag = string * string vector
  type gates = ((int * int) * (gate * int)) list
  type teleport = (int * int) * dir

  val coord: diag -> int * int -> sigil
  val lineHeader: string -> string * string
  val neighbors:
      diag -> int * int -> sigil * (sigil * sigil * sigil * sigil)
  val parse: 'a frag list -> diag
  val print_diag: diag -> unit
  val recognize: diag -> gates * teleport list
  val rotate_diag: diag -> string * string vector
  val rotate_sigil: sigil -> sigil
  type sigils = sigil * sigil * sigil * sigil
  val rotate_sigils: sigils -> sigils
  type sigils22 = sigils * sigils * sigils * sigils
  val rotate_sigils22: sigils22 -> sigils22
  type sigils31 = bool * sigils * sigils * sigils
  val rotate_sigils31: sigils31 -> sigils31
  val sigil_to_string: sigil -> string
  val smallNodePattern:
      small_gate -> (gol_simLib.gate * (sigils)) list

end
