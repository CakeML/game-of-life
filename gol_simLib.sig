signature gol_simLib =
sig

datatype bexp = False
              | True
              | Var of string * int
              | Not of bexp
              | And of bexp * bexp
              | Or of bexp * bexp;

datatype dir = N | S | W | E;

type io_port = (int * int) * dir;

type gate =
  { filename : string ,
    inputs : io_port list ,
    outputs : io_port list ,
    height : int ,
    width : int };

type state

val load: gate -> state

val run_to_fixpoint: state -> bexp vector vector

end;
