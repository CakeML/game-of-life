structure gol_simSyntax :> gol_simSyntax =
struct
open Abbrev HolKernel bossLib boolLib Parse gol_simTheory

val A_tm  = prim_mk_const {Name = "A",  Thy = "gol_sim"}
val B_tm  = prim_mk_const {Name = "B",  Thy = "gol_sim"}
val N_tm  = prim_mk_const {Name = "N",  Thy = "gol_circuit"}
val E_tm  = prim_mk_const {Name = "E",  Thy = "gol_circuit"}
val S_tm  = prim_mk_const {Name = "S",  Thy = "gol_circuit"}
val W_tm  = prim_mk_const {Name = "W",  Thy = "gol_circuit"}
val true_tm  = prim_mk_const {Name = "True",  Thy = "gol_sim"}
val false_tm = prim_mk_const {Name = "False", Thy = "gol_sim"}
val var_tm   = prim_mk_const {Name = "Var", Thy = "gol_sim"}
val not_tm   = prim_mk_const {Name = "Not", Thy = "gol_sim"}
val and_tm   = prim_mk_const {Name = "And", Thy = "gol_sim"}
val or_tm    = prim_mk_const {Name = "Or",  Thy = "gol_sim"}
val Nil_tm = prim_mk_const {Name = "Nil", Thy = "gol_sim"}
val Cell_tm = prim_mk_const {Name = "Cell", Thy = "gol_sim"}
val Falses_tm = prim_mk_const {Name = "Falses", Thy = "gol_sim"}

val bexp_ty = ``:bexp``

fun ERR x = mk_HOL_ERR "gol_simSyntax" x ""

val dest_and = dest_binop and_tm (ERR "dest_and")
val dest_or = dest_binop or_tm (ERR "dest_or")
val dest_var = dest_binop var_tm (ERR "dest_var")
val dest_not = dest_monop not_tm (ERR "dest_not")

end
