structure gol_simSyntax :> gol_simSyntax =
struct
open Abbrev HolKernel bossLib boolLib Parse gol_simTheory

val A_tm  = prim_mk_const {Name = "A",  Thy = "gol_sim"}
val B_tm  = prim_mk_const {Name = "B",  Thy = "gol_sim"}
val N_tm  = prim_mk_const {Name = "N",  Thy = "gol_circuit"}
val E_tm  = prim_mk_const {Name = "E",  Thy = "gol_circuit"}
val S_tm  = prim_mk_const {Name = "S",  Thy = "gol_circuit"}
val W_tm  = prim_mk_const {Name = "W",  Thy = "gol_circuit"}
val True_tm  = prim_mk_const {Name = "True",  Thy = "gol_sim"}
val False_tm = prim_mk_const {Name = "False", Thy = "gol_sim"}
val Var_tm   = prim_mk_const {Name = "Var", Thy = "gol_sim"}
val Not_tm   = prim_mk_const {Name = "Not", Thy = "gol_sim"}
val And_tm   = prim_mk_const {Name = "And", Thy = "gol_sim"}
val Or_tm    = prim_mk_const {Name = "Or",  Thy = "gol_sim"}
val Nil_tm = prim_mk_const {Name = "Nil", Thy = "gol_sim"}
val Cell_tm = prim_mk_const {Name = "Cell", Thy = "gol_sim"}
val Falses_tm = prim_mk_const {Name = "Falses", Thy = "gol_sim"}

val bexp_ty = ``:bexp``

fun ERR x = mk_HOL_ERR "gol_simSyntax" x ""

val dest_And = dest_binop And_tm (ERR "dest_And")
val dest_Or = dest_binop Or_tm (ERR "dest_Or")
val dest_Var = dest_binop Var_tm (ERR "dest_Var")
val dest_Not = dest_monop Not_tm (ERR "dest_Not")

end
