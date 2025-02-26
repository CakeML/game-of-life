signature gol_simSyntax =
sig
  include Abbrev

  val A_tm: term
  val B_tm: term
  val N_tm: term
  val E_tm: term
  val S_tm: term
  val W_tm: term
  val bexp_ty: hol_type
  val True_tm: term
  val False_tm: term
  val Var_tm: term
  val Not_tm: term
  val And_tm: term
  val Or_tm: term
  val Nil_tm: term
  val Cell_tm: term
  val Falses_tm: term

  val dest_Var: term -> term * term
  val dest_Not: term -> term
  val dest_And: term -> term * term
  val dest_Or: term -> term * term
end
