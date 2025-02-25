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
  val true_tm: term
  val false_tm: term
  val var_tm: term
  val not_tm: term
  val and_tm: term
  val or_tm: term
  val Nil_tm: term
  val Cell_tm: term
  val Falses_tm: term

  val dest_var: term -> term * term
  val dest_not: term -> term
  val dest_and: term -> term * term
  val dest_or: term -> term * term
end
