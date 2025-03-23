open HolKernel bossLib boolLib Parse;
open cv_transLib arithmeticTheory listTheory ASCIInumbersTheory
     gol_in_gol_circuitTheory;

val _ = new_theory "gol_in_gol_compiler";

Definition from_rle_inner_def:
  from_rle_inner [] count row acc = REVERSE (REVERSE row :: acc) ∧
  from_rle_inner (c::cs) count row acc =
    if isDigit c then
      from_rle_inner cs (count * 10 + (ORD c - ORD #"0")) row acc
    else if c = #"o" then
      from_rle_inner cs 0 (REPLICATE (MAX 1 count) T ++ row) acc
    else if c = #"b" then
      from_rle_inner cs 0 (REPLICATE (MAX 1 count) F ++ row) acc
    else if c = #"$" then
      from_rle_inner cs 0 [] (REPLICATE (count - 1) [] ++ REVERSE row :: acc)
    else if c = #"\n" then
      from_rle_inner cs count row acc
    else REVERSE (REVERSE row :: acc)
End

Definition from_rle_def:
  from_rle s = from_rle_inner s 0 [] []
End

Definition push_rle_def:
  push_rle [] n v = [(n:num,v)] ∧
  push_rle ((m,v)::acc) n v' =
    if v = v' then (n+m,v)::acc else (n,v')::(m,v)::acc
End

Definition to_rle_row_finish_def:
  to_rle_row_finish [] r = r ∧
  to_rle_row_finish ((m,v)::acc) r =
    to_rle_row_finish acc (
      (if m = 1:num then "" else toString m) ++
      (if v then #"o" else #"b") :: r)
End

Definition to_rle_row_def:
  to_rle_row env Nil acc r = to_rle_row_finish acc r ∧
  to_rle_row env (Cell b ls) acc r =
    to_rle_row env ls (push_rle acc 1 (eval env b)) r ∧
  to_rle_row env (Falses n ls) acc r =
    to_rle_row env ls (push_rle acc n F) r
End

Definition rle_fragments_def:
  rle_fragments =
    MAP (λl. (to_rle_row (λ_. F) l [] "", to_rle_row (λ_. T) l [] "")) main_circuit
End

Definition mega_cell_compile_big_row_def:
  mega_cell_compile_big_row [] frag acc = "$\n" :: acc ∧
  mega_cell_compile_big_row (b::row) (fragF, fragT) acc =
  mega_cell_compile_big_row row (fragF, fragT)
    ((if b then fragT else fragF) :: acc)
End

Definition mega_cell_compile_small_rows_def:
  mega_cell_compile_small_rows row [] acc = acc ∧
  mega_cell_compile_small_rows row (frag::ls) acc =
  mega_cell_compile_small_rows row ls (mega_cell_compile_big_row row frag acc)
End

Definition mega_cell_compile_big_rows_def:
  mega_cell_compile_big_rows frags [] acc = acc ∧
  mega_cell_compile_big_rows frags (row::ls) acc =
  mega_cell_compile_big_rows frags ls (mega_cell_compile_small_rows row frags acc)
End

Definition rev_concat_def:
  rev_concat [] acc = acc ∧
  rev_concat (s::l) acc = rev_concat l (s ++ acc)
End

Definition mega_cell_compile_def:
  mega_cell_compile s =
    rev_concat (mega_cell_compile_big_rows rle_fragments (from_rle s) []) "!"
End

Definition digit_def:
  digit n = CHR (48 + (MIN 9 n))
End

val digit_pre_def = cv_trans_pre digit_def;

Theorem digit_pre[cv_pre]:
  digit_pre n
Proof
  rw[digit_pre_def] \\ rw[MIN_DEF]
QED

Theorem MAP_HEX_n2l_10:
  MAP HEX (n2l 10 n) = MAP digit (n2l 10 n)
Proof
  rw[MAP_EQ_f]
  \\ qspec_then`10`mp_tac numposrepTheory.n2l_BOUND
  \\ rw[EVERY_MEM]
  \\ first_x_assum drule
  \\ rw[digit_def, MIN_DEF]
  \\ Cases_on`e = 10` \\ rw[]
  \\ `e < 10` by fs[]
  \\ fs[wordsTheory.NUMERAL_LESS_THM, HEX_def]
QED

val _ = cv_auto_trans numposrepTheory.n2l_n2lA;
val _ = cv_auto_trans (num_to_dec_string_def
  |> SIMP_RULE std_ss [n2s_def, FUN_EQ_THM, MAP_HEX_n2l_10])
val _ = cv_auto_trans mega_cell_compile_def

fun mega_cell_to_file filename s = let
  val f = TextIO.openOut filename
  val th = cv_eval ``mega_cell_compile ^(stringSyntax.fromMLstring s)``
  val _ = TextIO.output(f, stringSyntax.fromHOLstring $ rhs $ concl th)
  in TextIO.closeOut f end

val _ = mega_cell_to_file "mega-glider.rle" "\
    \bob$\
    \bbo$\
    \ooo!";

val _ = export_theory();
