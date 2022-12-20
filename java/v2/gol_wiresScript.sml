open HolKernel Parse boolLib bossLib;

val _ = new_theory "gol_wires";

fun read_file filename = let
  val f = TextIO.openIn filename
  fun loop aux =
    case TextIO.inputLine(f) of
      NONE => List.rev aux
    | SOME line => loop (line :: aux)
  val lines = loop []
  val _ = TextIO.closeIn(f)
  in lines end

val filename = "lwss-and-ns-w.rle.txt"
val filename = "lwss-wire-e-e.rle.txt"

val xs = read_file filename
fun part p xs = let
  fun partition_at p [] aux res = if null aux then rev res else rev (rev aux :: res)
    | partition_at p (x::xs) aux res =
        if p x then
          partition_at p xs [] (if null aux then res else rev aux :: res)
        else
          partition_at p xs (x::aux) res
  in partition_at p xs [] [] end
val ps = part (fn s => String.isPrefix "GOL" s orelse String.isPrefix "End" s) xs
fun parse_bool_str s = Term [QUOTE (s ^ ":bool")]
fun parse_line l = let
  val rs = String.tokens (fn c => c = #":") l
  val p = hd rs
  val t = hd (tl rs)
  val tm = parse_bool_str t
  val rs = String.tokens (fn c => mem c [#",",#")",#"("]) p
  val x = rs |> el 1 |> string_to_int
  val y = rs |> el 2 |> string_to_int
  in ((x,y),tm) end
val data = map (map parse_line) ps

val d = hd data

  fun mk_int i = intSyntax.term_of_int (Arbint.fromInt i)
  fun mk_pair f g (x,y) = pairSyntax.mk_pair(f x, g y)
  fun mk_iib_list xs = listSyntax.mk_list(xs,“:(int # int) # bool”)

(*

  map (mk_pair (mk_pair mk_int mk_int) I) d |> mk_iib_list

*)

val _ = export_theory();
