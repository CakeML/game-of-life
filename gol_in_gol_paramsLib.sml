structure gol_in_gol_paramsLib =
struct
local open gol_simLib gol_diagramLib in

datatype rvalue =
    Cell of int * int
  | RAnd of rvalue * rvalue
  | ROr of rvalue * rvalue
  | RNot of rvalue
  | RXor of rvalue * rvalue

datatype evalue =
    Clock
  | NotClock
  | ThisCell
  | ThisCellClock
  | ThisCellNotClock

datatype value = Regular of int * rvalue | Exact of int * evalue

Quote diag = gol_diagramLib.parse:
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
         ^   ^                                                               v   v         |
 0   o > o > o > o > o > o > o > o > o > s > s > s > s > s > s > s > o > o > o > o > o   0 |
     ^   ^   ^                       v                                       v   v   v     |
 1 > o > o > o > H - H > o > o > o > o > o > o > o > o > o   o > o > o > o > o > o > o > 1 |
     ^   ^       |   |               v                   v   ^               v   v   v     |
 2 > o > o > o > H - H > o > o > o > o > o > o > o > o > o > o > o > o       o   o > o > 2 |
     ^   ^                           v                   v   ^       v       v   v   v     |
 3   o   o           o > O > A > o > o > o > o           o   o       o       H - H   s   3 |
     ^   ^           ^   ^   ^       v       v           v   ^       v       |   |   v     |
 4   o   o   o > A > o > o > o       o   s > A > O > o > o > o > o   o   o < H - H   s   4 |
     ^   ^   ^   ^   ^   ^           v   ^       ^   v   v       v   v   v       v   v     |
 5   o   o   o   N   o   o           o > o > N > A < o   o > o > o > o > o > o   o   s   5 |
     ^   ^   ^   ^   ^   ^                                       v   v   v   v   v   v     |
 6   o   o < o < o < o < o < o < o < o < o < o < o < o < o < o < o   o   o   H - H   s   6 |
     ^       ^   ^       ^                                   v   v   v   v   |   |   v     |
 7   o   o > o > o > o > o   o < o < o < o < o < o < o < o < o   o   o   o   H - H   s   7 |
     ^   ^   ^   ^                                           v   v   v   v   v   v   v     |
 8   o   o   o   O < o < o   o < o < o < o < o < o < o < o < o   o   o   o > O   o   s   8 |
     ^   ^   ^   ^       ^                                   v   v   v       v   v   v     |
 9   s   o   H - H       o   o < o < o < o < o < o < o < o < o   o   o > o   o   o   s   9 |
     ^   ^   |   |       ^                                   v   v       v   v   v   v     |
10   s   o   H - H       o   o < o < o < o < o < o < o < o < o   o       H - H   o   s   10|
     ^   ^   ^   ^       ^                                   v   v       |   |   v   v     |
11   s   o   o   o < o   o   o < o < o < o < o < o < o < o < o   o       H - H   o   s   11|
     ^   ^   ^       ^   ^                                   v   v       v   v   v   v     |
12   s   o   O < o   o   o   o < o < o < o < o < o < o < o < o   o > o   o   o   o   s   12|
     ^   ^   ^   ^   ^   ^                                   v       v   v   v   v   v     |
13   s   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o < o < o < o < o   s   13|
     ^   |   |   ^   ^   ^                                   v   v   v   v   v       v     |
14   s   H - H   o   o   o   o < o < o < o < o < o < o < o < o   o   o > o > o > o   s   14|
     ^   ^   ^   ^   ^   ^   v                                   v       v   v   v   v     |
15   s   o   o < o < o < o < o < o   o < o < o < o < o < o < o < o < o < o   o   o   s   15|
     ^   ^       ^   ^   ^   v   ^   v                           v           v   v   v     |
16   s   H - H > o   o   o   o   o   o           o < o < o < o < o < o < o < o   o   s   16|
     ^   |   |       ^   ^   v   ^   v           v               v               v   v     |
17   s   H - H       o   o < o < o < O < H - H < o   o < o < o < o < o           o   s   17|
     ^   ^   ^       ^       v   ^       |   |       v           v   ^           v   v     |
18 < o < o   o       o < o < o < o < o < H - H < o < O < H - H < o   H - H < o < o < o < 18|
     ^   ^   ^               v   ^                       |   |       |   |       v   v     |
19 < o < o < o < o < o < o < o   o < o < o < o < o < o < H - H < o < H - H < o < o < o < 19|
     ^   ^   ^                                                               v   v   v     |
20   o < o < o < s < s < s < s < s < s < s < s < s < s < s < s < s < s < s < o < o < o   20|
         ^   ^                                                               v   v         |
     0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20     |
End

val tile = gol_diagramLib.tile
val tile2 = gol_diagramLib.tile2
val period = 586
val pulse = 22

val params = {
  period = period,
  pulse = pulse,
  asserts = [((6, 0), E, Exact (~77, Clock)), ((11, 4), E, Exact (~15, ThisCell))],
  weaken = [((14, 4), E), ((14, 4), N)]
}

val periodN = numSyntax.term_of_int period
val tileN = numSyntax.term_of_int tile
val periodZ = intSyntax.term_of_int (Arbint.fromInt period)
val pulseZ = intSyntax.term_of_int (Arbint.fromInt pulse)
val tileZ = intSyntax.term_of_int (Arbint.fromInt tile)
val tile2Z = intSyntax.term_of_int (Arbint.fromInt tile2)

val nextCell = let
  val e1 = RXor (Cell (0, 1), Cell (~1, 1))
  val e2 = RXor (Cell (1, 0), Cell (1, 1))
  val e3 = RXor (Cell (0, ~1), Cell (1, ~1))
  val e4 = RXor (Cell (~1, 0), Cell (~1, ~1))
  val e5 = RAnd (Cell (0, 1), Cell (~1, 1))
  val e6 = RAnd (Cell (0, ~1), Cell (1, ~1))
  val e7 = RAnd (Cell (~1, 0), Cell (~1, ~1))
  val e8 = RAnd (Cell (1, 0), Cell (1, 1))
  val e9 = (e1, RXor (e2, RXor (e3, e4)))
  val e10 = ROr (RAnd (e2, RXor (e3, e4)), e8)
  val e11 = ROr (RAnd e9, e5)
  val e12 = (ROr (RAnd (e3, e4), e6), e7)
  val e13 = (e11, RXor (e10, RXor e12))
  in
    RAnd (ROr (Cell (0, 0), RXor e9), RAnd (RXor e13,
      RNot (ROr (RAnd e13, ROr (RAnd (e10, RXor e12), RAnd e12)))))
  end

end
end
