(*
  Definition of four standard interfaces for GOL lwss
*)
open preamble gol_rulesTheory gol_specTheory;

val _ = new_theory "gol_interfaces";

Definition from_strings_def:
  from_strings strs =
    MAP (MAP (λc. if c = #"s" then Sender else
                  if c = #"r" then Receiver else
                  if c = #"." then Shared else
                  if c = #"x" then Signal else ARB)) strs
End

Definition EAST_def:
  EAST = from_strings [
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss.......rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss.x..x..rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss.....x.rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss.x...x.rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss..xxxx.rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss.......rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssss.......rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssssssssrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr"]
  : cell_owner list list
End

Theorem EAST = EVAL “EAST”;

Definition WEST_def:
  WEST = from_strings [
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr.......sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr.......sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr.xxxx..sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr.x...x.sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr.x.....sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr..x..x.sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr.......sssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssssssssssssssssssssssssssssssssss"]
  : cell_owner list list
End

Theorem WEST = EVAL “WEST”;

Definition NORTH_def:
  NORTH = from_strings [
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssssrrrrrrrssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss.......ssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss..xxx..ssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss..x..x.ssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss..x....ssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss..x....ssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss...x.x.ssssssssssssssssssssssssssssssssssss";
    "ssssssssssssssssssssssssssssssss.......ssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss"]
  : cell_owner list list
End

Theorem NORTH = EVAL “NORTH”;

Definition SOUTH_def:
  SOUTH = from_strings [
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss.......sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss.x.x...sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss....x..sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss....x..sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss.x..x..sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss..xxx..sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssss.......sssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "sssssssssssssssssssssssssssssssssssrrrrrrrsssssssssssssssssssssssssssssssss";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr";
    "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr"]
  : cell_owner list list
End

Theorem SOUTH = EVAL “SOUTH”;

Triviality north_ok:
  good_interface NORTH
Proof
  EVAL_TAC
QED

Triviality south_ok:
  good_interface SOUTH
Proof
  EVAL_TAC
QED

Triviality east_ok:
  good_interface EAST
Proof
  EVAL_TAC
QED

Triviality west_ok:
  good_interface WEST
Proof
  EVAL_TAC
QED

Theorem interface_rewrites =
  (LIST_CONJ [MATCH_MP shape_w west_ok,
              MATCH_MP shape_w east_ok,
              MATCH_MP shape_e west_ok,
              MATCH_MP shape_e east_ok,
              MATCH_MP shape_n north_ok,
              MATCH_MP shape_n south_ok,
              MATCH_MP shape_s north_ok,
              MATCH_MP shape_s south_ok] |> REWRITE_RULE [GSYM CONJ_ASSOC]);

val _ = export_theory();
