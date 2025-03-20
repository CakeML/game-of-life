# Verified compilation into Conway's Game of Life

The work by Nicolas Loizeau is an inspiration:

 - https://www.nicolasloizeau.com/gol-computer

 - https://www.youtube.com/watch?v=Kk2MH9O4pXY&t=930

To build the project:

* Install [HOL](https://hol-theorem-prover.org/)
* Run `Holmake` from the project directory

Points of interest:
* [`gol_rulesScript.sml`](./gol_rulesScript.sml) has the definition of
  GOL and what it means to be a GOL in GOL simulation

* [`gol_in_gol_circuitScript.sml`](./gol_in_gol_circuitScript.sml)
  has the main theorem `gol_in_gol_thm`

* The gate designs are in [`gates/`](./gates), in RLE format (which is
  supported by [Golly](https://golly.sourceforge.io/) - useful if you
  want to play with the gates outside the context of this formalization)

* The mega-cell design is in
  [`gol_in_gol_paramsLib.sml`](./gol_in_gol_paramsLib.sml), as an ASCII
  art diagram that is parsed and verified in
  [`gol_in_gol_circuitScript.sml`](./gol_in_gol_circuitScript.sml).

It should take about 5 minutes to compile the project.
