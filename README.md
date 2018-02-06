# gspn

A Clojure library for calculation of steady-state properties of Generalized Stochastic Petri Nets (GSPNs)

## Usage

This does calculations not in pdenno.spntools. The reason for splitting it out from pdenno.spntools is
to allow spntools to be used separately in cljs. This library (because of unexplored issues in
clojure.core.matrix) has problems compiling for ClojureScript. 

## License

Copyright © 2018 FIXME

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
