name = "dtt03/s8_symbolic_nbe"

version = "0.1.0"

license = "Apache-2.0"

keywords = [
  "symbolic-execution",
  "normalization-by-evaluation",
  "proof-synthesis",
  "path-condition",
  "induction",
]

description = "Module S8 (uses H3): symbolic execution integrated with NbE — neutral eliminators stuck on symbolic variables drive case splits and inductions, path conditions are explored exhaustively, and the execution tree is compiled into an eliminator proof term that the H3 kernel re-checks; failed goals yield concrete counterexamples"

import {
  "dtt03/h3_nbe_typecheck@0.1.0",
}
