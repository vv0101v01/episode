name = "dtt03/h6_unified_pipeline"

version = "0.1.0"

license = "Apache-2.0"

keywords = [
  "dependent-type-theory",
  "pipeline",
  "proofs-as-programs",
  "normalization",
  "type-checking",
]

description = "Unified module H6 (H1..H5): one pipeline from source text to elaborated proof term, derivation tree, eta-long normal form, strong-normalization certificate, extracted program run on the lazy machine, and a system-wide audit of the rule/kernel Galois duality"

import {
  "dtt03/h1_rule_harmony@0.1.0",
  "dtt03/h2_beta_eta_sn@0.1.0",
  "dtt03/h3_nbe_typecheck@0.1.0",
  "dtt03/h4_reduction_localization@0.1.0",
  "dtt03/h5_rule_kernel_chu@0.1.0",
  "dtt03/s10_bridges@0.1.0",
}
