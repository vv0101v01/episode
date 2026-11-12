name = "dtt03/h4_reduction_localization"

version = "0.1.0"

license = "Apache-2.0"

keywords = [
  "localization",
  "subject-reduction",
  "strong-normalization",
  "church-rosser",
  "bridge",
]

description = "Bridge module H4 (H2 x H3): lossless embedding of kernel terms into the hash-consed reduction arena, normalization as localization at reductions (O(1) definitional-equality classes), exhaustive subject-reduction and strong-normalization certification of well-typed terms, and NbE vs rewriting agreement"

import {
  "dtt03/h2_beta_eta_sn@0.1.0",
  "dtt03/h3_nbe_typecheck@0.1.0",
}
