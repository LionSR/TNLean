/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.GraphBall

/-!
# Infinite distance between graph components

The extended graph distance read as a pseudo-emetric, `ManyBody.graphPseudoEMetricSpace`, and
its lemmas `ManyBody.graphPseudoEMetricSpace_edist`, `_edist_ne_top` and `_edist_toReal` come
from QICLean. This file adds the complementary statement: two vertices are at infinite distance
exactly when they lie in different components of the graph.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 146–160, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This supplies the graph metric for the weighted kernel estimate; it introduces
no additional geometric assumptions.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace TNLean.PEPS.AreaLaw

variable {ι : Type*}

/-- Distinct graph components are at infinite distance in the pseudo-emetric. -/
@[simp]
theorem graphPseudoEMetricSpace_edist_eq_top (G : SimpleGraph ι) (x y : ι) :
    letI := ManyBody.graphPseudoEMetricSpace G
    edist x y = ⊤ ↔ ¬ G.Reachable x y := by
  simp only [← ManyBody.graphPseudoEMetricSpace_edist_ne_top G x y, not_not]

end TNLean.PEPS.AreaLaw
