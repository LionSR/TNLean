/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.EMetricSpace.Defs

/-!
# Extended graph distance as a pseudo-emetric

The canonical coercion from extended natural numbers to extended nonnegative
reals turns `SimpleGraph.edist` into a Mathlib `PseudoEMetricSpace`. The
structure is installed locally when applying metric results to a given graph;
there is no global instance on its vertex type. Disconnected vertices retain
infinite distance. Taking `toReal` agrees with natural graph distance, including
its zero convention between components.

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

open scoped ENNReal

namespace TNLean.PEPS.AreaLaw

variable {ι : Type*}

/-- Extended graph distance, coerced through Mathlib's canonical `ENat` to
`ENNReal` embedding. Use `letI := graphPseudoEMetricSpace G` locally. -/
@[instance_reducible]
noncomputable def graphPseudoEMetricSpace (G : SimpleGraph ι) : PseudoEMetricSpace ι :=
  .ofEDist (fun x y => (G.edist x y : ℝ≥0∞))
    (fun x => by simp only [G.edist_self, ENat.toENNReal_zero])
    (fun x y => by rw [G.edist_comm])
    (fun x y z => by
      simpa only [ENat.toENNReal_add] using ENat.toENNReal_mono (G.edist_triangle))

/-- Installing the graph pseudo-emetric preserves the extended graph distance. -/
@[simp]
theorem graphPseudoEMetricSpace_edist (G : SimpleGraph ι) (x y : ι) :
    letI := graphPseudoEMetricSpace G
    edist x y = (G.edist x y : ℝ≥0∞) := rfl

/-- Finite distance in the graph pseudo-emetric is equivalent to reachability. -/
@[simp]
theorem graphPseudoEMetricSpace_edist_ne_top (G : SimpleGraph ι) (x y : ι) :
    letI := graphPseudoEMetricSpace G
    edist x y ≠ ⊤ ↔ G.Reachable x y := by
  simp only [graphPseudoEMetricSpace_edist, ENat.toENNReal_ne_top,
    G.edist_ne_top_iff_reachable]

/-- Distinct graph components are at infinite distance in the pseudo-emetric. -/
@[simp]
theorem graphPseudoEMetricSpace_edist_eq_top (G : SimpleGraph ι) (x y : ι) :
    letI := graphPseudoEMetricSpace G
    edist x y = ⊤ ↔ ¬ G.Reachable x y := by
  simp only [← graphPseudoEMetricSpace_edist_ne_top G x y, not_not]

/-- Real-valued graph pseudo-distance agrees with natural graph distance.
Both sides are zero at unreachable pairs, so component support must be checked
before using this equality in a weighted kernel bound. -/
@[simp]
theorem graphPseudoEMetricSpace_edist_toReal (G : SimpleGraph ι) (x y : ι) :
    letI := graphPseudoEMetricSpace G
    (edist x y).toReal = (G.dist x y : ℝ) := by
  change (G.edist x y : ℝ≥0∞).toReal = ((G.edist x y).toNat : ℝ)
  induction G.edist x y using ENat.recTopCoe <;> simp

end TNLean.PEPS.AreaLaw
