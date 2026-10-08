/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform upper bounds from convergence along all selections

Suppose a real-valued family \(e_i(x)\) tends to zero along every choice
\(x_i\) of its auxiliary parameter. Then, for every positive tolerance,
all auxiliary parameters satisfy the upper bound eventually. The index
filter is arbitrary and the nonempty parameter space has no topology.

This elementary selection argument converts projection-defect limits with
arbitrarily varying outer lengths into one common overlap-length bound.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. It proves only the uniformization implication; convergence
of the tensor-specific defects remains a separate hypothesis.
-/

namespace Filter

/-- Convergence to zero along every choice of the auxiliary parameter gives
an eventual uniform upper bound. Neither countability of the parameter space
nor nonnegativity of the family is required. Source: the uniform projection
comparison in Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531; this is the elementary selection implication used there. -/
theorem eventually_forall_le_of_tendsto_all_selections
    {ι X : Type*} [Nonempty X] {f : Filter ι}
    (e : ι → X → ℝ)
    (h : ∀ x : ι → X, Tendsto (fun i => e i (x i)) f (nhds 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ i in f, ∀ x, e i x ≤ ε := by
  classical
  have hChoice : ∀ i, ∃ x, e i x ≤ ε → ∀ y, e i y ≤ ε := by
    intro i
    by_cases hi : ∀ y, e i y ≤ ε
    · exact ⟨Classical.arbitrary X, fun _ => hi⟩
    · rcases not_forall.mp hi with ⟨x, hx⟩
      exact ⟨x, fun hle => (hx hle).elim⟩
  choose x hx using hChoice
  exact ((h x).eventually (Iio_mem_nhds hε)).mono fun i hi => hx i hi.le

end Filter
