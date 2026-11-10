/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalViability
import TNLean.MPS.AreaLaw.IntervalGenerators
import QICLean.Analysis.ViableTrimmingRank

/-!
# Native matrix product vectors from weighted trimming bounds

The weighted rank bound of each actual recorded vector is converted at the
chosen common threshold. The existing finite-span result supplies the
additional generator-count factor for every vector in the same native space.

This supports ALVV, arXiv:1602.08828v2, collective trimming, lines 660–697,
and final refinement, lines 1809–1817. The finite-span argument is LVV,
arXiv:1307.5143v1, Claim `c:2`, lines 520–527.
-/

namespace TNLean.MPS.AreaLaw

/-- The actual full-interval space with recorded weighted trimming bounds
has one native MPS bond bound for its entire span. The extra count factor
is retained. Supporting ALVV, arXiv:1602.08828v2, collective trimming,
lines 660–697, and LVV, arXiv:1307.5143v1, Claim `c:2`, lines 520–527. -/
theorem isOpenMPS_of_mem_nativeFullIntervalSpace_of_trimming_rank_bound
    {L q D count : ℕ} (hD : 1 ≤ D)
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))}
    (hS : IsIntervalSpanWithRankBound L q 0 L count
      (1 / (1000 * (D : ℝ) * Real.sqrt ((L : ℝ) + 1))) S)
    {v : EuclideanSpace ℂ (Fin L → Fin q)} (hv : v ∈ nativeFullIntervalSpace L q S) :
    IsOpenMPS L q (1000000 * D ^ 2 * (L + 1) * count ^ 2) (fun x ↦ v x) := by
  obtain ⟨n, hn, generators, hspan, hranks⟩ := hS
  obtain ⟨x, hx, rfl⟩ := hv
  have hgenerators : ∀ (i : Fin n) (j : ℕ), j < L - 1 →
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutVector (intervalTrimCut L 0 L j) (generators i))) ≤
          1000000 * D ^ 2 * (L + 1) * count := by
    intro i j hj
    exact Real.viable_node_trimming_rank_bound hD (hranks j (by simpa using hj) i)
  rw [hspan] at hx
  have hmps := isOpenMPS_fullIntervalRead_of_mem_span generators hgenerators hx
  change IsOpenMPS L q (1000000 * D ^ 2 * (L + 1) * count ^ 2)
    (WithLp.ofLp (fullIntervalEquiv L q x))
  rw [fullIntervalEquiv_apply]
  apply hmps.mono
  calc
    _ ≤ count * (1000000 * D ^ 2 * (L + 1) * count) :=
      Nat.mul_le_mul_right _ hn
    _ = _ := by ring

end TNLean.MPS.AreaLaw
