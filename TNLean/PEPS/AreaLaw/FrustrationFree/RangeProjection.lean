/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SupportProjectionOrder
import QICLean.ManyBody.Sites.Twirl

/-!
# Range projections of positive local terms

QICLean's support projection `Π_A` of a positive semidefinite matrix `A` is an orthogonal
projection (`Matrix.IsHermitian.isStarProjection_supportProj`) annihilating the kernel of `A`
(`Matrix.IsHermitian.supportProj_mulVec_eq_zero_of_mulVec_eq_zero`). This module adds the two
facts the frustration-free sweep needs beyond these: `A ≤ J Π_A` when `A ≤ J`, and `Π_A` acts on
the sites on which `A` acts.

The frustration-free area-law note sweeps with the factors `(1 - h_i / J)^{1/2}`. Replacing them
by `1 - Π_{h_i}` keeps the three properties the note uses: each factor fixes the ground vector,
acts on the support of its term, and `Π_{h_i} ≥ h_i / J`, so the gap
`∑ Π_{h_i} ≥ (Δ/J)(1 - P)` persists. See
`docs/paper-gaps/frustrationfree_sweep_range_projections.tex`.

## Main statements

* `Matrix.PosSemidef.le_smul_supportProj`: `A ≤ J Π_A` when `0 ≤ A ≤ J`.
* `TNLean.PEPS.AreaLaw.FrustrationFree.supportProj_mem_supportedOperators`: `Π_A` acts on the
  support of `A`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  paragraph "Contraction in one sweep".
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive semidefinite matrix bounded by `J` lies below `J` times its range projection:
`A ≤ J Π_A`. Source: `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
paragraph "Contraction in one sweep", where `k_i = h_i / J` is a positive contraction. -/
theorem PosSemidef.le_smul_supportProj {A : Matrix n n ℂ} (hA : A.PosSemidef) {J : ℝ}
    (hAJ : A ≤ J • (1 : Matrix n n ℂ)) : A ≤ J • hA.supportProj := by
  have hsa : IsSelfAdjoint A := hA.isHermitian.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ A, x ≤ J := by
    rw [← Algebra.algebraMap_eq_smul_one] at hAJ
    exact (le_algebraMap_iff_spectrum_le hsa).mp hAJ
  change A ≤ J • hA.isHermitian.supportProj
  have hc := A.finite_real_spectrum.continuousOn (fun x : ℝ ↦ if x ≠ 0 then (1 : ℝ) else 0)
  rw [hA.isHermitian.supportProj_eq_cfc, ← cfc_const_mul J _ A hc]
  conv_lhs => rw [← cfc_id' ℝ A hsa]
  refine cfc_mono (fun x hx ↦ ?_) (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)
  by_cases hx0 : x = 0
  · simp [hx0]
  · simpa [hx0] using hspec x hx

end Matrix

namespace TNLean.PEPS.AreaLaw.FrustrationFree

open ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- The range projection of a Hermitian operator acting on a region acts on the same region.
Source: `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, paragraph
"Contraction in one sweep": the filters have the support bound of the terms. -/
theorem supportProj_mem_supportedOperators {D : Finset V} {A : Matrix (Config X) (Config X) ℂ}
    (hA : A.IsHermitian) (hmem : A ∈ supportedOperators X D) :
    hA.supportProj ∈ supportedOperators X D := by
  rw [hA.supportProj_eq_cfc]
  exact cfc_mem_supportedOperators _ hmem

end TNLean.PEPS.AreaLaw.FrustrationFree
