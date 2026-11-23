/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Templates.TwoFamilies
import QICLean.ManyBody.Entropy.MutualInformationPerturbation

/-!
# Regional entropy continuity on a finite lattice

For two normalized vectors on the same finite lattice, the entropy change
on a fixed region is bounded by the global trace distance and the number of
sites in that region. The dimension factor is `1 + |A| log q`.

The statement makes no geometric or Hamiltonian assumption and includes
empty regions and local dimension one. Both vectors are supplied; the
argument makes no further choice of state.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 2.1 (`01-preliminaries.tex`, lines 33–46), as used in
`08-scanner.tex`, lines 399–404, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The Lean proof follows the argument of Lemma 2.1 rather than transcribing its text.
-/

namespace TNLean.PEPS.AreaLaw

/-- Regional entropy continuity with the dimension of the actual region.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, and its application
in `08-scanner.tex`, lines 399–404. -/
theorem abs_regionEntropy_sub_le_sqrt_traceDistance_card
    (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω Φ : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (hΦ : ‖Φ‖ = 1)
    (A : Finset ↥Λ) :
    |ManyBody.regionEntropy Ω A - ManyBody.regionEntropy Φ A| ≤
      4 * Real.sqrt (Matrix.traceDistance
        (Matrix.vecMulVec Ω (star Ω)) (Matrix.vecMulVec Φ (star Φ))) *
        (1 + (A.card : ℝ) * Real.log q) := by
  have h := ManyBody.abs_regionEntropy_sub_le_sqrt_traceDistance
    (fun _ : ↥Λ ↦ Fin q) Ω Φ hΩ hΦ A
  have hdim :
      (Fintype.card (ManyBody.RegionConfig (fun _ : ↥Λ ↦ Fin q) A) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr
      (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
        (ManyBody.trace_regionState_eq_one hΩ (D := A))))).ne'
  rw [Real.log_mul (Real.exp_ne_zero 1) hdim] at h
  simpa [Nat.cast_pow, Real.log_pow] using h

end TNLean.PEPS.AreaLaw
