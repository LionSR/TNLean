/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowDensityEntropyBound
import TNLean.Lattice.RegionEntropyInequalities

/-!
# The low-energy entropy bound in every positive local dimension

The physical construction for local dimension at least two is unchanged.
For a scalar local space, the regional dimension bound gives zero entropy
and hence the same estimate directly. This includes empty chains and all
prescribed intervals. Positive local dimension is the usual convention for
qudit chains, rather than an extra physical assumption.

The bandwidth is fixed before the physical data as in ALVV,
arXiv:1602.08828v2, Assumption (LD), lines 281–284. The conclusion is the
entropy part of Theorem `thm:al-ld`, lines 1096–1105.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The original-band entropy estimate includes the scalar local space.
ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_entropy_bound_of_pos_dimension
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 0 < q), p ≤ r → r ≤ L → 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        Entropy.regionEntropy J ψ ≤ Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          K / v * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / v)) ^ 3 := by
  classical
  obtain ⟨K, hK, hactual⟩ := exists_fixed_bandwidth_interval_low_energy_entropy_bound etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw J G ψ hψG hψ
  by_cases hq2 : 2 ≤ q
  · exact hactual L q p r v hq2 hpr hrL hv h hs h0 h1 ψ hψG hψ
  · have hq1 : q = 1 := by omega
    subst q
    have hzero : Entropy.regionEntropy J ψ ≤ 0 := by
      simpa only [Nat.cast_one, Real.log_one, mul_zero] using
        TNLean.Lattice.regionEntropy_le_card_mul_log hψ J
    have hlogv : 0 ≤ Real.log (1 + 1 / v) :=
      Real.log_nonneg (by linarith only [one_div_pos.mpr hv])
    exact hzero.trans (add_nonneg (Real.log_natCast_nonneg _)
      (mul_nonneg (div_nonneg hK.le hv.le) (by
        simp only [Nat.cast_one, Real.log_one, add_zero]
        positivity)))

end TNLean.MPS.AreaLaw
