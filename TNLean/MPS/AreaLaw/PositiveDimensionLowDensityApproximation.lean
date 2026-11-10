/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLowDensitySharpApproximation

/-!
# Strict fixed-cut approximation in positive local dimension

The scalar local space is handled by its exact rank-one representation.
In local dimension at least two, use the same actual physical construction
at half the requested accuracy. This makes the overlap strict and changes
only the fixed numerical factor inside the accuracy logarithm.

The statement is the fixed-cut consequence of ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105, with the usual positive local-dimension
convention and fixed bandwidth. Its capped-width comparison is recorded in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Positive local dimension suffices for the sharp fixed-cut rank bound
with strict overlap. ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`,
lines 1096–1105. The accuracy logarithm contains the explicit factor two. -/
theorem exists_fixed_bandwidth_interval_low_energy_strict_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 0 < q), p ≤ r → r ≤ L → 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ h0 : ∀ i, 0 ≤ h i, (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + c)
      let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
      let b := min v (etaLD / 2)
      let g := min (b / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (2 / delta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta < ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  classical
  obtain ⟨K, hK, hactual⟩ :=
    exists_fixed_bandwidth_interval_low_energy_normalized_approximation etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw
    J beta tau U Phi Tm G e b g u delta hdelta hdelta1 a ψ hψG hψ
  by_cases hq2 : 2 ≤ q
  · obtain ⟨φ, hφ, hoverlap, hrank⟩ :=
      hactual L q p r v hq2 hpr hrL hv h hs h0 h1
        (delta / 2) (by positivity) (by linarith only [hdelta1]) ψ hψG hψ
    have hrecip : 1 / (delta / 2) = 2 / delta := by field_simp
    rw [hrecip] at hrank
    exact ⟨φ, hφ, by linarith only [hoverlap, hdelta], hrank⟩
  · have hq1 : q = 1 := by omega
    subst q
    have hg : 0 < g := lt_min (by dsimp only [b]; positivity) (by norm_num)
    have hg1 : g ≤ 1 := min_le_right _ _
    have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hu : 0 ≤ u := by
      simp only [u, Nat.cast_one, Real.log_one, add_zero]
      linarith only [hlogg]
    have hlogdelta : 0 ≤ Real.log (2 / delta) :=
      Real.log_nonneg ((one_le_div hdelta).2 (by linarith only [hdelta1]))
    have ha : 1 ≤ a := by dsimp only [a]; linarith only [hlogg, hlogdelta]
    have hP : 0 ≤ 1 + Real.log a := by linarith only [Real.log_nonneg ha]
    have hcost : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log a) := by positivity
    have hrank : Matrix.schmidtRank (WithLp.ofLp (e ψ)) ≤ 1 := by
      have h := Matrix.schmidtRank_le_left (WithLp.ofLp (e ψ))
      simpa only [Fintype.card_fun, Fintype.card_fin, one_pow] using h
    refine ⟨ψ, hψ, ?_, ?_⟩
    · have hi : ‖⟪ψ, ψ⟫_ℂ‖ = 1 := by norm_num [inner_self_eq_norm_sq_to_K, hψ]
      rw [hi]
      linarith only [hdelta]
    · exact (Real.log_nonpos (Nat.cast_nonneg _) (by exact_mod_cast hrank)).trans
        (add_nonneg (Real.log_natCast_nonneg _) hcost)

end TNLean.MPS.AreaLaw
