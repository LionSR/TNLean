/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.GroundGapUpperBound
import TNLean.MPS.AreaLaw.PhysicalDGGlobalApproximation

/-!
# The capped-gap estimates in the printed large-gap form

The Schmidt-rank and matrix product state estimates for a degenerate ground
space use the capped gap `g = min γ 1`. Theorem 4.9 of Arad, Landau, Vazirani
and Vidick, arXiv:1602.08828v2, source lines 1048–1086, prints the exponent

  `γ⁻¹ log³ d + γ^{-1/4} log^{3/4}(1/δ) log d`

with the uncapped gap. Since `1 / g = max γ 1 / γ`, the capped exponent is at
most `max γ 1` times the printed one. The gap bound of
`TNLean.MPS.AreaLaw.ALVV.GroundGapUpperBound` gives
`max γ 1 ≤ 1 + log r / log q`, so the two exponents differ by at most this
factor; it equals one when `r < q`, in particular for a unique ground state.

**Scope restriction (gap dependence):** For `γ > 1` and `r ≥ q` the printed
expression is reached only up to the factor `max γ 1 ≤ 1 + log r / log q` in
the exponent; the printed improvement with a single factor `r` is not proved.
Documented in `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw.ALVV

/-- The capped exponent is at most `max γ 1` times the uncapped printed
exponent. ALVV, arXiv:1602.08828v2, Theorem 4.9, source line 1080. -/
theorem capped_exponent_le_max_mul (gamma u a : ℝ) (hgamma : 0 < gamma) (hu : 0 ≤ u)
    (ha : 0 ≤ a) :
    u ^ 3 / min gamma 1 + (1 / min gamma 1) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u ≤
      max gamma 1 *
        (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) := by
  rcases le_or_gt gamma 1 with h | h
  · rw [min_eq_left h, max_eq_right h, one_mul]
  · rw [min_eq_right h.le, max_eq_left h.le, mul_add]
    have hinv0 : 0 < 1 / gamma := by positivity
    have hinv1 : 1 / gamma ≤ 1 := by rw [div_le_one hgamma]; exact h.le
    have hroot : 1 / gamma ≤ (1 / gamma) ^ (1 / 4 : ℝ) :=
      Real.self_le_rpow_of_le_one hinv0.le hinv1 (by norm_num)
    have hone : 1 ≤ gamma * (1 / gamma) ^ (1 / 4 : ℝ) := by
      calc (1 : ℝ) = gamma * (1 / gamma) := by field_simp
        _ ≤ gamma * (1 / gamma) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hroot hgamma.le
    have hfirst : u ^ 3 / 1 = gamma * (u ^ 3 / gamma) := by field_simp
    have hrest : 0 ≤ a ^ (3 / 4 : ℝ) * u := by positivity
    rw [div_one, div_one, Real.one_rpow, one_mul]
    rw [div_one] at hfirst
    nlinarith

/-- **Fixed-cut estimate with the uncapped gap.** Every original unit ground
vector has a normalized approximant whose Schmidt rank at the interval cut
satisfies the printed bound with the uncapped gap, up to the factor
`max γ 1` in the exponent, and `max γ 1 ≤ 1 + log r / log q`. The universal
constant precedes every physical input. ALVV, arXiv:1602.08828v2,
Theorem 4.9, fixed-cut conclusion, source lines 1048–1085.

**Scope restriction (gap dependence):** see the module docstring and
`docs/paper-gaps/alvv16_approximation_parameters.tex`. -/
theorem exists_physical_dg_interval_normalized_approximation_uncapped :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
      max gamma 1 ≤ 1 + Real.log (Module.finrank ℂ G : ℝ) / Real.log q ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ G : ℝ) +
          K * max gamma 1 *
            (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  obtain ⟨K, hK, hfixed⟩ := exists_physical_dg_interval_normalized_approximation
  refine ⟨K, hK, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G g u J beta tau U Phi Tm e
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 0 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  refine ⟨?_, ?_⟩
  · have hgapbound := gap_le_one_add_log_div_log L q h hs h0 h1 mu nu gamma hmu hnu hmunu hgap
    have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
    have hr : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
    have hlogr : 0 ≤ Real.log (Module.finrank ℂ G : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hr)
    have := div_nonneg hlogr hlogq
    exact max_le hgapbound (by linarith)
  intro delta hdelta hdelta1 a ψ hψG hψ
  obtain ⟨φ, hφ, hoverlap, hrank⟩ :=
    hfixed L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      delta hdelta hdelta1 ψ hψG hψ
  refine ⟨φ, hφ, hoverlap, hrank.trans ?_⟩
  have ha : 1 ≤ a := by
    have hlogdelta := Real.log_nonneg ((one_le_div hdelta).2 hdelta1)
    dsimp only [a]
    linarith only [hlogg, hlogdelta]
  have hloga : 0 ≤ 1 + Real.log a := by linarith [Real.log_nonneg ha]
  have hcmp := capped_exponent_le_max_mul gamma u a hgamma hu (by linarith)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcmp hK.le) hloga
  have : K * max gamma 1 *
      (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) * (1 + Real.log a) =
      K * (max gamma 1 *
      (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u)) *
        (1 + Real.log a) := by ring
  rw [this]
  linarith

/-- **One matrix product approximant with the uncapped gap.** Every original
unit ground vector has a normalized open-boundary matrix product approximant
of bond dimension `r B`, where `log B` satisfies the printed bound with the
uncapped gap up to the factor `max γ 1 ≤ 1 + log r / log q` in the exponent.
ALVV, arXiv:1602.08828v2, Theorem 4.9, global conclusion, source lines
1080–1086.

**Scope restriction (gap dependence):** see the module docstring and
`docs/paper-gaps/alvv16_approximation_parameters.tex`. -/
theorem exists_physical_dg_normalized_isOpenMPS_approximation_uncapped :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ),
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      max gamma 1 ≤ 1 + Real.log (Module.finrank ℂ G : ℝ) / Real.log q ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (16 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * max gamma 1 *
          (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ G * B) (fun x ↦ Φ x) ∧
        1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  obtain ⟨K, hK, hglobal⟩ := exists_physical_dg_normalized_isOpenMPS_approximation
  refine ⟨K, hK, ?_⟩
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G g u
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 0 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  refine ⟨?_, ?_⟩
  · have hgapbound := gap_le_one_add_log_div_log L q h hs h0 h1 mu nu gamma hmu hnu hmunu hgap
    have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
    have hr : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
    have hlogr : 0 ≤ Real.log (Module.finrank ℂ G : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hr)
    have := div_nonneg hlogr hlogq
    exact max_le hgapbound (by linarith)
  intro delta hdelta hdelta1 b
  obtain ⟨B, hB, hlogB, hvec⟩ :=
    hglobal L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap delta hdelta hdelta1
  refine ⟨B, hB, hlogB.trans ?_, hvec⟩
  have hb : 1 ≤ b := by
    have hL : (1 : ℝ) ≤ 16 * ((L : ℝ) + 1) / delta := by
      rw [le_div_iff₀ hdelta]
      have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    have hlogL := Real.log_nonneg hL
    dsimp only [b]
    linarith only [hlogg, hlogL]
  have hlogb : 0 ≤ 1 + Real.log b := by linarith [Real.log_nonneg hb]
  have hcmp := capped_exponent_le_max_mul gamma u b hgamma hu (by linarith)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcmp hK.le) hlogb
  have : K * max gamma 1 *
      (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) * (1 + Real.log b) =
      K * (max gamma 1 *
      (u ^ 3 / gamma + (1 / gamma) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u)) *
        (1 + Real.log b) := by ring
  rw [this]
  linarith

end TNLean.MPS.AreaLaw.ALVV
