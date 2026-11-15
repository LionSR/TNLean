/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGApproximation
import TNLean.MPS.AreaLaw.SharpRankCount

/-!
# The explicit sharp logarithmic-rank estimate

The physical normalized approximation retains one logarithm of the full
ground-space dimension. Its remaining rank cost has inverse-gap cubic local
logarithms and a quarter-power gap, three-quarter-power accuracy term, with
an explicit logarithmic correction. This supports the fixed-cut conclusion
of ALVV, arXiv:1602.08828v2, Theorem 4.9, source lines 1048–1085.

**Local fix (parameter choice):** Independent scales replace the printed
nonuniform prescription; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (gap dependence):** The bound uses `min gamma 1`.
Comparison with the printed quantitative dependence is established for
`0 < gamma ≤ 1`; the larger-gap comparison remains as recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

The distinct spectral values express Assumption (DG) of the source,
lines 275–279, which requires a second smallest eigenvalue.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A normalized approximation to every original unit ground vector satisfies
the explicit logarithmic Schmidt-rank estimate at each actual interval cut.
No rank, overlap or approximation premise is supplied. The universal constant
precedes the chain, Hamiltonian, gap, interval, accuracy and ground vector.
Supporting ALVV, arXiv:1602.08828v2, Theorem 4.9, fixed-cut conclusion,
source lines 1048–1085. -/
theorem exists_physical_dg_interval_normalized_approximation :
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
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ G : ℝ) +
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  classical
  obtain ⟨A, C, hA, hC, hraw⟩ :=
    exists_physical_dg_normalized_approximation_of_independent_scales
  let cA : ℝ := 6 + 2 * Real.log (A + 1)
  let K0 : ℝ := 22 * (A + 1) * cA
  let b : ℝ := (7 * C) ^ (1 / 4 : ℝ) * (5 / 4 : ℝ) ^ (1 / 4 : ℝ)
  have hlogA : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith only [hA])
  have hK0 : 0 ≤ K0 := by dsimp only [K0, cA]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hlogb : 0 ≤ Real.log (11 + b) := Real.log_nonneg (by linarith only [hb])
  let K := 24 * K0 + 88 * (1 + Real.log (11 + b)) * (11 + b)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G g u J beta tau U Phi Tm e
  let ell0 : ℕ := ⌈A * u ^ 2 / g⌉₊
  let D0 : ℕ := (q * ell0 ^ 2) ^ (22 * ell0)
  obtain ⟨hD0, hlogD0, happrox⟩ :=
    hraw L q p r hpr hrL h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hD02 : 2 ≤ D0 := hD0
  have hbootstrap : Real.log (D0 : ℝ) ≤ K0 / g * u ^ 3 := hlogD0
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  intro delta hdelta hdelta1 a ψ hψG hψ
  obtain ⟨ell1, hell1, hwindow, hvectors⟩ := happrox delta hdelta hdelta1
  let D1 : ℕ := (q * ell1 ^ 2) ^ (22 * ell1)
  obtain ⟨φ, hφ, hoverlap, hrank⟩ := hvectors ψ hψG hψ
  have hfrac : 1 / (4 * g / 5) = (5 / 4 : ℝ) * (1 / g) := by field_simp
  have hten : 8 / (4 * g / 5) = 10 / g := by
    field_simp
    norm_num
  have hwindow' : (ell1 : ℝ) ≤
      10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := by
    rw [hten, hfrac, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4)
      (by positivity : (0 : ℝ) ≤ 1 / g)] at hwindow
    simpa only [b, mul_assoc] using hwindow
  have ha : 1 ≤ a := by
    have hlogg := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hlogdelta := Real.log_nonneg ((one_le_div hdelta).2 hdelta1)
    dsimp only [a]
    linarith only [hlogg, hlogdelta]
  have hbudget : Real.log ((Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2 : ℕ) : ℝ) ≤
      Real.log (Module.finrank ℂ G : ℝ) +
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log a) :=
    Real.sharp_approximation_log_rank_budget (Module.finrank ℂ G) D0 q ell1 g a K0 b
      hrG (by omega) (by omega) hell1 hg hg1 ha hK0 hb hwindow' hbootstrap
  refine ⟨φ, hφ, hoverlap, ?_⟩
  by_cases hzero : Matrix.schmidtRank (WithLp.ofLp (e φ)) = 0
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact (Real.log_natCast_nonneg (Module.finrank ℂ G * D0 ^ 24 * D1 ^ 2)).trans hbudget
  · have hpos : (0 : ℝ) < (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    exact (Real.log_le_log hpos (by exact_mod_cast hrank)).trans hbudget

end TNLean.MPS.AreaLaw
