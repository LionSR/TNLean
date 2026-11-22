/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.IndependentLowDensityBufferedTargets
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.SharpApproximationParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.Spectral.PolynomialFilterParameters
import QICLean.Spectral.LowEnergy.ChebyshevViability
import QICLean.Spectral.LowEnergy.ShiftedLowEnergyCoordinates

/-!
# Sharp regional polynomial families under numerical budgets

Under explicit numerical budgets for the clipping threshold, window and degree, one
actual clipped Hamiltonian has a polynomial of the chosen degree with a common
regional tensor decomposition and a recorded gap between its two cutoffs. These
are the constructions behind `TNLean.MPS.AreaLaw.SharpRegionalLowDensityFamily`.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.

**Scope restriction (interior geometry):** The five-region fit and collar bound are
explicit. Boundary and short regions require the subsequent interval argument; see
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix


/-- Normalize the difference of the two cutoffs before specializing the
operator to its physical clipping formula. This is the nested Chebyshev
composition of ALVV, arXiv:1602.08828v2, lines 1037–1041. -/
theorem exists_nested_polynomial_with_recorded_gap
    {σ m e : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]
    {N degree : ℕ} (B : Matrix σ σ ℂ) (hB : B.IsHermitian)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ j, TensorProduct.mapL (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W j))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M j)))
    (eta0 eta1 upper gap : ℝ) (hgap : eta1 - eta0 = gap)
    (hsep : eta0 < eta1) (hend : eta1 ≤ upper) (hnorm : ‖B‖ ≤ upper) :
    let lower := Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues eta0
    let higher := Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues eta1
    let Delta := (2 * Real.exp (-2 * (degree : ℝ) * Real.sqrt
      (gap / (upper - eta0)))) ^ 2
    ∃ p : Polynomial ℝ, p.natDegree = degree ∧ p.eval eta0 = 1 ∧
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)
              (Polynomial.aeval B (p.map (algebraMap ℝ ℂ))) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ j, TensorProduct.mapL (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W j))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M j)) ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
          Submodule.IsViable (F := EuclideanSpace ℂ e) delta S
            (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ j : Fin N, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W j)).toLinearMap
          Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ e) (Delta / (1 - delta) ^ 2)
              grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  intro lower higher Delta
  have hresult := Matrix.exists_chebyshev_nested_viability_of_polynomial_family
    (degree := degree) B hB hB.eigenvectorBasis hB.eigenvalues
    hB.toEuclideanCLM_eigenvectorBasis W Tm hdecomp eta0 eta1 upper hsep hend hnorm
  rw [hgap] at hresult
  exact hresult

/-- The actual regional polynomial construction under explicit numerical
comparison and filter budgets. This auxiliary constructs every physical and
spectral object from the supported interactions; it assumes no operator family.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_sharp_regional_family_of_scalar_budgets
    (ell : ℕ) (t etaLD w epsilon g : ℝ)
    (hell : 1 ≤ ell) (hw : 0 < w) (hepsilon : 0 < epsilon) (hgw : g ≤ w)
    (ht0 : 0 ≤ t) (ht : 19 + etaLD ≤ t)
    (hxi1 : (288 * Real.exp (11 / 8)) * Real.exp (-(t - etaLD) / 8) ≤ 1)
    (hsmall : 2 * (6 + etaLD) * ((288 * Real.exp (11 / 8)) *
      Real.exp (-(t - etaLD) / 8)) ≤ (epsilon / 100) * w ^ 2)
    (hfilter : ∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt (g / R))) ^ 2 ≤ epsilon / 8) :
      ∀ (L q m a b : ℕ) (_hq : 2 ≤ q), q ≤ m →
      let D := (m * ell ^ 2) ^ (22 * ell)
      let nu := epsilon / 100
      ∀ (_hab : a + 2 * ell ≤ b) (_hbL : b + 2 * ell ≤ L - 1),
      ∀ Jtarget : Finset (Fin L),
      (interval L (a + ell) (b + ell + 1) \ Jtarget).card +
        (Jtarget \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ _h0 : ∀ i, 0 ≤ Φ.term i, (∀ i, Φ.term i ≤ 1) →
      let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
      let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
        ∑ i ∈ Finset.univ.filter
          (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
      let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
        (fun i ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, Φ.term i
      let K : Finset (Fin 5) := {0, 2, 4}
      let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
          Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
        (∑ j, ((if j ∈ T then
          cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
        (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
        star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        B t e ∅ = Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
        star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
        (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
        ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
        let J := Jtarget
        let beta := fun _ : Fin L ↦ Fin q
        let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
        let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
        let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
          (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
        let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
          (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
          (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
        ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
          ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
          (E0 + eta - 2 * w)
        let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
          (E0 + eta - w)
        let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
          Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
        lower ≤ higher ∧
        Submodule.IsCloseTo nu
          (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
        Submodule.IsCloseTo nu lower
          (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) ∧
        Delta ≤ epsilon / 8 ∧
          ∃ p : Polynomial ℝ, p.natDegree = ell ^ 2 ∧ p.eval (E0 + eta - 2 * w) = 1 ∧
            ∃ M : Fin N → Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ,
              Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                    (Polynomial.aeval (B t e K) (p.map (algebraMap ℝ ℂ))) ∘L
                  Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
                ∑ j, TensorProduct.mapL
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := {v // v ∉ J} → Fin q) (M j)) ∧
              ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
                Submodule.IsViable (F := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) delta S
                  (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
                let grow := ⨆ j : Fin N, S.map
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
                Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
                  Submodule.IsViable (F := EuclideanSpace ℂ ({v // v ∉ J} → Fin q))
                    (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  intro L q m a b hq hqm D nu hab hbL Jtarget hcollar Φ h0 h1 k A Cross Y K B
  obtain ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_independent_low_energy_targets_of_residual_budget_at_error
      L q a b ell t etaLD w nu ht0 hw (by dsimp only [nu]; positivity)
      ht hxi1 hsmall hq hell hab hbL Φ h0 h1
  change (B t e ∅).IsHermitian at hO
  change (B t e K).IsHermitian at hC
  change ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) at hnorm
  refine ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, ?_⟩
  intro J beta tau U Phi Tm
  have hdegree : 1 ≤ ell ^ 2 := hell.trans (Nat.le_self_pow (by decide) ell)
  have :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell hq hdegree hab hbL Φ e t J
  obtain ⟨N, W, hNraw, hdecomp⟩ := this
  have hN : N ≤ D ^ 2 := by
    apply hNraw.trans
    simpa only [Nat.mul_add] using
      collar_card_le_square_of_larger_count_base q m ell
        ((interval L (a + ell) (b + ell + 1) \ Jtarget).card +
          (Jtarget \ interval L (a + ell) (b + ell + 1)).card)
        (((q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))) ^ 2)
        hq hqm hell hcollar le_rfl
  refine ⟨N, W, hN, ?_⟩
  intro eta hbuffer hetaLD lower higher Delta
  have := htargets eta hbuffer hetaLD
  obtain ⟨hnest, hupperClose, hlowerClose⟩ := this
  have hupper : E0 + eta - w ≤ 3 * t + 4 * (ell : ℝ) := by
    linarith only [hE04, ht, hetaLD, hw, ht0,
      (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell)]
  have hR : 0 < (3 * t + 4 * (ell : ℝ)) - (E0 + eta - 2 * w) := by
    linarith only [hupper, hw]
  have hRup : (3 * t + 4 * (ell : ℝ)) - (E0 + eta - 2 * w) ≤
      3 * t + 4 * (ell : ℝ) := by linarith only [hE0, hbuffer, hw]
  have hpolynomial := exists_nested_polynomial_with_recorded_gap
    (degree := ell ^ 2) (B t e K) hC W Tm
    (fun Q hQ ↦ (hdecomp Q hQ).imp fun M hM ↦ by
      -- The two tensor coordinates agree after reducible unfolding only.
      have hconj := hM.2
      with_reducible exact hconj)
    (E0 + eta - 2 * w) (E0 + eta - w) (3 * t + 4 * (ell : ℝ)) w
    (by ring) (by linarith only [hw]) hupper hnorm
  refine ⟨hnest, hupperClose, hlowerClose, ?_, hpolynomial⟩
  apply le_trans ?_ (hfilter _ hR hRup)
  have hsqrt := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hgw hR.le)
  dsimp only [Delta]
  rw [Nat.cast_pow]
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg (sq_nonneg (ell : ℝ)) (sub_nonneg.mpr hsqrt)]

end TNLean.MPS.AreaLaw
