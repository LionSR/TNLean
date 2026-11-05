/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentLowDensityBufferedTargets
import TNLean.MPS.AreaLaw.SharpLowDensityParameters
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import QICLean.Analysis.NestedChebyshevViability
import QICLean.Analysis.ShiftedLowEnergyCoordinates

/-!
# Actual sharp low-energy polynomial families on retained regions

An independently chosen real clipping threshold and integer window determine
one actual clipped Hamiltonian. Its polynomial of the exact chosen degree
has a common regional tensor decomposition, whose collar cost fits the
same natural count. An all-cutoff equality identifies the original centered bands with the raw
Hamiltonian's canonical bands before the regional family is returned. Both
comparisons and Chebyshev suppression use the same physical construction.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041, and the sharp low-density approximation conclusion of
Theorem `thm:al-ld`, lines 1096–1105. The fixed bandwidth is explicit;
there is no spectral gap or supplied operator family, rank or residual.

**Scope restriction (interior geometry):** The five-region fit and collar
bound are explicit. Boundary and short regions require the subsequent
interval argument; see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Normalize the difference of the two cutoffs before specializing the
operator to its physical clipping formula. This is the nested Chebyshev
composition of ALVV, arXiv:1602.08828v2, lines 1037–1041. -/
private theorem exists_nested_polynomial_with_recorded_gap
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
private theorem exists_sharp_regional_family_of_scalar_budgets
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
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ _h0 : ∀ i, 0 ≤ h i, (∀ i, h i ≤ 1) →
      let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
      let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
        ∑ i ∈ Finset.univ.filter
          (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
      let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
        (fun i ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
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
        B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
        star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
        (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
        ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
        let J := Jtarget
        let beta := fun _ : Fin L ↦ Fin q
        let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
        let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
        let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
          (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
        let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
          (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
          (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
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
            ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
              Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                    (Polynomial.aeval (B t e K) (p.map (algebraMap ℝ ℂ))) ∘L
                  Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
                ∑ j, TensorProduct.mapL
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jᶜ) → Fin q) (M j)) ∧
              ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
                Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
                  (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
                let grow := ⨆ j : Fin N, S.map
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
                Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
                  Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                    (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  intro L q m a b hq hqm D nu hab hbL Jtarget hcollar h hs h0 h1 k A Cross Y K B
  obtain ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_independent_low_energy_targets_of_residual_budget_at_error
      L q a b ell t etaLD w nu ht0 hw (by dsimp only [nu]; positivity)
      ht hxi1 hsmall hq hell hab hbL h hs h0 h1
  change (B t e ∅).IsHermitian at hO
  change (B t e K).IsHermitian at hC
  change ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) at hnorm
  refine ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, ?_⟩
  intro J beta tau U Phi Tm
  have hdegree : 1 ≤ ell ^ 2 := hell.trans (Nat.le_self_pow (by decide) ell)
  obtain ⟨N, W, hNraw, hdecomp⟩ :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell hq hdegree hab hbL h hs e t J
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
  obtain ⟨hnest, hupperClose, hlowerClose⟩ := htargets eta hbuffer hetaLD
  have hupper : E0 + eta - w ≤ 3 * t + 4 * (ell : ℝ) := by
    linarith only [hE04, ht, hetaLD, hw, ht0,
      (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell)]
  have hR : 0 < (3 * t + 4 * (ell : ℝ)) - (E0 + eta - 2 * w) := by
    linarith only [hupper, hw]
  have hRup : (3 * t + 4 * (ell : ℝ)) - (E0 + eta - 2 * w) ≤
      3 * t + 4 * (ell : ℝ) := by linarith only [hE0, hbuffer, hw]
  have hpolynomial := exists_nested_polynomial_with_recorded_gap
    (degree := ell ^ 2) (B t e K) hC W Tm
    (fun Q hQ ↦ (hdecomp Q hQ).imp fun M hM ↦ hM.2)
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


/-- The same actual clipped polynomial gives a retained-region improving
family at the independent sharp scales. The threshold and window precede
the chain and physical terms; the regional family precedes every buffered
cutoff and source subspace. The canonical original-band identity is retained
for every cutoff, alongside the unchanged actual polynomial witnesses.
ALVV, arXiv:1602.08828v2, Theorems `t:aisgapless` and `thm:al-ld`,
lines 1027–1041 and 1096–1105. -/
theorem exists_fixed_bandwidth_sharp_regional_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 21 ≤ C ∧
      ∀ w epsilon : ℝ, 0 < w → 0 < epsilon → epsilon ≤ 1 →
      let g := min w 1
      let u := 16 + Real.log (1 / g) + Real.log (1 / epsilon)
      let t := C * u
      ∃ ell : ℕ, 1 ≤ ell ∧
        (ell : ℝ) ≤ 8 / g +
          (7 * C) ^ (1 / 4 : ℝ) * (1 / g) ^ (1 / 4 : ℝ) * u ^ (3 / 4 : ℝ) ∧
      ∀ (L q m a b : ℕ) (hq : 2 ≤ q), q ≤ m →
      let D := (m * ell ^ 2) ^ (22 * ell)
      let nu := epsilon / 100
      ∀ (_hab : a + 2 * ell ≤ b) (_hbL : b + 2 * ell ≤ L - 1),
      ∀ Jtarget : Finset (Fin L),
      (interval L (a + ell) (b + ell + 1) \ Jtarget).card +
        (Jtarget \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ h0 : ∀ i, 0 ≤ h i, (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
      let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
        ∑ i ∈ Finset.univ.filter
          (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
      let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
        (fun i ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
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
        B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
        star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
        (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
        ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
        minEigenvalue hRaw = E0 + ∑ j, e j ∧
        (∀ c : ℝ, Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + c) =
          Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
            (minEigenvalue hRaw + c)) ∧
        let J := Jtarget
        let beta := fun _ : Fin L ↦ Fin q
        let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
        let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
        let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
          (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
        let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
          (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
          (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
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
            ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
              Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                    (Polynomial.aeval (B t e K) (p.map (algebraMap ℝ ℂ))) ∘L
                  Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
                ∑ j, TensorProduct.mapL
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jᶜ) → Fin q) (M j)) ∧
              ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
                Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
                  (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
                let grow := ⨆ j : Fin N, S.map
                  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
                Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
                  Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                    (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, hscalar⟩ := Real.exists_sharp_low_density_scalar_parameters etaLD hLD
  refine ⟨C, hC, ?_⟩
  intro w epsilon hw hepsilon hepsilon1 g u t
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgw : g ≤ w := min_le_left _ _
  obtain ⟨ell, hell, hbound, ht, hxi1, hsmallg, hfilter⟩ :=
    hscalar g epsilon hg hg1 hepsilon hepsilon1
  have hsmall : 2 * (6 + etaLD) * ((288 * Real.exp (11 / 8)) *
      Real.exp (-(t - etaLD) / 8)) ≤ (epsilon / 100) * w ^ 2 :=
    hsmallg.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hgw 2)
      (by positivity))
  have ht0 : 0 ≤ t := by linarith only [ht, hLD]
  refine ⟨ell, hell, hbound, ?_⟩
  intro L q m a b hq hqm D nu hab hbL Jtarget hcollar h hs h0 h1 config H hRaw
    k A Cross Y K B
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hfamilies⟩ :=
    exists_sharp_regional_family_of_scalar_budgets ell t etaLD w epsilon g
      hell hw hepsilon hgw ht0 ht hxi1 hsmall hfilter
      L q m a b hq hqm hab hbL Jtarget hcollar h hs h0 h1
  obtain ⟨hminimum, hidentity⟩ :=
    hRaw.spectralSpanLE_centered_ground_of_eq hO (∑ j, e j) E0 z
      hcenter hzunit hz hE0low
  exact ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hminimum, hidentity, hfamilies⟩

end TNLean.MPS.AreaLaw
