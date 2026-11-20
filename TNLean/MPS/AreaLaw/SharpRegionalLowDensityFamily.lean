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
import TNLean.MPS.AreaLaw.SharpRegionalScalarBudgets

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

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix

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
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ h0 : ∀ i, 0 ≤ Φ.term i, (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
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
        minEigenvalue hRaw = E0 + ∑ j, e j ∧
        (∀ c : ℝ, Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + c) =
          Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
            (minEigenvalue hRaw + c)) ∧
        let J := Jtarget
        let beta := fun _ : Fin L ↦ Fin q
        let tau := (ManyBody.splitEquiv beta J).trans (Equiv.prodComm _ _)
        let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
        let Phi := ((EuclideanSpace.basisFun (ManyBody.RegionConfig beta Jᶜ) ℂ).tensorProduct
          (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
        let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
          (EuclideanSpace ℂ (ManyBody.RegionConfig beta Jᶜ))
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
  have := Real.exists_sharp_low_density_scalar_parameters etaLD hLD
  refine this.elim fun C hspec ↦ hspec.elim fun hC hspec ↦ ?_
  have hscalar := hspec
  refine ⟨C, hC, ?_⟩
  intro w epsilon hw hepsilon hepsilon1 g u t
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgw : g ≤ w := min_le_left _ _
  have :=
    hscalar g epsilon hg hg1 hepsilon hepsilon1
  refine this.elim fun ell hspec ↦ hspec.elim fun hell hspec ↦ hspec.elim fun hbound hspec ↦
    hspec.elim fun ht hspec ↦ hspec.elim fun hxi1 hspec ↦ hspec.elim fun hsmallg hspec ↦ ?_
  have hfilter := hspec
  have hsmall : 2 * (6 + etaLD) * ((288 * Real.exp (11 / 8)) *
      Real.exp (-(t - etaLD) / 8)) ≤ (epsilon / 100) * w ^ 2 :=
    hsmallg.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hgw 2)
      (by positivity))
  have ht0 : 0 ≤ t := by linarith only [ht, hLD]
  refine ⟨ell, hell, hbound, ?_⟩
  intro L q m a b hq hqm D nu hab hbL Jtarget hcollar Φ h0 h1 config H hRaw
    k A Cross Y K B
  let : Nonempty (Fin L → Fin q) := config
  have hspec :=
    exists_sharp_regional_family_of_scalar_budgets ell t etaLD w epsilon g
      hell hw hepsilon hgw ht0 ht hxi1 hsmall hfilter
      L q m a b hq hqm hab hbL Jtarget hcollar Φ h0 h1
  refine hspec.elim fun e hspec ↦ hspec.elim fun E0 hspec ↦ hspec.elim fun x hspec ↦
    hspec.elim fun z hspec ↦ hspec.elim fun hO hspec ↦ hspec.elim fun hC hspec ↦
    hspec.elim fun hxunit hspec ↦ hspec.elim fun hx hspec ↦ hspec.elim fun hlo hspec ↦
    hspec.elim fun hcenter hspec ↦ hspec.elim fun hzunit hspec ↦ hspec.elim fun hz hspec ↦
    hspec.elim fun hE0low hspec ↦ hspec.elim fun hE0 hspec ↦ hspec.elim fun hE04 hspec ↦
    hspec.elim fun hnorm hspec ↦ ?_
  have hfamilies := hspec
  have :=
    hRaw.spectralSpanLE_centered_ground_of_eq hO (∑ j, e j) E0 z
      hcenter hzunit hz hE0low
  refine this.elim fun hminimum hspec ↦ ?_
  have hidentity := hspec
  exact ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hminimum, hidentity, hfamilies⟩

end TNLean.MPS.AreaLaw
