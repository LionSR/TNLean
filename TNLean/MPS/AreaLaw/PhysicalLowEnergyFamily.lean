/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.LowEnergy.ChebyshevViability
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.PhysicalLowEnergyCloseness

import TNLean.MPS.AreaLaw.IndependentFiveRegionResidual
import TNLean.MPS.AreaLaw.ChebyshevNestedViability
import TNLean.MPS.AreaLaw.PhysicalBufferedTargets

/-!
# Improving families between buffered physical low-energy spaces

One actual three-bulk truncation supplies low-energy targets at distinct cutoffs.
Its common polynomial family contains the constructed Chebyshev filter,
which improves viability from the upper target to the lower one. The same
truncated Hamiltonian is used in the physical spectral comparisons and in
its tensor decomposition. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041.

The spectral buffers and five-region geometry are explicit. No low-density
bootstrap, efficient central tensor representation or merge-tree conclusion
is asserted. The false soft-cluster estimate is not used.

**Scope restriction (buffers and geometry):** The physical existence result
uses `3*w < eta` and the stated interior five-region geometry. The source
hypothesis at line 1027 gives `eta₁ ≥ 6*w` after the substitution
`w = mu/(3*log n)` for integers `n ≥ 2`. The substitution, finite short
chains and boundary regions are treated in `LowEnergyIntervalFamily`;
see `docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

**Local fix (closed cutoffs and filter sign):** The spectral estimates use
closed cutoffs; positivity of the unsquared Chebyshev filter is not claimed.
See the companion notes
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
-/

open ManyBody (interval)

open Matrix

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- One physically constructed three-bulk truncation has buffered nested
low-energy targets and one common operator family containing the actual
Chebyshev filter. Regional minima, ground data, spectral bases, polynomial,
tensor factors and both one-sided spectral comparisons are derived from
the original supported positive contractions. They precede every viable
subspace. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
This five-region statement retains its buffers and explicit filter error;
it is not the low-density bootstrap or the unrestricted source theorem. -/
theorem exists_five_region_physical_low_energy_filter_family
    (L q a b ell : ℕ) (eta w epsilon : ℝ)
    (hbuffer : 3 * w < eta) (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
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
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (epsilon * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      let J := interval L (a + ell) (b + ell + 1)
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      let D := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      lower ≤ higher ∧
      Submodule.IsCloseTo epsilon
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo epsilon lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) ∧
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
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
  intro k A Cross Y K B
  obtain ⟨t, e, E0, x, z, hO, hC, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_physical_buffered_targets L q a b ell eta w epsilon
      hbuffer hw hepsilon hq hell hab hbL Φ h0 h1
  change (B t e ∅).IsHermitian at hO
  change (B t e K).IsHermitian at hC
  change ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) at hnorm
  refine ⟨t, e, E0, x, z, hO, hC, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, ?_⟩
  intro lower higher J beta tau U Phi Tm D Delta
  obtain ⟨hnest, hupperClose, hlowerClose⟩ := htargets
  have heigen (j : Fin L → Fin q) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (B t e K) (hC.eigenvectorBasis j) =
        (hC.eigenvalues j : ℂ) • hC.eigenvectorBasis j :=
    hC.toEuclideanCLM_eigenvectorBasis j
  refine ⟨hnest, hupperClose, hlowerClose, ?_⟩
  have hdegree : 1 ≤ ell ^ 2 := by
    rw [pow_two]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hell hell
  have :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell hq hdegree hab hbL Φ e t J
  obtain ⟨N, W, hNraw, hdecomp⟩ := this
  have hN : N ≤ D ^ 2 := by
    simpa only [J, D, Finset.sdiff_self, Finset.card_empty, Nat.mul_zero, Nat.zero_add,
      pow_zero, mul_one] using hNraw
  have :=
    exists_chebyshev_nested_viability_of_polynomial_family
      (B t e K) hC hC.eigenvectorBasis hC.eigenvalues heigen W Tm
      (fun Q hQ ↦ (hdecomp Q hQ).imp fun M hM ↦ by
        -- The two tensor coordinates agree after reducible unfolding only.
        have hconj := hM.2
        with_reducible exact hconj)
      (E0 + eta - 2 * w) (E0 + eta - w) (3 * t + 4 * (ell : ℝ))
      (by linarith only [hw])
      (by linarith only [hE04, hcut, ht, (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell), hw, hbuffer]) hnorm
  obtain ⟨p, hpdegree, hp0, M, hM, himprove⟩ := this
  refine ⟨N, W, hN, p, hpdegree, hp0, M, hM, ?_⟩
  simpa only [Delta,
    show (E0 + eta - w) - (E0 + eta - 2 * w) = w by ring] using himprove

end TNLean.MPS.AreaLaw
