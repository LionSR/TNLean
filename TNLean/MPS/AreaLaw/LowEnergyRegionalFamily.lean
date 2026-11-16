/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLowEnergyFamily
import TNLean.MPS.AreaLaw.PolynomialFilterParameters

/-!
# Low-energy improving families on a region containing the five-region core

The actual clipped polynomial family on a five-region core extends to a
larger prescribed region. At most `2 * ell` additional sites are absorbed
in the count `(q * ell ^ 2) ^ (22 * ell)`. The same clipped Hamiltonian
supplies both physical spectral comparisons and the improving family,
chosen before every viable subspace. This supports ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.

**Scope restriction (five-region buffers):** The core geometry and the
strict spectral buffer `3 * w < eta` are explicit. This is an auxiliary
regional result, not the low-density bootstrap or the unrestricted source
theorem. See `docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

**Local fix (closed cutoffs and filter sign):** All spectral cutoffs are
closed, and the filter estimates concern the absolute value of the
Chebyshev polynomial. See
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
-/

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
theorem exists_five_region_low_energy_family_on_larger_region
    (L q a b ell : ℕ) (Jtarget : Finset (Fin L)) (eta w epsilon : ℝ)
    (hbuffer : 3 * w < eta) (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (hsub : interval L (a + ell) (b + ell + 1) ⊆ Jtarget)
    (hcollar : (Jtarget \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
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
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (epsilon * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      let J := Jtarget
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let D := (q * ell ^ 2) ^ (22 * ell)
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      lower ≤ higher ∧
      Submodule.IsCloseTo epsilon
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo epsilon lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) ∧
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
          Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
            (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ j : Fin N, S.map
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
          Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
              (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  intro k A Cross Y K B
  obtain ⟨t, e, E0, _x, z, hO, hC, htformula, ht, hcut, _hxunit, _hx, _hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_physical_low_energy_filter_family L q a b ell eta w epsilon
      hbuffer hw hepsilon hq hell hab hbL h hs h0 h1
  change (B t e ∅).IsHermitian at hO
  change (B t e K).IsHermitian at hC
  change ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) at hnorm
  refine ⟨t, e, E0, z, hO, hC, htformula, ht, hcut,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, ?_⟩
  intro lower higher J beta tau U Phi Tm D Delta
  obtain ⟨hnest, hupper, hlower, _holdfamily⟩ := htargets
  refine ⟨hnest, hupper, hlower, ?_⟩
  have hdegree : 1 ≤ ell ^ 2 := one_le_pow₀ hell
  obtain ⟨N, W, hNraw, hdecomp⟩ :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell hq hdegree hab hbL h hs e t J
  let J0 := interval L (a + ell) (b + ell + 1)
  let D0 := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
  change N ≤ D0 ^ 2 * q ^ (2 * (J0 \ J).card + 2 * (J \ J0).card) at hNraw
  have hdiff : J0 \ J = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  have hN : N ≤ D ^ 2 := by
    have hN' : N ≤ D0 ^ 2 * q ^ (2 * (J \ J0).card) := by
      simpa only [hdiff, Finset.card_empty, Nat.mul_zero, Nat.zero_add] using hNraw
    exact hN'.trans (collar_card_le_square_at_square_degree
      q ell (J \ J0).card (D0 ^ 2) hq hell hcollar le_rfl)
  obtain ⟨_p, _hpdegree, _hp0, _M, _hM, himprove⟩ :=
    exists_chebyshev_nested_viability_of_polynomial_family
      (B t e K) hC hC.eigenvectorBasis hC.eigenvalues
      (fun j ↦ hC.toEuclideanCLM_eigenvectorBasis j) W Tm
      (fun Q hQ ↦ (hdecomp Q hQ).imp fun M hM ↦ hM.2)
      (E0 + eta - 2 * w) (E0 + eta - w) (3 * t + 4 * (ell : ℝ))
      (by linarith only [hw])
      (by linarith only [hE04, hcut, ht, (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell),
        hw, hbuffer]) hnorm
  refine ⟨N, W, hN, ?_⟩
  simpa only [Delta,
    show (E0 + eta - w) - (E0 + eta - 2 * w) = w by ring] using himprove

end TNLean.MPS.AreaLaw
