/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates
import TNLean.MPS.AreaLaw.PhysicalLowEnergyFamily

/-!
# Improving viability between original low-energy windows

One common physical polynomial family acts on viable subspaces for the
original upper spectral window. Its improved subspaces are viable for the
original lower window, with the two buffered-comparison losses retained.
This is a bounded corollary supporting ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041.

**Scope restriction (buffers and geometry):** The theorem assumes `3*w < eta`
and the interior five-region geometry. It retains the exact finite filter
error and the losses of the two spectral comparisons; the source parameter
substitution, boundary and short regions, low-density induction and sampled
tree remain separate. See
`docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

**Local fix (closed cutoffs and filter sign):** The closed spectral cutoffs
and absolute-value Chebyshev estimates are those documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- One physical family improves viability from the original upper spectral
window to the original lower spectral window, with both losses from buffered
comparison displayed explicitly. The clipping, family, actual polynomial and
tensor factors are chosen before every viable subspace. ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041, and Lemma
`l:close`, lines 484–489. This buffered interior corollary does not assert
that the final error equals the clipped-target error. -/
theorem exists_five_region_original_low_energy_filter_family
    (L q a b ell : ℕ) (eta w epsilon : ℝ)
    (hbuffer : 3 * w < eta) (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
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
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (epsilon * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      let J := interval L (a + ell) (b + ell + 1)
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let D := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
          0 ≤ delta → 2 * (delta + epsilon) < 1 →
          Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
            ((Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues
              (E0 + eta)).map Tm.toLinearEquiv.toLinearMap) →
          let grow := ⨆ j : Fin N, S.map
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
          Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
              (2 * (Delta / (1 - 2 * (delta + epsilon)) ^ 2 + epsilon)) grow
              ((Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues
                (E0 + eta - 3 * w)).map Tm.toLinearEquiv.toLinearMap) := by
  classical
  intro k A Cross Y K B
  obtain ⟨t, e, E0, x, z, hO, hC, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_physical_low_energy_filter_family L q a b ell eta w epsilon
      hbuffer hw hepsilon hq hell hab hbL h hs h0 h1
  change (B t e ∅).IsHermitian at hO
  change (B t e K).IsHermitian at hC
  refine ⟨t, e, E0, x, z, hO, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, ?_⟩
  intro J beta tau U Phi Tm D Delta
  obtain ⟨_hnest, hupper, hlower, N, W, hN, _p, _hdegree, _hp0, _M, _hM, himprove⟩ := htargets
  refine ⟨N, W, hN, ?_⟩
  intro S delta hdelta hbudget hS
  have hstart : Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
      (2 * (delta + epsilon)) S
        ((Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
          (E0 + eta - w)).map Tm.toLinearEquiv.toLinearMap) :=
    Submodule.IsCloseTo.trans hS ((Submodule.isCloseTo_map_iff Tm).mpr hupper) hdelta
  obtain ⟨hdim, hraw⟩ := himprove S (2 * (delta + epsilon)) hstart hbudget
  exact ⟨hdim, Submodule.IsCloseTo.trans hraw
    ((Submodule.isCloseTo_map_iff Tm).mpr hlower)
    (div_nonneg (sq_nonneg _) (sq_nonneg _))⟩

end TNLean.MPS.AreaLaw
