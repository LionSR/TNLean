/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.HardTruncationResidual
import QICLean.Analysis.ShiftedSoftHardTruncation
import QICLean.Analysis.SoftTruncationRestrictedResidual

/-!
# Actual original-to-soft regional residual

The original positive-contraction nearest-neighbour interactions determine the regional
minimum energies and the centered original Hamiltonian. On its actual closed low-energy
space, one centered regional soft replacement has a residual controlled by the derived
physical hard tail and the explicit independent-scale polynomial remainder.
This is a one-direction auxiliary for ALVV, arXiv:1602.08828v2, `lem:exp-approx`,
lines 1195–1255, and `t:aisefficient`, lines 1373–1420.

**Scope restriction (attained energy centers):** the regional centers are constructed exact
minimum energies. The result does not treat every estimated center allowed by the source's
interval of width ten; see `docs/paper-gaps/alvv16_soft_regional_residuals.tex`.

**Local fix (cutoff and residual):** the hard cutoff is at least the original low-energy
width plus seven, and the additional soft error is `(t/m)*(T/t)^m`. No printed uniform
energy estimate, reverse soft-to-original comparison, efficient filter or running-time
conclusion is asserted. The source-error records remain in
`docs/paper-gaps/alvv16_cluster_approximation.tex` and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- Actual regional minima and the original ground energy are chosen from the local bonds
before the width, hard cutoff, soft scale and order. The resulting soft replacement is
Hermitian and below the original centered Hamiltonian, with its actual original-side
restricted residual derived. Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`,
lines 1195–1255, and `t:aisefficient`, lines 1373–1420. -/
theorem exists_single_region_original_soft_truncation_residual {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, aklvRegionalHamiltonians l r h j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (aklvRegionalHamiltonians l r h j - (e j : ℂ) • 1).PosSemidef) ∧
      (∀ j, 0 ≤ e j) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 2 ∧
      ∃ hH : H.IsHermitian,
        ∀ η T t : ℝ, ∀ m : ℕ, 0 < η → η + 7 ≤ T → 0 < t → 1 ≤ m →
          let X := aklvRegionalHamiltonians l r h 1 - (e 1 : ℂ) • 1
          let G := H - X + cfc (Real.softTruncation t m) X
          G.IsHermitian ∧ G ≤ H ∧
            ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
                (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) G).domRestrict
              (Submodule.spectralSpanLE
                ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
                  finrank_euclideanSpace) hH.eigenvalues₀ (E + η))‖ ≤
              32 * Real.exp (-(T - η) / 8) + (t / (m : ℝ)) * (T / t) ^ m := by
  obtain ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hE, hE0, hE2, hhard⟩ :=
    exists_single_region_hard_truncation_residuals hq hlr hrL h hs h0 h1
  let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
  have hraw : (∑ i, h i).IsHermitian :=
    (Matrix.posSemidef_sum _ (fun i _ ↦ (h0 i).posSemidef)).isHermitian
  have hH : H.IsHermitian := hraw.sub
    (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
  refine ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hE, hE0, hE2, hH, ?_⟩
  intro η T t m hη hT ht hm X G
  let A := aklvRegionalHamiltonians l r h
  let Y := ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), h i
  let F := energyTruncation (A 1) (e 1 + T) + A 0 + A 2 + Y -
    (((∑ j, e j) : ℝ) : ℂ) • 1
  let S := Submodule.spectralSpanLE
    ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
      finrank_euclideanSpace) hH.eigenvalues₀ (E + η)
  have hX : X.PosSemidef := he 1
  have hA1 : (A 1).IsHermitian := by
    dsimp only [A, aklvRegionalHamiltonians]
    exact (Matrix.posSemidef_sum _ (fun i _ ↦ (h0 i).posSemidef)).isHermitian
  have hG : G.IsHermitian :=
    (hH.sub hX.isHermitian).add (cfc_predicate (Real.softTruncation t m) X)
  have hsoft : cfc (Real.softTruncation t m) X ≤ X := by
    conv_rhs => rw [← cfc_id' ℝ X hX.isHermitian.isSelfAdjoint]
    exact cfc_mono (fun u hu ↦ (Real.softTruncation_bounds t m u ht hm
      (spectrum_nonneg_of_nonneg hX.nonneg hu)).2.1)
      (X.finite_real_spectrum.continuousOn _) (X.finite_real_spectrum.continuousOn _)
  refine ⟨hG, ?_, ?_⟩
  · have hd : G = H + (cfc (Real.softTruncation t m) X - X) := by
      dsimp only [G, H]
      abel
    rw [hd]
    exact add_le_of_nonpos_right (sub_nonpos.mpr hsoft)
  · obtain ⟨_hH, _hF, _E', _z', _horder, _hz', _hFz', _hE', _hE'0, _hE'2,
        hres, _hreverse⟩ := hhard η T hη hT
    change ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) F).domRestrict S‖ ≤
      32 * Real.exp (-(T - η) / 8) at hres
    have hsum : (∑ i, h i) = (∑ j, A j) + Y :=
      sum_three_regions_add_crossings hlr h
    have hdiff : H - F = X - energyTruncation X T := by
      rw [hA1.energyTruncation_sub_smul_one (e 1) T]
      dsimp only [H, F, X]
      rw [hsum, Fin.sum_univ_three]
      abel
    have hdsoft : H - G = X - cfc (Real.softTruncation t m) X := by
      dsimp only [G, H]
      abel
    have hT0 : 0 ≤ T := by linarith only [hη, hT]
    change ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G).domRestrict S‖ ≤
      32 * Real.exp (-(T - η) / 8) + (t / (m : ℝ)) * (T / t) ^ m
    have hbound := hX.norm_softTruncation_residual_domRestrict_le t m T ht hm hT0 S
    rw [← hdsoft, ← hdiff] at hbound
    simp only [map_sub] at hbound
    linarith only [hbound, hres]

end TNLean.MPS.AreaLaw.ALVV
