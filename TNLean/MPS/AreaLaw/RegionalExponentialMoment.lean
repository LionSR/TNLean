/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalTruncationResidual
import TNLean.Lattice.DisjointRegionalGround
import QICLean.Analysis.ExponentialWeightRestriction
import QICLean.Analysis.EuclideanEigenvectorBasis

/-!
# Regional exponential moments on the original low-energy space

The actual interval split has at most two crossing bonds. Its attained
regional minima center the original Hamiltonian at a ground energy at most
two. The original nearest-neighbour imaginary-time estimate then controls
the exponential of the regional Hamiltonian on every original low-energy
window. No spectral gap or ground-space dimension is assumed.

This is a corrected auxiliary comparison for ALVV, arXiv:1602.08828v2,
`def:soft-trunc` and `lem:exp-approx`, lines 1175–1255. It retains the
regional operator in the exponential and does not compare higher powers of
noncommuting ordered operators. The full soft-truncation spectral comparison
is separate.

**Local fix (regional moments):** The first uniform energy estimate in the
source is false. The present result controls the actual regional exponential
on the original spectral space; it does not assert that printed estimate.
See `docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The original interval Hamiltonian has a dimension-independent exponential
moment on every original low-energy window. Regional minima and the centered
ground energy are attained and constructed before the approximate regional
energy, window width and all vectors. Empty and boundary intervals are included.
Auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`,
lines 1175–1255; the full soft spectral comparison is not asserted. -/
theorem exists_interval_regional_exponential_moment
    (L q p r : ℕ) (hq : 0 < q) (hpr : p ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, p, r, r, r, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ),
      let Hc := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      ∃ hHc : Hc.IsHermitian,
        star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        star z ⬝ᵥ z = 1 ∧ Hc *ᵥ z = (E0 : ℂ) • z ∧
        (Hc - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
        ∀ (eps eta : ℝ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 ≤ eta →
          let G := Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues (E0 + eta)
          ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
            (NormedSpace.exp ((1 / 8 : ℝ) •
              (A 1 - eps • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))))).domRestrict G‖ ≤
            5 * Real.exp ((17 + eta) / 8) := by
  classical
  intro k A
  let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦ Finset.univ.filter
    (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
  let J : Finset (Fin (L - 1)) := Finset.univ.filter
    (fun i ↦ i.val + 1 ∈ ({p, r, r, r} : Finset ℕ))
  let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, h i
  obtain ⟨_hk, hR, hAs, hAcap, hY, hYC, _hJ4, hH⟩ :=
    five_region_original_bond_data L q p r r r hpr le_rfl le_rfl hrL h hs h0 h1
  have hJ2 : J.card ≤ 2 := by
    have hc := Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
      (s := J) (t := {p, r})
      (fun i hi ↦ by
        change i.val + 1 ∈ ({p, r} : Finset ℕ)
        have hm := (Finset.mem_filter.mp hi).2
        simpa only [Finset.mem_insert, Finset.mem_singleton, or_self] using hm)
      (by
        intro i _ j _ hij
        apply Fin.ext
        change i.val + 1 = j.val + 1 at hij
        omega)
    exact hc.trans Finset.card_le_two
  let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
  obtain ⟨e, x, hxunit, hx, he, hclip⟩ := Matrix.exists_disjoint_regional_clipping_structure
    hq R A (fun j ↦ (I j).card) hR hAs (fun j ↦ (hAcap j).1)
      (fun j ↦ (hAcap j).2) Y J.card hY hYC
  let X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    ∑ j, (A j - (e j : ℂ) • 1)
  have hcenter : X + Y = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 := by
    dsimp only [X]
    rw [hH, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_smul]
    abel
  obtain ⟨hXpos, _hxzero, _hcomm, _horder, _hcap, _hnorm,
    E0, z, hzunit, hz, hElow, hE0, hEbound⟩ := hclip 0 le_rfl ∅
  change X.PosSemidef at hXpos
  change (X + Y) *ᵥ z = (E0 : ℂ) • z at hz
  change (X + Y - (E0 : ℂ) • 1).PosSemidef at hElow
  refine ⟨e, E0, x, z, ?_⟩
  intro Hc
  have hHc : Hc.IsHermitian := by
    have ht : (X + Y).IsHermitian := (hXpos.add hY).isHermitian
    rw [hcenter] at ht
    exact ht
  refine ⟨hHc, hxunit, hx, he, hzunit, ?_, ?_, hE0, ?_, ?_⟩
  · simpa only [hcenter] using hz
  · simpa only [hcenter] using hElow
  · exact hEbound.trans (by exact_mod_cast hJ2)
  intro eps eta hepslo _hepshi heta G
  let C : ℝ := 2 * (J.card : ℝ)
  let u : ℝ := E0 + eta + C + 1
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hC4 : C ≤ 4 := by
    have hcard : (J.card : ℝ) ≤ 2 := by exact_mod_cast hJ2
    dsimp only [C]
    linarith only [hcard]
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith only [hE0, heta, hC0]
  obtain ⟨_hXpos', _hxzero', hcomm, horder, _hcap', _hnorm', _hground⟩ := hclip u hu0 ∅
  change ∀ j, Commute X (A j) at hcomm
  change ∀ j v, 0 ≤ v → v ≤ u →
    v • Matrix.spectralProjectionGE (A j) (e j + v) ≤ X at horder
  have hEigen : ∀ j, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (X + Y) (hHc.eigenvectorBasis j) =
        (hHc.eigenvalues j : ℂ) • hHc.eigenvectorBasis j := by
    intro j
    rw [hcenter]
    exact hHc.toEuclideanCLM_eigenvectorBasis j
  have hgap : 2 * (J.card : ℝ) < u - (E0 + eta) := by
    dsimp only [u, C]
    linarith
  obtain ⟨Z, hZ, hZn⟩ := exists_nearestNeighbour_weighted_low_restriction
    (I 1) J h (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
    X (e 1) u (E0 + eta) (1 / 8) (by norm_num) (by norm_num)
    (hcomm 1) (horder 1 u hu0 le_rfl)
    hHc.eigenvectorBasis hHc.eigenvalues hEigen hgap
  change ‖Z‖ ≤ C / (u - (E0 + eta) - C) at hZn
  have hden : u - (E0 + eta) - C = 1 := by dsimp only [u]; ring
  rw [hden, div_one] at hZn
  have hA : (A 1).IsHermitian := (hAcap 1).1.isHermitian
  have hweight := Matrix.norm_exp_domRestrict_le_of_high_restriction
    (A 1) hA (e 1) u (1 / 8) C (by norm_num) G Z hZ hZn
  have hshift := Matrix.norm_shifted_exp_domRestrict_le
    (A 1) (e 1) u eps (1 / 8) (1 + C) G hweight
  have hE2 : E0 ≤ 2 := hEbound.trans (by exact_mod_cast hJ2)
  have hu : u ≤ 7 + eta := by dsimp only [u]; linarith only [hE2, hC4]
  have hexp : Real.exp ((1 / 8 : ℝ) * (e 1 + u - eps)) ≤
      Real.exp ((17 + eta) / 8) := by
    apply Real.exp_le_exp.mpr
    linarith only [hepslo, hu]
  refine hshift.trans ?_
  calc
    _ ≤ Real.exp ((17 + eta) / 8) * 5 :=
      mul_le_mul hexp (by linarith only [hC4]) (by linarith only [hC0])
        (Real.exp_nonneg _)
    _ = 5 * Real.exp ((17 + eta) / 8) := mul_comm _ _

end TNLean.MPS.AreaLaw
