/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationResidual
import QICLean.Analysis.SoftTruncationCoercivity

/-!
# The physical soft-truncation residual on the soft spectral window

The actual soft Hamiltonian is compared with a hard truncation only in matrix
order. The resulting high-projection coercivity controls an exponential moment
on its own low-energy space. The scalar remainder then bounds the difference
from the original Hamiltonian on that same space.

**Local fix (corrected residual comparison):** The scale is
positive and at most four times the positive order. The explicit reverse cutoff condition
is retained with correction `(t / 2) * (1 / 2) ^ m`.
This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc`
and `lem:exp-approx`, lines 1178–1255. It does not assert the printed first
uniform energy estimate or a spectral-subspace comparison. See
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual soft Hamiltonian has an attained ground energy and an
exponentially small residual on its own low-energy window. Original regional
minima are chosen before the approximate regional energy and order; the soft
ground data are chosen before the bandwidth. No moment, residual, gap or
ground-space-rank hypothesis is supplied. Corrected auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1178–1255. -/
theorem exists_interval_physical_scaled_soft_reverse_residual
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
      let H := ∑ i, h i
      let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
      ∃ _hHc : Hc.IsHermitian,
        star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        star z ⬝ᵥ z = 1 ∧ Hc *ᵥ z = (E0 : ℂ) • z ∧
        (Hc - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
        ∀ (eps : ℝ) (m : ℕ) (t : ℝ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 < m → 0 < t → t ≤ 4 * m →
          10 ≤ t / 2 →
          let alpha := t / 2 * (1 / 2 : ℝ) ^ m
          let Hsoft := H - A 1 + (eps : ℂ) • 1 +
            cfc (Real.softTruncation t m) (A 1 - (eps : ℂ) • 1)
          let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ (Es : ℝ) (zs : (Fin L → Fin q) → ℂ) (hHsc : Hsc.IsHermitian),
            Hsoft ≤ H ∧ star zs ⬝ᵥ zs = 1 ∧ Hsc *ᵥ zs = (Es : ℂ) • zs ∧
            (Hsc - (Es : ℂ) • 1).PosSemidef ∧ -alpha ≤ Es ∧ Es ≤ E0 ∧
            ∀ eta : ℝ, 0 ≤ eta → 17 + eta + alpha ≤ t / 2 →
              let G := Submodule.spectralSpanLE hHsc.eigenvectorBasis
                hHsc.eigenvalues (Es + eta)
              ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (H - Hsoft)).domRestrict G‖ ≤
                  80 * Real.exp ((17 + eta + alpha) / 8 - t / 16) := by
  classical
  intro k A
  let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦ Finset.univ.filter
    (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
  let J : Finset (Fin (L - 1)) := Finset.univ.filter
    (fun i ↦ i.val + 1 ∈ ({p, r, r, r} : Finset ℕ))
  let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, h i
  obtain ⟨hk, _hR, _hAs, hAcap, hY, _hYC, _hJ4, hH⟩ :=
    five_region_original_bond_data L q p r r r hpr le_rfl le_rfl hrL h hs h0 h1
  have hJ2 : J.card ≤ 2 := by
    have hc := Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
      (s := J) (t := {p, r})
      (fun i hi ↦ by
        change i.val + 1 ∈ ({p, r} : Finset ℕ)
        have hm := (Finset.mem_filter.mp hi).2
        simpa only [Finset.mem_insert, Finset.mem_singleton, or_self] using hm)
      (by intro i _ j _ hij; apply Fin.ext; change i.val + 1 = j.val + 1 at hij; omega)
    exact hc.trans Finset.card_le_two
  obtain ⟨e, E0, x, z, hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, hforward⟩ :=
    exists_interval_physical_scaled_soft_truncation_residual L q p r hq hpr hrL h hs h0 h1
  refine ⟨e, E0, x, z, ?_⟩
  intro H Hc
  refine ⟨hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, ?_⟩
  intro eps m t hepslo hepshi hm ht htm htau alpha Hsoft Hsc
  let F := (eps : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) +
    cfc (Real.softTruncation t m) (A 1 - (eps : ℂ) • 1)
  let Xs : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    ∑ j, ((if j = 1 then F else A j) - (e j : ℂ) • 1)
  have hsplit : Xs + Y = Hsc := by
    have hreplace : (∑ j : Fin 5, (if j = 1 then F else A j)) = ∑ j, A j + F - A 1 := by
      have hf : (fun j : Fin 5 ↦ if j = 1 then F else A j) =
          (fun j ↦ A j + if j = 1 then F - A 1 else 0) := by
        funext j
        by_cases hj : j = 1 <;> simp [hj]
      rw [hf, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      abel
    dsimp only [Xs]
    have heq : (∑ j, (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) =
        (((∑ j, e j) : ℝ) : ℂ) • 1 := by
      push_cast
      exact Finset.sum_smul.symm
    rw [Finset.sum_sub_distrib, hreplace, heq]
    change (∑ j, A j) + F - A 1 - (((∑ j, e j) : ℝ) : ℂ) • 1 + Y = _
    dsimp only [Hsc, Hsoft, F, H]
    rw [hH]
    abel
  have hcoerce (u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t / 2 - 10) :=
    Matrix.softTruncation_centered_coercivity A e 1 eps t u m
      (fun j ↦ (hAcap j).1.isHermitian) (fun j ↦ Matrix.le_iff.mpr (he j))
      hepslo hepshi ht hm hu hut
  have hXpos : (Xs + (alpha : ℂ) • 1).PosSemidef :=
    (hcoerce 0 le_rfl (by linarith only [htau])).1
  obtain ⟨hsoft, hsoftH, _hres⟩ := hforward eps 0 m t hepslo hepshi le_rfl hm ht htm
  have hHsc : Hsc.IsHermitian := hsoft.sub (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨Es, zs, hzs, hzsunit, hEslow⟩ := hHsc.exists_unit_eigenvector_le
  have hElowsoft : -alpha ≤ Es := by
    have hpos : (Hsc + (alpha : ℂ) • 1).PosSemidef := by
      have heq : Xs + (alpha : ℂ) • 1 + Y = Hsc + (alpha : ℂ) • 1 := by rw [← hsplit]; abel
      exact heq ▸ hXpos.add hY
    have hev : (Hsc + (alpha : ℂ) • 1) *ᵥ zs = ((Es + alpha : ℝ) : ℂ) • zs := by
      rw [add_mulVec, smul_mulVec, one_mulVec, hzs, Complex.ofReal_add, add_smul]
    have hb := hpos.nonneg_of_normalized_eigenvector (Es + alpha) zs hev hzsunit
    linarith only [hb]
  have hEs0 : Es ≤ E0 := by
    have hd : (Hc - Hsc).PosSemidef := by
      have hd : (H - Hsoft).PosSemidef := Matrix.le_iff.mp hsoftH
      have heq : Hc - Hsc = H - Hsoft := by dsimp only [Hc, Hsc]; abel
      exact heq.symm ▸ hd
    have hp : (Hc - (Es : ℂ) • 1).PosSemidef := by
      convert hd.add hEslow using 1
      abel
    have hv : (Hc - (Es : ℂ) • 1) *ᵥ z = ((E0 - Es : ℝ) : ℂ) • z := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, hz, Complex.ofReal_sub, sub_smul]
    exact sub_nonneg.mp (hp.nonneg_of_normalized_eigenvector (E0 - Es) z hv hzunit)
  refine ⟨Es, zs, hHsc, hsoftH, hzsunit, hzs, hEslow, hElowsoft, hEs0, ?_⟩
  intro eta heta hscale G
  let C : ℝ := 2 * (J.card : ℝ)
  let u : ℝ := Es + alpha + eta + C + 1
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hC4 : C ≤ 4 := by
    have hc : (J.card : ℝ) ≤ 2 := by exact_mod_cast hJ2
    dsimp only [C]
    linarith only [hc]
  obtain ⟨hu0, hut, hu, hgap, hden⟩ := Real.softTruncation_reverse_cutoff_bounds_of_scale
    m t Es eta C hElowsoft (hEs0.trans hE2) heta hC0 hC4 hscale
  have hpair := pairwise_commute_sum_internal_consecutive_regions k hk h hs
  have hscalar (a : ℂ) : Commute (a • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) (A 1) := by
    change (a • 1) * A 1 = A 1 * (a • 1)
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes a (A 1)
  have hF : Commute F (A 1) :=
    (hscalar eps).add_left (((Commute.refl (A 1)).sub_left (hscalar eps)).cfc_real _)
  have hcomm : Commute (Xs + (alpha : ℂ) • 1) (A 1) := by
    apply Commute.add_left ?_ (hscalar alpha)
    apply Commute.sum_left
    intro j _
    apply Commute.sub_left ?_ (hscalar (e j))
    by_cases hj : j = 1
    · simpa only [hj, ite_true] using hF
    · simpa only [hj, ite_false] using hpair hj
  let a := fun j ↦ hHsc.eigenvalues j + alpha
  have hEigen : ∀ j, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Xs + (alpha : ℂ) • 1 + Y) (hHsc.eigenvectorBasis j) =
        (a j : ℂ) • hHsc.eigenvectorBasis j := by
    intro j
    have heq : Xs + (alpha : ℂ) • 1 + Y = Hsc + (alpha : ℂ) • 1 := by rw [← hsplit]; abel
    rw [heq, map_add, map_smul, map_one]
    simp only [_root_.add_apply, _root_.smul_apply,
      one_apply_eq_self, hHsc.toEuclideanCLM_eigenvectorBasis j, a,
      Complex.ofReal_add, add_smul]
    rfl
  have hGeq : Submodule.spectralSpanLE hHsc.eigenvectorBasis a (Es + alpha + eta) = G := by
    apply Submodule.ext
    intro v
    change v ∈ Submodule.spectralSpanLE hHsc.eigenvectorBasis a (Es + alpha + eta) ↔
      v ∈ Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues (Es + eta)
    rw [Submodule.mem_spectralSpanLE_iff, Submodule.mem_spectralSpanLE_iff]
    constructor <;> intro hv j hj <;> apply hv j <;> dsimp only [a] at * <;> linarith
  obtain ⟨Z, hZ, hZn⟩ := exists_nearestNeighbour_weighted_low_restriction
    (I 1) J h (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
    (Xs + (alpha : ℂ) • 1) (e 1) u (Es + alpha + eta) (1 / 8)
    (by norm_num) (by norm_num) hcomm (hcoerce u hu0 hut).2
    hHsc.eigenvectorBasis a hEigen hgap
  change ‖Z‖ ≤ C / (u - (Es + alpha + eta) - C) at hZn
  rw [hden, div_one] at hZn
  have hA : (A 1).IsHermitian := (hAcap 1).1.isHermitian
  have hweight := Matrix.norm_exp_domRestrict_le_of_high_restriction
    (A 1) hA (e 1) u (1 / 8) C (by norm_num) _ Z hZ hZn
  rw [hGeq] at hweight
  have hshift := Matrix.norm_shifted_exp_domRestrict_le
    (A 1) (e 1) u eps (1 / 8) (1 + C) G hweight
  have hexp : Real.exp ((1 / 8 : ℝ) * (e 1 + u - eps)) ≤
      Real.exp ((17 + eta + alpha) / 8) := by
    apply Real.exp_le_exp.mpr
    linarith only [hepslo, hu]
  have hmoment : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (NormedSpace.exp ((1 / 8 : ℝ) • (A 1 - (eps : ℂ) • 1)))).domRestrict G‖ ≤
      5 * Real.exp ((17 + eta + alpha) / 8) := by
    simp only [Complex.coe_smul] at *
    refine hshift.trans ?_
    calc
      _ ≤ Real.exp ((17 + eta + alpha) / 8) * 5 :=
        mul_le_mul hexp (by linarith only [hC4]) (by linarith only [hC0])
          (Real.exp_nonneg _)
      _ = 5 * Real.exp ((17 + eta + alpha) / 8) := mul_comm _ _
  let U := A 1 - (eps : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
  have hU : U.PosSemidef := by
    have hmin : (e 1 : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A 1 := by
      simpa only [Complex.coe_smul] using Matrix.le_iff.mpr (he 1)
    have hep : eps • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ (e 1 : ℝ) • 1 :=
      smul_le_smul_of_nonneg_right hepshi zero_le_one
    apply Matrix.le_iff.mp
    simpa only [Complex.coe_smul] using hep.trans hmin
  have hdiff : H - Hsoft = U - cfc (Real.softTruncation t m) U := by
    dsimp only [Hsoft, U]
    abel
  rw [hdiff]
  refine (Matrix.norm_softTruncation_remainder_domRestrict_le_exp_weight_of_scale_le
    U hU m hm t ht htm G).trans ?_
  calc
    _ ≤ (16 * Real.exp (-t / 16)) *
        (5 * Real.exp ((17 + eta + alpha) / 8)) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = 80 * Real.exp ((17 + eta + alpha) / 8 - t / 16) := by
      rw [show (16 * Real.exp (-t / 16)) *
          (5 * Real.exp ((17 + eta + alpha) / 8)) =
          80 * (Real.exp (-t / 16) * Real.exp ((17 + eta + alpha) / 8)) by ring,
        ← Real.exp_add]
      congr 2
      ring

end TNLean.MPS.AreaLaw
