/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.DisjointRegionalGround
import TNLean.MPS.AreaLaw.AKLV.TwoBlockTruncation

/-!
# Actual residuals for one regional hard truncation

Original positive-contraction nearest-neighbour bonds determine three disjoint
regional sums and their genuine minimum energies. Only the middle regional sum
is clipped. Both actual restricted errors, on the original and clipped closed
low-energy spaces, are derived from those bonds at `t ≥ η + 7`.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3 and Proposition 4.4(1),
`local_alg_arxiv_v2.tex`, lines 873–921. The sufficient cutoff is explicit;
the unrestricted truncated-side claim under merely `t > η` is not asserted.
The companion spectral-window note is
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
Its pending cutoff revision, the separate source counterexample and the
acceptance gates for the physical prerequisites are recorded in
`docs/audits/2026-10-29_single_region_hard_truncation.md`.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
private theorem three_region_data {L q l r : ℕ} (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 4 → ℕ := ![0, l, r, L]
    let R := fun j : Fin 3 ↦ interval L (k j.castSucc) (k j.succ)
    let I := fun j : Fin 3 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := aklvRegionalHamiltonians l r h
    let J := Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    Monotone k ∧ (Pairwise fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A j) (R j)) ∧
      (∀ j, (A j).PosSemidef ∧ A j ≤ ((I j).card : ℝ) • 1) ∧
      Y.PosSemidef ∧ Y ≤ (J.card : ℝ) • 1 ∧ J.card ≤ 2 ∧
      (∑ i, h i) = (∑ j, A j) + Y := by
  intro k R I A J Y
  let k5 : Fin 6 → ℕ := ![0, l, l, r, r, L]
  let R5 := fun j : Fin 5 ↦ interval L (k5 j.castSucc) (k5 j.succ)
  let I5 := fun j : Fin 5 ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k5 j.castSucc ≤ i.val ∧ i.val + 1 < k5 j.succ)
  let A5 := fun j : Fin 5 ↦ ∑ i ∈ I5 j, h i
  let f := fun j : Fin 3 ↦ (⟨2 * j.val, by omega⟩ : Fin 5)
  obtain ⟨_hk5, hR5, hs5, hA5, hY, hYC, _hJ4, hsum5⟩ :=
    five_region_original_bond_data L q l l r r le_rfl hlr le_rfl hrL h hs h0 h1
  have hR (j : Fin 3) : R j = R5 (f j) := by fin_cases j <;> rfl
  have hI (j : Fin 3) : I j = I5 (f j) := by fin_cases j <;> rfl
  have hA (j : Fin 3) : A j = A5 (f j) := by fin_cases j <;> rfl
  have hJ5 : Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, l, r, r} : Finset ℕ)) = J := by
    ext i
    simp [J]
  have hJ : J.card ≤ 2 := by
    have hc := Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
      (s := J) (t := {l, r}) (fun _ hi ↦ (Finset.mem_filter.mp hi).2) (by
        intro i _ j _ hij
        apply Fin.ext
        change i.val + 1 = j.val + 1 at hij
        omega)
    exact hc.trans (by simpa using Finset.card_insert_le l ({r} : Finset ℕ))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hJ, ?_⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  · intro i j hij
    have hne : f i ≠ f j := by
      intro heq
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val at hv
      omega
    rw [hR i, hR j]
    exact hR5 hne
  · intro j
    rw [hA j, hR j]
    exact hs5 (f j)
  · intro j
    rw [hA j, hI j]
    exact hA5 (f j)
  · simpa only [hJ5] using hY
  · simpa only [hJ5] using hYC
  · have hempty (c : ℕ) :
        (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
          c ≤ i.val ∧ i.val + 1 < c), h i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      omega
    have hsum := hsum5
    rw [Fin.sum_univ_five] at hsum
    simpa [A5, I5, k5, A, aklvRegionalHamiltonians, Fin.sum_univ_three, J,
      hempty, add_assoc] using hsum

private theorem residual_coefficient_le {c E η t : ℝ} (hc : c ≤ 2) (hE : E ≤ 2) :
    (Real.exp (-(1 / 8) * (t - (η + 7)) - 1) / (1 / 8)) *
        ((2 * c) / ((η + 7) - (E + η) - 2 * c)) ≤
      32 * Real.exp (-(t - η) / 8) := by
  have hd : 1 ≤ (η + 7) - (E + η) - 2 * c := by linarith
  have hq : (2 * c) / ((η + 7) - (E + η) - 2 * c) ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < (η + 7) - (E + η) - 2 * c)).mpr
    linarith
  have hexp : -(1 / 8 : ℝ) * (t - (η + 7)) - 1 =
      -(t - η) / 8 + (-1 / 8) := by ring
  calc
    _ ≤ (Real.exp (-(1 / 8) * (t - (η + 7)) - 1) / (1 / 8)) * 4 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 32 * Real.exp (-(t - η) / 8) * Real.exp (-1 / 8) := by
      rw [hexp, Real.exp_add]
      ring
    _ ≤ 32 * Real.exp (-(t - η) / 8) * 1 := by
      gcongr
      exact Real.exp_le_one_iff.mpr (by norm_num)
    _ = _ := mul_one _

private theorem canonical_spectralSpanLE_eq {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues c =
      Submodule.spectralSpanLE
        ((isSymmetric_toEuclideanLin_iff.mpr hM).eigenvectorBasis finrank_euclideanSpace)
        hM.eigenvalues₀ c := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  unfold Submodule.spectralSpanLE
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e.symm i, hi, ?_⟩
    simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply, e]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · simpa only [IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hi
    · simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply,
        e, Equiv.symm_apply_apply]

open Classical in
/-- Actual single-middle-region hard truncation from the original chain, with both
restricted errors at the same original-ground-energy cutoff. Regional minima and
the original and clipped ground vectors are constructed. The sufficient cutoff
is `t ≥ η+7`; no clipped gap, perturbation bound or decomposition is assumed.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3 and Proposition 4.4(1),
lines 873–921, with the explicit sufficient cutoff and pending companion-note
revision recorded in `docs/audits/2026-10-29_single_region_hard_truncation.md`.
Empty regions and coincident or endpoint cuts are included. -/
theorem exists_single_region_hard_truncation_residuals {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let A := aklvRegionalHamiltonians l r h
    let J := Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ (∀ j, 0 ≤ e j) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 2 ∧
      ∀ η t : ℝ, 0 < η → η + 7 ≤ t →
        let F := energyTruncation (A 1) (e 1 + t) + A 0 + A 2 + Y -
          (((∑ j, e j) : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian)
          (E' : ℝ) (z' : (Fin L → Fin q) → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • 1).PosSemidef ∧ 0 ≤ E' ∧ E' ≤ 2 ∧
          let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
            finrank_euclideanSpace
          let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
            finrank_euclideanSpace
          ‖(toEuclideanCLM H - toEuclideanCLM F).domRestrict
            (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))‖ ≤
              32 * Real.exp (-(t - η) / 8) ∧
          ‖(toEuclideanCLM H - toEuclideanCLM F).domRestrict
            (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))‖ ≤
              32 * Real.exp (-(t - η) / 8) := by
  intro A J Y
  let k : Fin 4 → ℕ := ![0, l, r, L]
  let R := fun j : Fin 3 ↦ interval L (k j.castSucc) (k j.succ)
  let I := fun j : Fin 3 ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
  obtain ⟨hk, hR, hsA, hA, hY, hYC, hJ, hsum⟩ :=
    three_region_data hlr hrL h hs h0 h1
  obtain ⟨e, x, hx, hxe, he, hclip⟩ :=
    Matrix.exists_disjoint_regional_clipping_structure hq R A (fun j ↦ (I j).card)
      hR hsA (fun j ↦ (hA j).1) (fun j ↦ (hA j).2) Y J.card hY hYC
  let B (t : ℝ) (T : Finset (Fin 3)) :=
    (∑ j, ((if j ∈ T then energyTruncation (A j) (e j + t) else A j) -
      (e j : ℂ) • 1)) + Y
  let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
  have hcenter (t : ℝ) : B t ∅ = H := by
    simp only [B, H, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsum]
    push_cast
    rw [Finset.sum_smul]
    abel
  obtain ⟨hX0, _hx0, _hc0, _ho0, _hcap0, _hnorm0,
      E, z, hz, hHz, hE, hE0, hEJ⟩ := hclip 0 le_rfl ∅
  have hHpos : H.PosSemidef := by
    rw [← hcenter 0]
    exact hX0.add hY
  have hHz' : H *ᵥ z = (E : ℂ) • z := by
    simpa only [← hcenter 0] using hHz
  have hE' : (H - (E : ℂ) • 1).PosSemidef := by
    simpa only [← hcenter 0] using hE
  refine ⟨e, x, z, E, hx, hxe, he,
    fun j ↦ (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hxe j) hx,
    hz, hHz', hE', hE0, hEJ.trans (by exact_mod_cast hJ), ?_⟩
  intro η t hη ht F
  have ht0 : 0 ≤ t := by linarith
  have hmiddle : B t {1} = F := by
    simp only [B, Fin.sum_univ_three, Finset.mem_singleton, Fin.reduceEq, ite_true,
      ite_false]
    dsimp only [F]
    rw [Fin.sum_univ_three]
    push_cast
    rw [add_smul, add_smul]
    abel
  have hdiff : H - F = A 1 - energyTruncation (A 1) (e 1 + t) := by
    dsimp only [H, F]
    rw [hsum, Fin.sum_univ_three]
    abel
  have hFH : F ≤ H := Matrix.le_iff.mpr (by
    rw [hdiff]
    exact Matrix.le_iff.mp ((hA 1).1.isHermitian.energyTruncation_le (e 1 + t)))
  obtain ⟨hX1, _hx1, _hc1, _ho1, _hcap1, _hnorm1,
      E', z', hz', hFz', hE', hE'0, hE'J⟩ := hclip t ht0 {1}
  have hFpos : F.PosSemidef := by
    rw [← hmiddle]
    exact hX1.add hY
  let hH := hHpos.isHermitian
  let hF := hFpos.isHermitian
  refine ⟨hH, hF, E', z', hFH, hz', ?_, ?_, hE'0,
    hE'J.trans (by exact_mod_cast hJ), ?_⟩
  · simpa only [← hmiddle] using hFz'
  · simpa only [← hmiddle] using hE'
  · have heorder (j : Fin 3) : (e j : ℂ) • 1 ≤ A j := Matrix.le_iff.mpr (he j)
    have hJreal : (J.card : ℝ) ≤ 2 := by exact_mod_cast hJ
    have hE2 : E ≤ 2 := hEJ.trans (by exact_mod_cast hJ)
    have hgap : 2 * (J.card : ℝ) < (η + 7) - (E + η) := by linarith
    have hres (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hM : M.IsHermitian)
        (T : Finset (Fin 3)) (hBM : B t T = M) :
        ‖(toEuclideanCLM H - toEuclideanCLM F).domRestrict
          (Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues (E + η))‖ ≤
            32 * Real.exp (-(t - η) / 8) := by
      have hEigen (v : Fin L → Fin q) : toEuclideanCLM (B t T)
          (hM.eigenvectorBasis v) = (hM.eigenvalues v : ℂ) • hM.eigenvectorBasis v := by
        rw [hBM]
        exact hM.toEuclideanCLM_eigenvectorBasis v
      have hsingle := norm_consecutive_regional_truncation_low_le k hk h hs h0 h1
        e T 1 J (η + 7) (E + η) (1 / 8) t (by norm_num) (by norm_num)
        (by linarith) ht hM.eigenvectorBasis hM.eigenvalues heorder hEigen hgap
      have hsingle' := hsingle.trans (residual_coefficient_le hJreal hE2)
      simpa only [← map_sub, hdiff] using hsingle'
    constructor
    · rw [← canonical_spectralSpanLE_eq hH (E + η)]
      exact hres H hH ∅ (hcenter t)
    · rw [← canonical_spectralSpanLE_eq hF (E + η)]
      exact hres F hF {1} hmiddle

end TNLean.MPS.AreaLaw.ALVV
