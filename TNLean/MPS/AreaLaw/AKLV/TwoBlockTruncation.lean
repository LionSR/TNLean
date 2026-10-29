/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EuclideanEigenvectorBasis
import TNLean.MPS.AreaLaw.RegionalTruncationResidual
import Mathlib.Tactic.FinCases

/-!
# The actual two-outer-block truncation in the AKLV geometry

Three consecutive regions are formed from the original nearest-neighbour bonds. Only
the left and right regional sums are clipped; the middle sum and the two connecting
bonds are retained. The energy shifts are required only to be regional lower bounds.
The residual is derived on the actual low spectral space of every partial outer
clipping, without a supplied perturbation or closeness estimate.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, equation (5), the definition of `H^(t)`
and Theorem 6.1.

**Scope restriction (original nearest-neighbour data):** This module proves an
auxiliary residual for the actual two exterior clippings of the original bond sums.
It does not prove the source normalization, gap preservation, or normalized
ground-vector conclusion of Theorem 6.1. The remaining steps are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The three actual consecutive regional sums used for clipping the two exterior
blocks. AKLV, arXiv:1301.1162v1, Section 6.1, the definition of `H^(t)` after (5). -/
def aklvRegionalHamiltonians {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Fin 3 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  let k : Fin 4 → ℕ := ![0, l, r, L]
  fun j ↦ ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i

open Classical in
/-- The centered partially clipped Hamiltonian: the selector `T : Finset (Fin 2)`
can select only the left and right blocks. The middle block is never clipped.
AKLV, arXiv:1301.1162v1, Section 6.1, the definition of `H^(t)` after (5). -/
noncomputable def aklvTwoBlockHamiltonian {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (e : Fin 3 → ℝ) (t : ℝ) (T : Finset (Fin 2)) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  let A := aklvRegionalHamiltonians l r h
  let O := T.image (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3))
  (∑ j, ((if j ∈ O then cfc (fun x : ℝ ↦ min x (e j + t)) (A j) else A j) -
    (e j : ℂ) • 1)) +
    ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), h i

private theorem card_two_cut_crossing_le (L l r : ℕ) :
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))).card ≤ 2 := by
  have hcard := Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
    (s := Finset.univ.filter (fun i ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)))
    (t := {l, r}) (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
    (by
      intro i _ j _ hij
      apply Fin.ext
      change i.val + 1 = j.val + 1 at hij
      omega)
  exact hcard.trans (by simpa using Finset.card_insert_le l ({r} : Finset ℕ))

private theorem sum_three_regions_add_crossings {L q l r : ℕ} (hlr : l ≤ r)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ i, h i) = (∑ j, aklvRegionalHamiltonians l r h j) +
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), h i := by
  have hempty (c : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        c ≤ i.val ∧ i.val + 1 < c), h i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    omega
  have hsum := Finset.sum_five_internal_regions_add_crossings
    (L := L) (k1 := l) (k2 := l) (k3 := r) (k4 := r) le_rfl hlr le_rfl h
  rw [hsum]
  simp [aklvRegionalHamiltonians, Fin.sum_univ_three, hempty]
  abel

private theorem two_block_tail_coefficient_le {c ε t : ℝ} (hc : c ≤ 2) :
    (Real.exp (-(1 / 8) * (t - (ε + 5)) - 1) / (1 / 8)) *
      ((2 * c) / ((ε + 5) - ε - 2 * c)) ≤
        32 * Real.exp (-(t - ε) / 8) := by
  have hd : 1 ≤ (ε + 5) - ε - 2 * c := by linarith
  have hq : (2 * c) / ((ε + 5) - ε - 2 * c) ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < (ε + 5) - ε - 2 * c)).mpr
    linarith
  have hexp : -(1 / 8 : ℝ) * (t - (ε + 5)) - 1 =
      -3 / 8 + (-(t - ε) / 8) := by ring
  calc
    _ ≤ (Real.exp (-(1 / 8) * (t - (ε + 5)) - 1) / (1 / 8)) * 4 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 32 * Real.exp (-3 / 8) * Real.exp (-(t - ε) / 8) := by
      rw [hexp, Real.exp_add]
      ring
    _ ≤ 32 * 1 * Real.exp (-(t - ε) / 8) := by
      gcongr
      exact Real.exp_le_one_iff.mpr (by norm_num)
    _ = _ := by ring

open Classical in
/-- The actual two-outer-block truncation has exponentially small residual on each
actual partially clipped low-energy space. The only energy normalization assumptions
are the original regional lower bounds; no perturbation estimate or low-space witness
is supplied. AKLV, arXiv:1301.1162v1, Section 6.1, equation (5) and Theorem 6.1.
This bounded residual statement does not assert that theorem's gap preservation. -/
theorem norm_aklv_two_block_truncation_low_le {L q l r : ℕ}
    (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e : Fin 3 → ℝ) (ε t : ℝ) (hε : 0 ≤ ε) (ht : ε + 5 ≤ t)
    (he : ∀ j, (e j : ℂ) • 1 ≤ aklvRegionalHamiltonians l r h j) :
    let B := aklvTwoBlockHamiltonian l r h e t
    ∃ hB : ∀ T, (B T).IsHermitian,
      B ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      ∀ T : Finset (Fin 2),
        let G := Submodule.spectralSpanLE (hB T).eigenvectorBasis (hB T).eigenvalues ε
        ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (B ∅ - B Finset.univ)).domRestrict G)‖ ≤
            64 * Real.exp (-(t - ε) / 8) := by
  intro B
  let k : Fin 4 → ℕ := ![0, l, r, L]
  let A := aklvRegionalHamiltonians l r h
  let J := (Finset.univ : Finset (Fin (L - 1))).filter
    (fun i ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
  let Y := ∑ i ∈ J, h i
  let O : Finset (Fin 3) := {0, 2}
  let clip (T : Finset (Fin 2)) := T.image (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3))
  let X (T : Finset (Fin 2)) := ∑ j,
    ((if j ∈ clip T then cfc (fun x : ℝ ↦ min x (e j + t)) (A j) else A j) -
      (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  have hk : Monotone k := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [k]
    omega
  have hA (j : Fin 3) : (A j).IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hY : Y.PosSemidef := nonneg_iff_posSemidef.mp
    (show 0 ≤ Y from Finset.sum_nonneg fun i _ ↦ h0 i)
  have hB (T : Finset (Fin 2)) : (B T).IsHermitian := by
    obtain ⟨hX, _⟩ := Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t (clip T) hA he (0 : (Fin L → Fin q) → ℂ) (by intro j; simp) (by linarith)
    exact (hX.add hY).isHermitian
  have hcenter : B ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 := by
    have hsum := sum_three_regions_add_crossings hlr h
    simp only [B, aklvTwoBlockHamiltonian, Finset.image_empty, Finset.notMem_empty,
      ite_false, Finset.sum_sub_distrib]
    rw [hsum]
    push_cast
    rw [Finset.sum_smul]
    abel
  refine ⟨hB, hcenter, ?_⟩
  intro T G
  have hJ : (J.card : ℝ) ≤ 2 := by exact_mod_cast card_two_cut_crossing_le L l r
  have hEigen (v : Fin L → Fin q) :
      Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (X T + Y) ((hB T).eigenvectorBasis v) =
          ((hB T).eigenvalues v : ℂ) • (hB T).eigenvectorBasis v := by
    exact (hB T).toEuclideanCLM_eigenvectorBasis v
  have hsingle (j : Fin 3) :
      ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G)‖ ≤
          32 * Real.exp (-(t - ε) / 8) := by
    have htail := norm_consecutive_regional_truncation_low_le k hk h hs h0 h1
      e (clip T) j J (ε + 5) ε (1 / 8) t
      (by norm_num) (by norm_num) (by linarith) ht
      (hB T).eigenvectorBasis (hB T).eigenvalues he hEigen (by linarith)
    exact htail.trans (two_block_tail_coefficient_le hJ)
  have hsum := Matrix.norm_centered_clipping_discrepancy_domRestrict_le_sum
    A (fun j ↦ cfc (fun x : ℝ ↦ min x (e j + t)) (A j))
    (fun j ↦ (e j : ℂ)) O G
  have hfull : clip Finset.univ = O := by
    change (Finset.univ : Finset (Fin 2)).image
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) = {0, 2}
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hsumB : ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (B ∅ - B Finset.univ)).domRestrict G)‖ ≤
      ∑ j ∈ O, ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G)‖ := by
    change _ ≤ _ at hsum
    change ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      ((X ∅ + Y) - (X Finset.univ + Y))).domRestrict G)‖ ≤ _
    simpa only [X, hfull, clip, Finset.image_empty,
      Finset.notMem_empty, ite_false, add_sub_add_right_eq_sub] using hsum
  exact hsumB.trans (by
    calc
      _ ≤ ∑ _j ∈ O, (32 * Real.exp (-(t - ε) / 8)) :=
        Finset.sum_le_sum fun j _ ↦ hsingle j
      _ = _ := by norm_num [O, Finset.sum_const, nsmul_eq_mul]; ring)

end TNLean.MPS.AreaLaw
