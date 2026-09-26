/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DiagonalPolar

/-!
# The polar decomposition of an orthogonal sum

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write the blocked tensor `B` of a tensor that is not normal as
a direct sum over its normal blocks and assert "Since `V` is an isometry, `P` inherits the block
structure of `A`" (eq. (S5)). This file proves the matrix statement behind that sentence under
the hypothesis that makes it true: if `B = ∑ⱼ cⱼ Bⱼ Kⱼᴴ` with `cⱼ > 0`, isometries `Kⱼ` with
orthogonal ranges, and `Bⱼᴴ Bⱼ' = 0` for `j ≠ j'`, then
`V = ∑ⱼ Vⱼ Kⱼᴴ` and `P = ∑ⱼ cⱼ Kⱼ Pⱼ Kⱼᴴ`, where `Bⱼ = Vⱼ Pⱼ` are the polar decompositions of
the summands (`Matrix.polarIso_sum_of_orthogonal`, `Matrix.polarPos_sum_of_orthogonal`).
Without `Bⱼᴴ Bⱼ' = 0` the conclusion fails
(`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`).

## Main declarations

* `Matrix.exists_polarIso_eq_mul` — the partial isometry is `V = M R` for some `R`.
* `Matrix.conjTranspose_polarIso_mul_eq_zero`,
  `Matrix.conjTranspose_polarIso_mul_polarIso_eq_zero` — orthogonality `Mᴴ M' = 0` passes to
  the partial isometries.
* `Matrix.polarIso_sum_of_orthogonal`, `Matrix.polarPos_sum_of_orthogonal` — the polar
  decomposition of an orthogonal sum.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eq. (S5).
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- If the range of `X` lies in the range of `Y`, then `X = Y R` for some `R`. -/
theorem exists_mul_eq_of_range_le {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']
    {X : Matrix κ ρ' ℂ} {Y : Matrix κ ρ ℂ}
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin) :
    ∃ R : Matrix ρ ρ' ℂ, Y * R = X := by
  classical
  choose u hu using fun c : ρ' => h ⟨Pi.single c 1, rfl⟩
  refine ⟨of fun a c => u c a, ?_⟩
  ext a c
  have h1 := congrFun (hu c) a
  simp only [mulVecLin_apply, mulVec, dotProduct] at h1
  rw [mul_apply]
  simpa [Pi.single_apply] using h1

/-- The positive part has a right factor onto the support projector: `P R = Π` for some `R`. -/
theorem exists_polarPos_mul_eq_polarSupport (M : Matrix ι κ ℂ) :
    ∃ R : Matrix κ κ ℂ, polarPos M * R = polarSupport M :=
  exists_mul_eq_of_range_le (range_polarSupport M).le

/-- The partial isometry of the polar decomposition factors through the matrix: `V = M R` for
some `R` (arXiv:2307.01696, Supplemental Material, the polar decomposition `B = V P` with
`V†V = Π`). -/
theorem exists_polarIso_eq_mul (M : Matrix ι κ ℂ) : ∃ R : Matrix κ κ ℂ, polarIso M = M * R := by
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
  refine ⟨R, ?_⟩
  have hV : polarIso M * polarSupport M = polarIso M :=
    mul_eq_self_of_conjTranspose_mul_self_eq (conjTranspose_polarIso_mul_polarIso M)
      (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M)
  rw [← hV, ← hR, ← Matrix.mul_assoc, polarIso_mul_polarPos]

variable {κ' : Type*} [Fintype κ'] [DecidableEq κ']

omit [Fintype κ'] [DecidableEq κ'] in
/-- If `Mᴴ M' = 0`, then `Vᴴ M' = 0` for the partial isometry `V` of `M`. -/
theorem conjTranspose_polarIso_mul_eq_zero {M : Matrix ι κ ℂ} {M' : Matrix ι κ' ℂ}
    (h : Mᴴ * M' = 0) : (polarIso M)ᴴ * M' = 0 := by
  obtain ⟨R, hR⟩ := exists_polarIso_eq_mul M
  rw [hR, conjTranspose_mul, Matrix.mul_assoc, h, Matrix.mul_zero]

/-- If `Mᴴ M' = 0`, the partial isometries of `M` and `M'` have orthogonal ranges:
`Vᴴ V' = 0`. -/
theorem conjTranspose_polarIso_mul_polarIso_eq_zero {M : Matrix ι κ ℂ} {M' : Matrix ι κ' ℂ}
    (h : Mᴴ * M' = 0) : (polarIso M)ᴴ * polarIso M' = 0 := by
  obtain ⟨R', hR'⟩ := exists_polarIso_eq_mul M'
  rw [hR', ← Matrix.mul_assoc, conjTranspose_polarIso_mul_eq_zero h, Matrix.zero_mul]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A product of two finite sums whose cross terms vanish is the sum of the diagonal
products. -/
theorem sum_mul_sum_of_mul_eq_zero {β α γ : Type*} [Fintype β] [Fintype κ]
    {X : β → Matrix α κ ℂ} {Y : β → Matrix κ γ ℂ} (h : ∀ j j', j ≠ j' → X j * Y j' = 0) :
    (∑ j, X j) * (∑ j, Y j) = ∑ j, X j * Y j := by
  classical
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_sum, Finset.sum_eq_single j (fun j' _ hj' => h j j' (Ne.symm hj'))
    (fun hj => absurd (Finset.mem_univ j) hj)]

variable {β : Type*} [Fintype β] {κj : β → Type*} [∀ j, Fintype (κj j)]
  [∀ j, DecidableEq (κj j)]

/-- **The polar decomposition of an orthogonal sum.** Let `B = ∑ⱼ cⱼ Bⱼ Kⱼᴴ` with `cⱼ > 0`,
isometries `Kⱼ` with orthogonal ranges (`Kⱼᴴ Kⱼ = 1`, `Kⱼᴴ Kⱼ' = 0` for `j ≠ j'`), and
`Bⱼᴴ Bⱼ' = 0` for `j ≠ j'`. Then the partial isometry of `B` is `∑ⱼ Vⱼ Kⱼᴴ` and its positive part
is `∑ⱼ cⱼ Kⱼ Pⱼ Kⱼᴴ`, with `Bⱼ = Vⱼ Pⱼ`.

This is the block form of the positive part asserted in arXiv:2307.01696, Supplemental Material,
eq. (S5), for blocks of multiplicity one whose states are orthogonal; the source does not state
the orthogonality, without which the block form fails
(`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`). -/
theorem polarIso_sum_of_orthogonal {B : (j : β) → Matrix ι (κj j) ℂ}
    (hB : ∀ j j', j ≠ j' → (B j)ᴴ * B j' = 0) {c : β → ℝ} (hc : ∀ j, 0 < c j)
    {K : (j : β) → Matrix κ (κj j) ℂ} (hK : ∀ j, (K j)ᴴ * K j = 1)
    (hK' : ∀ j j', j ≠ j' → (K j)ᴴ * K j' = 0) :
    polarIso (∑ j, (c j : ℂ) • (B j * (K j)ᴴ)) = ∑ j, polarIso (B j) * (K j)ᴴ ∧
      polarPos (∑ j, (c j : ℂ) • (B j * (K j)ᴴ)) =
        ∑ j, (c j : ℂ) • (K j * polarPos (B j) * (K j)ᴴ) := by
  set W := ∑ j, polarIso (B j) * (K j)ᴴ
  set Q := ∑ j, (c j : ℂ) • (K j * polarPos (B j) * (K j)ᴴ)
  set E := ∑ j, K j * polarSupport (B j) * (K j)ᴴ
  choose R hR using fun j => exists_polarPos_mul_eq_polarSupport (B j)
  set R' := ∑ j, ((c j : ℂ)⁻¹) • (K j * R j * (K j)ᴴ)
  -- Products are normalized to right-associated form; every cross term contains `Kⱼᴴ Kⱼ'`.
  have hKr : ∀ j j' (Y : Matrix (κj j') κ ℂ), j ≠ j' →
      (K j)ᴴ * (K j' * Y) = 0 := fun j j' Y h => by
    rw [← Matrix.mul_assoc, hK' j j' h, Matrix.zero_mul]
  have hKd : ∀ j (Y : Matrix (κj j) κ ℂ), (K j)ᴴ * (K j * Y) = Y :=
    fun j Y => by rw [← Matrix.mul_assoc, hK j, Matrix.one_mul]
  have hVr : ∀ j j' (Y : Matrix (κj j') κ ℂ), j ≠ j' →
      (polarIso (B j))ᴴ * (polarIso (B j') * Y) = 0 := fun j j' Y h => by
    rw [← Matrix.mul_assoc, conjTranspose_polarIso_mul_polarIso_eq_zero (hB j j' h),
      Matrix.zero_mul]
  have hVd : ∀ j (Y : Matrix (κj j) κ ℂ),
      (polarIso (B j))ᴴ * (polarIso (B j) * Y) = polarSupport (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, conjTranspose_polarIso_mul_polarIso]
  have hVP : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarIso (B j) * (polarPos (B j) * Y) = B j * Y := fun j Y => by
    rw [← Matrix.mul_assoc, polarIso_mul_polarPos]
  have hSS : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarSupport (B j) * (polarSupport (B j) * Y) = polarSupport (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, polarSupport_mul_polarSupport]
  have hSP : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarSupport (B j) * (polarPos (B j) * Y) = polarPos (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, polarSupport_mul_polarPos]
  have hPR : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarPos (B j) * (R j * Y) = polarSupport (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, hR j]
  -- `B = W Q`.
  have hWQ : ∑ j, (c j : ℂ) • (B j * (K j)ᴴ) = W * Q := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_smul, Matrix.mul_assoc, hKr j j' _ h, Matrix.mul_zero, smul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_smul, Matrix.mul_assoc, hKd, hVP]
  -- `Q ≥ 0`.
  have hQ : Q.PosSemidef := posSemidef_sum _ fun j _ =>
    ((posSemidef_polarPos (B j)).mul_mul_conjTranspose_same (K j)).smul
      (Complex.zero_le_real.mpr (hc j).le)
  -- `Wᴴ W = E`.
  have hWW : Wᴴ * W = E := by
    rw [conjTranspose_sum]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_assoc, hVr j j' _ h, Matrix.mul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc, hVd]
  -- `E` is a Hermitian idempotent.
  have hE : E.IsHermitian := by
    rw [IsHermitian, conjTranspose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      (isHermitian_polarSupport (B j)).eq, Matrix.mul_assoc]
  have hEE : E * E = E := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_assoc, hKr j j' _ h, Matrix.mul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc, hKd, hSS]
  -- `E` and `Q` have the same range.
  have hEQ : E * Q = Q := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_smul, Matrix.mul_assoc, hKr j j' _ h, Matrix.mul_zero, smul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_smul, Matrix.mul_assoc, hKd, hSP]
  have hQR : Q * R' = E := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hKr j j' _ h,
        Matrix.mul_zero, smul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcj : (c j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc j).ne'
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hKd, hPR, smul_smul,
      inv_mul_cancel₀ hcj, one_smul]
  have hran := range_mulVecLin_eq_of_mul_eq hEQ hQR
  exact ⟨polarIso_eq_of_eq_mul hWQ hQ hWW hE hEE hran,
    polarPos_eq_of_eq_mul hWQ hQ hWW hE hEE hran⟩

end Matrix
