/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import QICLean.Channel.Semigroup.PauliDissipation
import TNLean.Algebra.ComplexSqrt
import TNLean.Wielandt.Primitivity.Definitions

/-!
# The three-Pauli channel has different primitivity and matrix-span indices

The qubit Kraus family consists of the three Pauli matrices divided by `√3`.
Its one-step images span the qubit space at every nonzero vector, whereas its
one-letter matrix span is traceless. Products of two letters span all matrices.
Thus its primitivity index is one and its full-Kraus-rank index is two.

## Main definitions

* `MPSTensor.threePauliTensor`: the normalized three-Pauli Kraus family.

## Main results

* `MPSTensor.threePauliTensor_normalized`: trace-preserving normalization.
* `MPSTensor.threePauliTensor_vectorSpreadSpan_one`: one-step spreading.
* `MPSTensor.threePauliTensor_wordSpan_one_ne_top`: the one-letter obstruction.
* `MPSTensor.threePauliTensor_wordSpan_two`: exact-length two-letter spanning.
* `MPSTensor.threePauliTensor_qIndex`, `MPSTensor.threePauliTensor_iIndex`: the two indices.

## References

* Sanz, Pérez-García, Wolf and Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347, the Pauli example following Proposition 2;
  `Papers/0909.5347/main.tex`, lines 496–499.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

private def pauliNormalization : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)⁻¹

private theorem pauliNormalization_ne_zero : pauliNormalization ≠ 0 :=
  inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))

private theorem pauliNormalization_mul_self :
    pauliNormalization * pauliNormalization = (3 : ℂ)⁻¹ := by
  simpa [pauliNormalization] using Complex.ofReal_sqrt_inv_mul_self 3 (by norm_num)

private theorem star_pauliNormalization : star pauliNormalization = pauliNormalization := by
  simp [pauliNormalization]

/-- The Kraus matrices `σx/√3`, `σy/√3`, `σz/√3` from the strict-index example
in arXiv:0909.5347, lines 496–499. -/
def threePauliTensor : MPSTensor 3 2 := fun k ↦ pauliNormalization • SpinCover.pauli k

/-- The three-Pauli family is trace preserving, as required by the channel example
in arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_normalized :
    ∑ k : Fin 3, (threePauliTensor k)ᴴ * threePauliTensor k = 1 := by
  simp_rw [threePauliTensor, Matrix.conjTranspose_smul, star_pauliNormalization,
    PauliDissipation.pauli_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, pauliNormalization_mul_self, PauliDissipation.pauli_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply]

/-- Every nonzero qubit vector is spanned by its three one-letter Pauli images.
This is the `q = 1` assertion of arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_vectorSpreadSpan_one (φ : Fin 2 → ℂ) (hφ : φ ≠ 0) :
    Kraus.vectorSpreadSpan threePauliTensor φ 1 = ⊤ := by
  classical
  let W := Kraus.vectorSpreadSpan threePauliTensor φ 1
  have hPauli (k : Fin 3) : SpinCover.pauli k *ᵥ φ ∈ W := by
    apply (W.smul_mem_iff pauliNormalization_ne_zero).mp
    simpa [threePauliTensor, Kraus.evalWord, Matrix.smul_mulVec] using
      Kraus.evalWord_mulVec_mem_vectorSpreadSpan threePauliTensor φ [k]
  have hfirst : (2 * φ 1) • ![(1 : ℂ), 0] ∈ W := by
    convert W.add_mem (hPauli 0) (W.smul_mem Complex.I (hPauli 1)) using 1
    ext i
    fin_cases i <;>
      simp [SpinCover.pauli, Matrix.vecHead, Matrix.vecTail,
        smul_eq_mul, ← mul_assoc] <;> ring
  have hsecond : (2 * φ 0) • ![(0 : ℂ), 1] ∈ W := by
    convert W.sub_mem (hPauli 0) (W.smul_mem Complex.I (hPauli 1)) using 1
    ext i
    fin_cases i <;>
      simp [SpinCover.pauli, Matrix.vecHead, Matrix.vecTail,
        smul_eq_mul, ← mul_assoc] <;> ring
  have haxes : ![(1 : ℂ), 0] ∈ W ∧ ![(0 : ℂ), 1] ∈ W := by
    by_cases hzero : φ 0 = 0
    · have hone : φ 1 ≠ 0 := by
        intro hone
        apply hφ
        ext i
        fin_cases i <;> simp [hzero, hone]
      have he₀ := (W.smul_mem_iff (mul_ne_zero two_ne_zero hone)).mp hfirst
      refine ⟨he₀, ?_⟩
      apply (W.smul_mem_iff hone).mp
      convert W.sub_mem (W.smul_mem (φ 0) he₀) (hPauli 2) using 1
      ext i
      fin_cases i <;>
        simp [SpinCover.pauli, Matrix.vecHead, Matrix.vecTail,
          smul_eq_mul]
    · have he₁ := (W.smul_mem_iff (mul_ne_zero two_ne_zero hzero)).mp hsecond
      refine ⟨?_, he₁⟩
      apply (W.smul_mem_iff hzero).mp
      convert W.add_mem (hPauli 2) (W.smul_mem (φ 1) he₁) using 1
      ext i
      fin_cases i <;>
        simp [SpinCover.pauli, Matrix.vecHead, Matrix.vecTail,
          smul_eq_mul]
  apply top_unique
  intro v _
  have hv : v = v 0 • ![(1 : ℂ), 0] + v 1 • ![(0 : ℂ), 1] := by
    ext i
    fin_cases i <;> simp [smul_eq_mul]
  rw [hv]
  exact W.add_mem (W.smul_mem _ haxes.1) (W.smul_mem _ haxes.2)

/-- Every one-letter Pauli matrix is traceless, so the one-letter word span is
proper. This is the obstruction to `i = 1` in arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_wordSpan_one_ne_top : Kraus.wordSpan threePauliTensor 1 ≠ ⊤ := by
  have hle : Kraus.wordSpan threePauliTensor 1 ≤
      LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ) := by
    rw [Kraus.wordSpan_one]
    apply Submodule.span_le.mpr
    rintro M ⟨k, rfl⟩
    simp [threePauliTensor, LinearMap.mem_ker]
  intro htop
  have hzero := hle (show (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Kraus.wordSpan threePauliTensor 1 by rw [htop]; exact Submodule.mem_top)
  norm_num [LinearMap.mem_ker, Matrix.trace_fin_two] at hzero

private theorem pauli_cycle_mul (k : Fin 3) :
    SpinCover.pauli (k + 1) * SpinCover.pauli (k + 2) = Complex.I • SpinCover.pauli k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [SpinCover.pauli, smul_eq_mul]

/-- Two-letter products span the whole qubit matrix algebra. This is the upper
bound `i ≤ 2` in arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_wordSpan_two : Kraus.wordSpan threePauliTensor 2 = ⊤ := by
  let W := Kraus.wordSpan threePauliTensor 2
  have hproduct (a b : Fin 3) : SpinCover.pauli a * SpinCover.pauli b ∈ W := by
    apply (W.smul_mem_iff
      (mul_ne_zero pauliNormalization_ne_zero pauliNormalization_ne_zero)).mp
    simpa [threePauliTensor, Kraus.evalWord, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul] using Kraus.evalWord_mem_wordSpan threePauliTensor [a, b]
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ W := by
    simpa only [PauliDissipation.pauli_sq] using hproduct 0 0
  have hPauli (k : Fin 3) : SpinCover.pauli k ∈ W := by
    have h := hproduct (k + 1) (k + 2)
    rw [pauli_cycle_mul] at h
    exact (W.smul_mem_iff Complex.I_ne_zero).mp h
  apply top_unique
  intro M _
  rw [SpinCover.pauli_expansion M]
  exact W.add_mem (W.smul_mem _ hone) (W.sum_mem fun k _ ↦ W.smul_mem _ (hPauli k))

/-- The primitivity index of the three-Pauli channel is one.
Source: arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_qIndex : qIndex threePauliTensor = 1 := by
  let S : Set ℕ := {n | 0 < n ∧ ∀ φ : Fin 2 → ℂ, φ ≠ 0 →
    Kraus.vectorSpreadSpan threePauliTensor φ n = ⊤}
  have hone : 1 ∈ S := ⟨one_pos, threePauliTensor_vectorSpreadSpan_one⟩
  have hpos := (Nat.sInf_mem (show S.Nonempty from ⟨1, hone⟩)).1
  have hle := Nat.sInf_le hone
  change sInf S = 1
  omega

/-- The exact-length full-Kraus-rank index of the three-Pauli channel is two.
Source: arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_iIndex : iIndex threePauliTensor = 2 := by
  let S : Set ℕ := {n | 0 < n ∧ Kraus.wordSpan threePauliTensor n = ⊤}
  have htwo : 2 ∈ S := ⟨two_pos, threePauliTensor_wordSpan_two⟩
  have hmem := Nat.sInf_mem (show S.Nonempty from ⟨2, htwo⟩)
  have hle := Nat.sInf_le htwo
  have hne : sInf S ≠ 1 := by
    intro h
    exact threePauliTensor_wordSpan_one_ne_top (h ▸ hmem.2)
  change sInf S = 2
  have hpos : 0 < sInf S := hmem.1
  omega

/-- The two indices are strictly different for a trace-preserving qubit channel.
Source: the strict-index example in arXiv:0909.5347, lines 496–499. -/
theorem threePauliTensor_qIndex_lt_iIndex : qIndex threePauliTensor < iIndex threePauliTensor := by
  rw [threePauliTensor_qIndex, threePauliTensor_iIndex]
  omega

end MPSTensor
