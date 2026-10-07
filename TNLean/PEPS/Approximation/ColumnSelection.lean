/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNormFrobenius
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# A nonzero column close to a pure state

Let `Ω` be a unit vector in a finite-dimensional space with a distinguished
orthonormal basis `|z⟩`, and let `σ` be an arbitrary operator with
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`. Then some basis column `v = σ|z⟩` is nonzero and,
up to a unit phase, its normalization lies within `2η` of `Ω`. The operator
`σ` is neither assumed positive nor Hermitian, and no lower bound on the
overlap `⟨Ω|z⟩` of the selected column is assumed.

The argument has three steps.

* Parseval and the Hilbert--Schmidt bound: with `E = σ - |Ω⟩⟨Ω|`,
  `∑_z ‖E|z⟩‖² = ‖E‖₂² ≤ ‖E‖₁² ≤ η²`, while `∑_z |⟨Ω|z⟩|² = 1`.
* Selection: some `z` has `⟨Ω|z⟩ ≠ 0` and `‖E|z⟩‖ ≤ η |⟨Ω|z⟩|`, since
  otherwise the weighted sum of the two families gives a strict contradiction.
* Normalization: `w = v / ⟨Ω|z⟩` obeys `‖w - Ω‖ ≤ η`, hence `w ≠ 0`,
  `|‖w‖ - 1| ≤ η` and `‖w / ‖w‖ - Ω‖ ≤ 2η`; the phase of `⟨Ω|z⟩` transfers
  this to `v / ‖v‖`.

The proofs here were written independently from the manuscript.

The trace norm of QICLean is defined on matrices indexed by `Fin n`. An
operator on a space with an arbitrary finite basis is measured after
reindexing along an arbitrary enumeration `e` of that basis. All statements
hold for every enumeration, so no particular enumeration is singled out.

The generic statements of this file are candidates for QICLean.

## Main results

* `TNLean.PEPS.Approximation.sum_norm_sq_le_traceNorm_reindex_sq` — the sum of
  the squared moduli of all entries is at most the squared trace norm.
* `TNLean.PEPS.Approximation.exists_ne_zero_norm_sq_le_of_sum` — selection of
  one index from the two square-summed families.
* `TNLean.PEPS.Approximation.exists_phase_normalize_sub_le` — the
  normalization step in an arbitrary complex normed space.
* `TNLean.PEPS.Approximation.exists_column_ne_zero_of_traceNorm_sub_pure_le` —
  the vector part of Lemma 8.1.

## References

Polynomial-PEPS approximation manuscript (September 24, 2026), Lemma 8.1
`lem:columns`, `07-assembly.tex`, lines 67–99 (statement lines 67–78, proof
lines 79–94); openai/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder

namespace TNLean.PEPS.Approximation

section Frobenius

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The squared Hilbert--Schmidt norm, written as the sum of the squared
moduli of all entries, is at most the squared trace norm. The basis
enumeration `e` used to evaluate the trace norm is arbitrary.

This is the bound `∑_z ‖E|z⟩‖² = ‖E‖₂² ≤ ‖E‖₁²` in the proof of
Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 79–84. -/
theorem sum_norm_sq_le_traceNorm_reindex_sq (E : Matrix ι ι ℂ) (e : ι ≃ Fin n) :
    ∑ z, ∑ x, ‖E x z‖ ^ 2 ≤ Matrix.traceNorm (Matrix.reindex e e E) ^ 2 := by
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e E
  have hB : ‖B‖ ^ 2 = ∑ z, ∑ x, ‖E x z‖ ^ 2 := by
    change ‖WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ B i j‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.norm_sq_eq_of_L2, B, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Finset.sum_comm]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [← e.sum_comp]
    simp
  rw [← hB]
  exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.frobenius_norm_le_traceNorm B) 2

end Frobenius

section Selection

variable {ι : Type*} [Fintype ι]

/-- Selection of one index from two square-summed families.

If `∑_z ‖f z‖² ≤ η²` and `∑_z ‖a z‖² = 1`, then some `z` has `a z ≠ 0` and
`‖f z‖² ≤ η² ‖a z‖²`. No positive lower bound on `‖a z‖` is assumed, and
`η = 0` is allowed.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 84–86. -/
theorem exists_ne_zero_norm_sq_le_of_sum {E : Type*} [SeminormedAddCommGroup E]
    (f : ι → E) (a : ι → ℂ) {η : ℝ} (hf : ∑ z, ‖f z‖ ^ 2 ≤ η ^ 2)
    (ha : ∑ z, ‖a z‖ ^ 2 = 1) :
    ∃ z, a z ≠ 0 ∧ ‖f z‖ ^ 2 ≤ η ^ 2 * ‖a z‖ ^ 2 := by
  classical
  -- Restrict both sums to the indices with nonzero overlap.
  set s : Finset ι := {z | a z ≠ 0}
  have hsa : ∑ z ∈ s, ‖a z‖ ^ 2 = 1 := by
    rw [← ha]
    exact Finset.sum_filter_of_ne fun z _ hz ↦ by simpa using hz
  obtain ⟨z, hz, hle⟩ := Finset.exists_le_of_sum_le
    (f := fun z ↦ ‖f z‖ ^ 2) (g := fun z ↦ η ^ 2 * ‖a z‖ ^ 2)
    (Finset.nonempty_of_sum_ne_zero (hsa ▸ one_ne_zero)) <|
    calc ∑ z ∈ s, ‖f z‖ ^ 2
        ≤ ∑ z, ‖f z‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ ↦ sq_nonneg _
      _ ≤ η ^ 2 := hf
      _ = ∑ z ∈ s, η ^ 2 * ‖a z‖ ^ 2 := by rw [← Finset.mul_sum, hsa, mul_one]
  exact ⟨z, (Finset.mem_filter.mp hz).2, hle⟩

end Selection

section Normalization

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Normalization within twice the error.

If `‖w - Ω‖ ≤ η < 1` and `‖Ω‖ = 1`, then `w ≠ 0` and
`‖w / ‖w‖ - Ω‖ ≤ 2η`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 86–89. -/
theorem normalize_sub_le_two_mul {w Ω : H} {η : ℝ} (hΩ : ‖Ω‖ = 1)
    (hw : ‖w - Ω‖ ≤ η) (hη : η < 1) :
    w ≠ 0 ∧ ‖((‖w‖ : ℂ)⁻¹) • w - Ω‖ ≤ 2 * η := by
  have hnorm : |‖w‖ - 1| ≤ η := by
    rw [← hΩ]
    exact (abs_norm_sub_norm_le w Ω).trans hw
  have hpos : 0 < ‖w‖ := by
    have := (abs_le.mp hnorm).1
    linarith
  have hw0 : w ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨hw0, ?_⟩
  have hscale : ‖((‖w‖ : ℂ)⁻¹) • w - w‖ = |‖w‖ - 1| := by
    have : ((‖w‖ : ℂ)⁻¹) • w - w = ((‖w‖ : ℂ)⁻¹ * (1 - ‖w‖)) • w := by
      rw [mul_sub, mul_one, inv_mul_cancel₀ (by exact_mod_cast hpos.ne'), sub_smul,
        one_smul]
    rw [this, norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
    field_simp
  calc ‖((‖w‖ : ℂ)⁻¹) • w - Ω‖
      ≤ ‖((‖w‖ : ℂ)⁻¹) • w - w‖ + ‖w - Ω‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η + η := add_le_add (hscale ▸ hnorm) hw
    _ = 2 * η := by ring

/-- The normalization step of Polynomial-PEPS Lemma 8.1.

Let `‖Ω‖ = 1`, `0 ≤ η < 1`, and `v = f + a Ω` with `a ≠ 0` and
`‖f‖ ≤ η ‖a‖`. Then `v ≠ 0` and some unit phase `e^{iθ}` satisfies
`‖v / ‖v‖ - e^{iθ} Ω‖ ≤ 2η`. The phase is the phase of `a`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 84–89. -/
theorem exists_phase_normalize_sub_le {v f Ω : H} {a : ℂ} {η : ℝ}
    (hΩ : ‖Ω‖ = 1) (ha : a ≠ 0) (hv : v = f + a • Ω) (hf : ‖f‖ ≤ η * ‖a‖)
    (hη : η < 1) :
    v ≠ 0 ∧ ∃ θ : ℝ,
      ‖((‖v‖ : ℂ)⁻¹) • v - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨w, hw_def⟩ : ∃ w : H, w = a⁻¹ • v := ⟨_, rfl⟩
  have hvw : v = a • w := by rw [hw_def, smul_inv_smul₀ ha]
  have hwΩ : ‖w - Ω‖ ≤ η := by
    have : w - Ω = a⁻¹ • f := by
      rw [hw_def, hv, smul_add, inv_smul_smul₀ ha, add_sub_cancel_right]
    rw [this, norm_smul, norm_inv, inv_mul_le_iff₀ hapos, mul_comm]
    exact hf
  obtain ⟨hw0, hwn⟩ := normalize_sub_le_two_mul hΩ hwΩ hη
  subst hvw
  refine ⟨smul_ne_zero ha hw0, Complex.arg a, ?_⟩
  set c : ℂ := Complex.exp (Complex.arg a * Complex.I)
  have hc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hac : a = (‖a‖ : ℂ) * c := (Complex.norm_mul_exp_arg_mul_I a).symm
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hscalar : ((‖a‖ * ‖w‖ : ℝ) : ℂ)⁻¹ * ((‖a‖ : ℂ) * c) = c * (‖w‖ : ℂ)⁻¹ := by
    have ha' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hapos.ne'
    have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
    push_cast
    field_simp
  rw [← hac] at hscalar
  have hnormalize : ((‖a • w‖ : ℂ)⁻¹) • (a • w) = c • (((‖w‖ : ℂ)⁻¹) • w) := by
    rw [smul_smul, smul_smul, norm_smul, hscalar]
  rw [hnormalize, ← smul_sub, norm_smul, hc, one_mul]
  exact hwn

end Normalization

section Column

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The column of a matrix at a basis vector has the expected coordinates. -/
theorem toEuclideanLin_single_one_apply (σ : Matrix ι ι ℂ) (z x : ι) :
    Matrix.toEuclideanLin σ (EuclideanSpace.single z 1) x = σ x z := by
  simp [Matrix.toLpLin_apply]

/-- **Polynomial-PEPS Lemma 8.1, vector part.**

Let `Ω` be a unit vector in a finite-dimensional space with orthonormal basis
indexed by `ι`, and let `σ` be an arbitrary operator with
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, the trace norm being evaluated along an arbitrary
enumeration `e` of the basis. Then some basis column `v = σ|z⟩` is nonzero
and some unit phase `e^{iθ}` satisfies `‖v / ‖v‖ - e^{iθ} Ω‖ ≤ 2η`.

The existence of such a phase is equivalent to the source bound on the
minimum over `θ`, which is attained by continuity on the circle. The operator
`σ` is not assumed positive or Hermitian. When `ι` is the set of
configurations of a tensor product, `|z⟩` is a product-basis vector.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94. -/
theorem exists_column_ne_zero_of_traceNorm_sub_pure_le (e : ι ≃ Fin n)
    (σ : Matrix ι ι ℂ) (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.traceNorm
      (Matrix.reindex e e (σ - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) :
    ∃ z : ι, Matrix.toEuclideanLin σ (EuclideanSpace.single z 1) ≠ 0 ∧ ∃ θ : ℝ,
      ‖((‖Matrix.toEuclideanLin σ (EuclideanSpace.single z 1)‖ : ℂ)⁻¹) •
          Matrix.toEuclideanLin σ (EuclideanSpace.single z 1) -
        Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  set E : Matrix ι ι ℂ := σ - Matrix.vecMulVec (⇑Ω) (star ⇑Ω)
  have hη0 : 0 ≤ η := (Matrix.traceNorm_nonneg _).trans hσ
  -- The columns of the error operator, as vectors.
  set f : ι → EuclideanSpace ℂ ι := fun z ↦ WithLp.toLp 2 fun x ↦ E x z
  -- The overlaps `⟨Ω|z⟩`.
  set a : ι → ℂ := fun z ↦ star (Ω z)
  have hf : ∑ z, ‖f z‖ ^ 2 ≤ η ^ 2 := by
    have h1 := sum_norm_sq_le_traceNorm_reindex_sq E e
    have h2 : Matrix.traceNorm (Matrix.reindex e e E) ^ 2 ≤ η ^ 2 :=
      pow_le_pow_left₀ (Matrix.traceNorm_nonneg _) hσ 2
    simpa only [f, EuclideanSpace.norm_sq_eq] using h1.trans h2
  have ha : ∑ z, ‖a z‖ ^ 2 = 1 := by
    simp only [a, norm_star, ← EuclideanSpace.norm_sq_eq, hΩ, one_pow]
  obtain ⟨z, haz, hfz⟩ := exists_ne_zero_norm_sq_le_of_sum f a hf ha
  refine ⟨z, exists_phase_normalize_sub_le (f := f z) hΩ haz ?_ ?_ hη⟩
  · ext x
    simp [toEuclideanLin_single_one_apply, f, a, E, Matrix.vecMulVec_apply, mul_comm]
  · rw [← mul_pow] at hfz
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg hη0 (norm_nonneg _)) two_ne_zero).mp hfz

end Column

end TNLean.PEPS.Approximation
