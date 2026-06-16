/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.Core.Correlations

/-!
# AKLT correlation length

This module computes the spectrum of the AKLT transfer map and the resulting
finite correlation length.  The AKLT tensor (`MPSTensor.akltTensor`) has a
transfer map `E_A(X) = ∑ᵢ A^i X (A^i)ᴴ` with leading eigenvalue `1` and a single
subleading eigenvalue `-1/3` of algebraic multiplicity three.  The three Pauli
matrices `σx`, `σy`, `σz` are explicit eigenvectors for `-1/3`, while the
identity is the eigenvector for `1`; together they form a basis of `M₂(ℂ)`, so
the full spectrum is `{1, -1/3, -1/3, -1/3}`.

The subleading eigenvalue has modulus `1/3`, so the AKLT correlation length is
`ξ = -1/log|λ₂| = 1/log 3`, a finite value: the AKLT state has exponentially
decaying connected correlations with decay rate `(1/3)ⁿ`.

## Main results

* `aklt_transferMap_sigmaZ`, `aklt_transferMap_sigmaX`, `aklt_transferMap_sigmaY`
  — the three Pauli matrices are eigenvectors of the AKLT transfer map with
  eigenvalue `-1/3`
* `aklt_transferMap_hasEigenvalue_neg_third` — `-1/3` is an eigenvalue of the
  AKLT transfer map
* `aklt_transferMap_hasEigenvalue_one` — `1` is an eigenvalue of the AKLT
  transfer map (the identity is the corresponding eigenvector)
* `aklt_subleading_norm` — the subleading eigenvalue has modulus `1/3`
* `aklt_correlationLength_eq` — the AKLT correlation length is `1/log 3`
* `aklt_correlationLength_pos` — the AKLT correlation length is positive (finite)

## References

* RMP review (arXiv:2011.12127), Section 2.3 and Example III.1
  ("Correlations, Entanglement, and the Transfer Matrix").  The AKLT transfer
  matrix has spectrum `{1, -1/3, -1/3, -1/3}` and correlation length
  `ξ = 1/log 3`.
* Affleck, Kennedy, Lieb, Tasaki (1987) — original AKLT construction.
-/

open scoped Matrix BigOperators
open Matrix MPSTensor

noncomputable section

namespace MPSTensor

/-! ### Pauli eigenvectors of the AKLT transfer map

The AKLT transfer map fixes the identity (`aklt_transferMap_one`) and scales each
of the three Pauli matrices by `-1/3`.  These four matrices form a basis of
`M₂(ℂ)`, so the spectrum is `{1, -1/3, -1/3, -1/3}`. -/

/-- `(√3)² = 3` as a complex equation. -/
private lemma aklt_sqrt3_sq : (↑(Real.sqrt 3) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_ofNat]

/-- `(√2)² = 2` as a complex equation. -/
private lemma aklt_sqrt2_sq : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_ofNat]

/-- `σz = diag(1, -1)` is an eigenvector of the AKLT transfer map with eigenvalue
`-1/3`. -/
theorem aklt_transferMap_sigmaZ :
    transferMap akltTensor (!![(1 : ℂ), 0; 0, -1]) =
      (-1 / 3 : ℂ) • !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  simp only [transferMap_apply, Fin.sum_univ_three, Matrix.add_apply,
    akltTensor_conjTranspose, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [akltTensor, one_div, Complex.ofReal_inv, smul_of, smul_cons,
      smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, mul_neg,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two,
      zero_mul, add_zero, zero_add, Complex.ofReal_div, neg_smul, neg_of,
      neg_cons, neg_zero, Matrix.neg_empty, neg_mul, neg_neg] <;>
    field_simp <;>
    ring_nf <;>
    norm_num [aklt_sqrt3_sq, aklt_sqrt2_sq]

/-- `σx = !![0, 1; 1, 0]` is an eigenvector of the AKLT transfer map with
eigenvalue `-1/3`. -/
theorem aklt_transferMap_sigmaX :
    transferMap akltTensor (!![(0 : ℂ), 1; 1, 0]) =
      (-1 / 3 : ℂ) • !![(0 : ℂ), 1; 1, 0] := by
  ext i j
  simp only [transferMap_apply, Fin.sum_univ_three, Matrix.add_apply,
    akltTensor_conjTranspose, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [akltTensor, one_div, Complex.ofReal_inv, smul_of, smul_cons,
      smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, mul_neg,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two,
      zero_mul, add_zero, zero_add, Complex.ofReal_div, neg_smul, neg_of,
      neg_cons, neg_zero, Matrix.neg_empty, neg_mul] <;>
    field_simp <;>
    ring_nf <;>
    norm_num [aklt_sqrt3_sq, aklt_sqrt2_sq]

/-- `σy = !![0, -i; i, 0]` is an eigenvector of the AKLT transfer map with
eigenvalue `-1/3`.  The off-diagonal entries come only from `A⁰ = (1/√3) σz`,
giving the prefactor `(1/√3)·(1/√3) = 1/3`; the diagonal entries vanish. -/
theorem aklt_transferMap_sigmaY :
    transferMap akltTensor (!![(0 : ℂ), -Complex.I; Complex.I, 0]) =
      (-1 / 3 : ℂ) • !![(0 : ℂ), -Complex.I; Complex.I, 0] := by
  ext i j
  simp only [transferMap_apply, Fin.sum_univ_three, Matrix.add_apply,
    akltTensor_conjTranspose, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [akltTensor, one_div, Complex.ofReal_inv, smul_of, smul_cons,
      smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, mul_neg,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two,
      zero_mul, add_zero, zero_add, Complex.ofReal_div, neg_smul, neg_of,
      neg_cons, neg_zero, Matrix.neg_empty, neg_mul, neg_neg] <;>
    field_simp <;>
    ring_nf <;>
    norm_num [aklt_sqrt3_sq, aklt_sqrt2_sq]

/-! ### Spectrum and correlation length -/

/-- `σz` is a nonzero matrix, so it witnesses `-1/3` as a genuine eigenvalue. -/
private lemma sigmaZ_ne_zero : (!![(1 : ℂ), 0; 0, -1]) ≠ 0 := by
  intro h
  have : (!![(1 : ℂ), 0; 0, -1]) 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  simp at this

/-- The subleading eigenvalue `-1/3` is a genuine eigenvalue of the AKLT transfer
map, witnessed by the eigenvector `σz`. -/
theorem aklt_transferMap_hasEigenvalue_neg_third :
    Module.End.HasEigenvalue (transferMap akltTensor) (-1 / 3 : ℂ) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr aklt_transferMap_sigmaZ, sigmaZ_ne_zero⟩)

/-- The leading eigenvalue `1` is a genuine eigenvalue of the AKLT transfer map,
witnessed by the identity as eigenvector (`aklt_transferMap_one`). -/
theorem aklt_transferMap_hasEigenvalue_one :
    Module.End.HasEigenvalue (transferMap akltTensor) (1 : ℂ) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [one_smul]; exact aklt_transferMap_one),
        one_ne_zero⟩)

/-- The subleading eigenvalue of the AKLT transfer map has modulus `1/3`. -/
theorem aklt_subleading_norm : ‖(-1 / 3 : ℂ)‖ = 1 / 3 := by
  rw [neg_div, norm_neg, Complex.norm_div]
  norm_num

/-- The AKLT correlation length, computed from the subleading eigenvalue
`λ₂ = -1/3`, equals `1/log 3`.  Since `0 < 1/log 3 < ∞`, the AKLT state has a
finite, positive correlation length: its connected correlations decay
exponentially with rate `(1/3)ⁿ`. -/
theorem aklt_correlationLength_eq :
    correlationLength (-1 / 3 : ℂ) = 1 / Real.log 3 := by
  rw [correlationLength, aklt_subleading_norm,
    show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [div_neg, neg_div, neg_neg]

/-- The AKLT correlation length is positive: `0 < 1/log 3`. -/
theorem aklt_correlationLength_pos :
    0 < correlationLength (-1 / 3 : ℂ) := by
  apply correlationLength_pos
  · rw [aklt_subleading_norm]; norm_num
  · rw [aklt_subleading_norm]; norm_num

end MPSTensor

end
