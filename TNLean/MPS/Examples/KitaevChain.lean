/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.InvariantProjection
import TNLean.MPS.Examples.EvenParity

/-!
# Kitaev chain: the fixed-point matrices and their bosonic contraction

**Source.** Bultinck, Williamson, Haegeman, Verstraete 2017 (arXiv:1610.07849),
Section II, `References/1610.07849/source/FermionicMPS.tex` lines 264–286: the
ground state of the Kitaev chain `H = -i ∑ⱼ γ₂ⱼ γ₂ⱼ₊₁` with periodic boundary
conditions is the fermionic MPS with matrices `A⁰ = 1`, `A¹ = Y = y = !![0, 1; -1, 0]`,
the periodic coefficients carry an extra `y` in the trace (line 372), and `Y` commutes
with every `Aⁱ`, so read as a bosonic MPS the matrices are reducible (line 289).
Kitaev 2001 (arXiv:cond-mat/0010440) introduced the chain.
Review: arXiv:2011.12127, Appendix A, "The Kitaev chain",
`Papers/2011.12127/TN-Review-main.tex` lines 2526–2532; Section II.B.4, equation
`Majchain`, lines 474–478: the state `∑ Tr[Y A^{i₁} ⋯ A^{i_N}] |i₁⟩ ⊗_g ⋯` has odd parity,
and the graded description is injective; Section III.A.4, lines 1261–1264: read as a
bosonic MPS the matrices commute with `Y`, so the MPS is non-injective and is a sum of two
injective MPS.

**Formalized here.** The matrices exactly as printed, `(A¹)² = -1`, `A¹ = Y`, the closed
forms of the untwisted periodic amplitudes `tr(A^{i₁} ⋯ A^{i_N})` and of the twisted
amplitudes `tr(Y A^{i₁} ⋯ A^{i_N})` (the coefficients of `Majchain`), their complementary
parity supports (the twisted family lives on an odd number of `1`s, the untwisted one on
an even number), the open-boundary relations between the four boundary closures, the
commutation of `Y` with both matrices, and the bosonic status of the tensor: a common
eigenvector and a nontrivial invariant orthogonal projection exist, the tensor is neither
injective nor normal, and the twisted amplitudes are the sum of two injective
bond-dimension-one MPS (Section III.A.4).

**Scope restriction (bosonic contraction only):** the graded tensor product `⊗_g`, the
fermionic sign rules of the virtual contraction, and the fermionic notion of
injectivity are not formalized; every statement concerns the ordinary (bosonic)
contraction of the printed matrices, which gives the coefficients of `Majchain` in the
ordered graded product basis. Documented in
`docs/paper-gaps/rmp_kitaev_chain_bosonic_scope.tex`.

## Main definitions
* `MPSTensor.kitaevTwist` : the twist `Y = !![0, 1; -1, 0]`
* `MPSTensor.kitaevTensor` : the tensor `A⁰ = 1`, `A¹ = !![0, 1; -1, 0]`
* `MPSTensor.kitaevTwistedCoeff` : the twisted periodic amplitude `tr(Y A^{i₁} ⋯ A^{i_N})`
* `MPSTensor.kitaevSectorTensor` : the bond-dimension-one tensor `(1, c)`

## Main results
* `MPSTensor.kitaevTensor_one_mul_self` : `(A¹)² = -1`
* `MPSTensor.kitaevTensor_evalWord` : a word evaluates to `Y ^ (number of 1s)`
* `MPSTensor.kitaevTensor_coeff`, `MPSTensor.kitaevTwistedCoeff_eq` : closed forms
* `MPSTensor.kitaevTensor_coeff_ne_zero_iff`, `MPSTensor.kitaevTwistedCoeff_ne_zero_iff` :
  complementary parity supports
* `MPSTensor.kitaevTensor_not_isIrreducibleFamily`, `MPSTensor.kitaevTensor_not_isInjective`,
  `MPSTensor.kitaevTensor_not_isNormal`
* `MPSTensor.kitaevTwistedCoeff_eq_add`, `MPSTensor.kitaevSectorTensor_isInjective` :
  the sum of two injective MPS
* `MPSTensor.kitaevTensor_mul_kitaevGauge` : bridge to `evenParityTensor`

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*
- [arXiv:1610.07849](https://arxiv.org/abs/1610.07849) -- Bultinck, Williamson, Haegeman,
  Verstraete, *Fermionic matrix product states and one-dimensional topological phases*
- [arXiv:cond-mat/0010440](https://arxiv.org/abs/cond-mat/0010440) -- Kitaev,
  *Unpaired Majorana fermions in quantum wires*
-/

open scoped Matrix
open Matrix

namespace MPSTensor

/-! ### Definitions -/

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2531–2532 and
line 477; arXiv:1610.07849, `FermionicMPS.tex` line 280. The boundary twist
`Y = !![0, 1; -1, 0]`. -/
def kitaevTwist : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2531–2532;
arXiv:1610.07849, `FermionicMPS.tex` lines 278–281. The Kitaev-chain tensor with
`A⁰ = !![1, 0; 0, 1]` and `A¹ = !![0, 1; -1, 0]`, as printed. -/
def kitaevTensor : MPSTensor 2 2 := ![!![1, 0; 0, 1], !![0, 1; -1, 0]]

/-- Source: arXiv:2011.12127, equation `Majchain`, `Papers/2011.12127/TN-Review-main.tex`
line 476. The twisted periodic amplitude `tr(Y A^{i₁} ⋯ A^{i_N})` of a word, the
coefficient of `|i₁⟩ ⊗_g ⋯ ⊗_g |i_N⟩` in the Kitaev-chain state. -/
def kitaevTwistedCoeff (w : List (Fin 2)) : ℂ :=
  Matrix.trace (kitaevTwist * Kraus.evalWord kitaevTensor w)

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2531. `A⁰` is the
identity. -/
@[simp] lemma kitaevTensor_zero : kitaevTensor 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2532 ("with a
twist `Y = A¹`"). -/
@[simp] lemma kitaevTensor_one : kitaevTensor 1 = kitaevTwist := rfl

/-- Source: arXiv:1610.07849, `FermionicMPS.tex` line 591 (`y² = -1`). -/
theorem kitaevTwist_mul_self : kitaevTwist * kitaevTwist = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [kitaevTwist, Matrix.mul_apply]

/-- Source: arXiv:1610.07849, `FermionicMPS.tex` line 591. `(A¹)² = -1`. -/
theorem kitaevTensor_one_mul_self : kitaevTensor 1 * kitaevTensor 1 = -1 :=
  kitaevTwist_mul_self

/-- Source: arXiv:1610.07849, `FermionicMPS.tex` line 289. The twist commutes with
both matrices of the tensor. -/
theorem kitaevTwist_mul_kitaevTensor (i : Fin 2) :
    kitaevTwist * kitaevTensor i = kitaevTensor i * kitaevTwist := by
  fin_cases i <;> simp

/-! ### Word evaluation -/

/-- Project result: a word evaluates to the power of `Y` counting its letters `1`. -/
theorem kitaevTensor_evalWord (w : List (Fin 2)) :
    Kraus.evalWord kitaevTensor w = kitaevTwist ^ w.count 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ih, List.count_cons]
    fin_cases i
    · simp
    · simp [pow_succ']

private lemma kitaevTwist_pow_two_mul (m : ℕ) :
    kitaevTwist ^ (2 * m) = ((-1 : ℂ) ^ m) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pow_mul, sq, kitaevTwist_mul_self]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, pow_succ]; simp

private lemma kitaevTwist_pow_two_mul_add_one (m : ℕ) :
    kitaevTwist ^ (2 * m + 1) = ((-1 : ℂ) ^ m) • kitaevTwist := by
  rw [pow_succ, kitaevTwist_pow_two_mul, smul_mul_assoc, one_mul]

private lemma trace_kitaevTwist : Matrix.trace kitaevTwist = 0 := by
  simp [kitaevTwist, Matrix.trace_fin_two]

/-! ### Periodic amplitudes -/

/-- Project result: the periodic contraction of the matrices of arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex` lines 2531–2532, without the twist. With `k`
the number of letters `1`, the untwisted periodic amplitude is `2 (-1)^{k/2}` for
even `k` and `0` for odd `k`, independently of the length. -/
theorem kitaevTensor_coeff (w : List (Fin 2)) :
    coeff kitaevTensor w =
      if Even (w.count 1) then 2 * (-1) ^ (w.count 1 / 2) else 0 := by
  rw [coeff_eq, kitaevTensor_evalWord]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (w.count 1) <;> rw [hm]
  · rw [kitaevTwist_pow_two_mul, Nat.mul_div_cancel_left m two_pos]
    simp [Matrix.trace_smul, mul_comm]
  · rw [kitaevTwist_pow_two_mul_add_one]
    simp [Matrix.trace_smul, trace_kitaevTwist]

/-- Source: arXiv:2011.12127, equation `Majchain`, `Papers/2011.12127/TN-Review-main.tex`
line 476, and lines 2531–2532. With `k` the number of letters `1`, the twisted amplitude
`tr(Y A^{i₁} ⋯ A^{i_N})` is `0` for even `k` and `2 (-1)^{(k+1)/2}` for odd `k`,
independently of the length. -/
theorem kitaevTwistedCoeff_eq (w : List (Fin 2)) :
    kitaevTwistedCoeff w =
      if Even (w.count 1) then 0 else 2 * (-1) ^ ((w.count 1 + 1) / 2) := by
  rw [kitaevTwistedCoeff, kitaevTensor_evalWord, ← pow_succ']
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (w.count 1) <;> rw [hm]
  · rw [kitaevTwist_pow_two_mul_add_one]
    simp [Matrix.trace_smul, trace_kitaevTwist]
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, kitaevTwist_pow_two_mul,
      Nat.mul_div_cancel_left _ two_pos]
    simp [Matrix.trace_smul, mul_comm]

/-- Project result: the untwisted counterpart of arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex` lines 474–476. The untwisted amplitude is
supported exactly on words with an even number of letters `1`. -/
theorem kitaevTensor_coeff_ne_zero_iff (w : List (Fin 2)) :
    coeff kitaevTensor w ≠ 0 ↔ Even (w.count 1) := by
  rw [kitaevTensor_coeff]
  split_ifs with h <;> simp [h]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 474–476 ("one
gets a system with odd parity"); arXiv:1610.07849, `FermionicMPS.tex` line 277. The
twisted amplitude is supported exactly on words with an odd number of letters `1`. -/
theorem kitaevTwistedCoeff_ne_zero_iff (w : List (Fin 2)) :
    kitaevTwistedCoeff w ≠ 0 ↔ Odd (w.count 1) := by
  rw [kitaevTwistedCoeff_eq, ← Nat.not_even_iff_odd]
  split_ifs with h <;> simp [h]

/-- Project result: the twisted and untwisted amplitudes have disjoint supports. -/
theorem kitaevTensor_coeff_mul_kitaevTwistedCoeff (w : List (Fin 2)) :
    coeff kitaevTensor w * kitaevTwistedCoeff w = 0 := by
  rw [kitaevTensor_coeff, kitaevTwistedCoeff_eq]
  split_ifs <;> simp

/-! ### Open boundary closures -/

/-- Source: arXiv:1610.07849, `FermionicMPS.tex` line 286 (bosonic contraction).
For every word the two diagonal closures agree and the two off-diagonal closures differ
by a sign. -/
theorem kitaevTensor_evalWord_entries (w : List (Fin 2)) :
    Kraus.evalWord kitaevTensor w 0 0 = Kraus.evalWord kitaevTensor w 1 1 ∧
      Kraus.evalWord kitaevTensor w 0 1 = -Kraus.evalWord kitaevTensor w 1 0 := by
  rw [kitaevTensor_evalWord]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (w.count 1) <;> rw [hm]
  · rw [kitaevTwist_pow_two_mul]; simp
  · rw [kitaevTwist_pow_two_mul_add_one]; simp [kitaevTwist]

/-! ### Bosonic reducibility, non-injectivity and non-normality -/

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1261–1263; arXiv:1610.07849, `FermionicMPS.tex` line 289. The vector `(1, i)` is a
common eigenvector of both matrices, with eigenvalues `1` and `i`. -/
theorem kitaevTensor_mulVec_common_eigenvector (i : Fin 2) :
    kitaevTensor i *ᵥ ![1, Complex.I] = (![1, Complex.I] i) • ![1, Complex.I] := by
  ext a
  fin_cases i <;> fin_cases a <;> simp [kitaevTwist, Matrix.mulVec, dotProduct]

/-- The orthogonal projection onto the line spanned by `(1, i)`. -/
private noncomputable def kitaevEigenProj : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2]

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1261–1263 (the matrices commute with `Y`); arXiv:1610.07849, `FermionicMPS.tex`
line 289 ("reducible"). As a bosonic MPS the tensor is reducible: the projection onto
the line spanned by `(1, i)` is a nontrivial invariant orthogonal projection. -/
theorem kitaevTensor_not_isIrreducibleFamily : ¬ Kraus.IsIrreducibleFamily kitaevTensor := by
  refine not_not.2 ⟨kitaevEigenProj, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [kitaevEigenProj, Matrix.conjTranspose_apply]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [kitaevEigenProj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [kitaevEigenProj] at this
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [kitaevEigenProj] at this
  · intro i
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [kitaevEigenProj, kitaevTwist, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.sub_apply, Matrix.one_apply] <;> ring_nf <;> simp [Complex.I_sq]

/-- The functional `M ↦ M₀₀ - M₁₁` annihilates every word of the tensor. -/
private lemma kitaev_diag_sub_evalWord (w : List (Fin 2)) :
    (Matrix.entryLinearMap ℂ ℂ (0 : Fin 2) (0 : Fin 2) -
        Matrix.entryLinearMap ℂ ℂ (1 : Fin 2) (1 : Fin 2))
      (Kraus.evalWord kitaevTensor w) = 0 := by
  simp [(kitaevTensor_evalWord_entries w).1]

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1261–1263 ("hence the MPS is non-injective"). As a bosonic MPS the tensor is not
injective. -/
theorem kitaevTensor_not_isInjective : ¬ Kraus.IsInjective kitaevTensor :=
  Kraus.not_isInjective_of_linearMap
    (Matrix.entryLinearMap ℂ ℂ (0 : Fin 2) (0 : Fin 2) -
      Matrix.entryLinearMap ℂ ℂ (1 : Fin 2) (1 : Fin 2))
    (fun i => by simpa using kitaev_diag_sub_evalWord [i])
    (Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ))) (by simp)

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1261–1263 ("hence the MPS is non-injective"). As a bosonic MPS the tensor is not
normal: no blocking length makes it injective. -/
theorem kitaevTensor_not_isNormal : ¬ Kraus.IsNormal kitaevTensor := by
  rintro ⟨N, -, hN⟩
  exact Kraus.not_isNBlkInjective_of_linearMap _
    (fun σ => kitaev_diag_sub_evalWord (List.ofFn σ))
    (Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ))) (by simp) hN

/-! ### Decomposition into two injective MPS -/

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1263–1264. The bond-dimension-one tensor `(1, c)`; for `c = ±i` it is the
restriction of the Kitaev tensor to the eigenline of `Y` with eigenvalue `c`. -/
def kitaevSectorTensor (c : ℂ) : MPSTensor 2 1 := ![1, c • 1]

/-- Project result: a word of the sector tensor evaluates to `c ^ (number of 1s)`. -/
theorem kitaevSectorTensor_evalWord (c : ℂ) (w : List (Fin 2)) :
    Kraus.evalWord (kitaevSectorTensor c) w = c ^ w.count 1 • 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ih, List.count_cons]
    fin_cases i
    · simp [kitaevSectorTensor]
    · simp [kitaevSectorTensor, smul_smul, pow_succ, mul_comm]

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1263–1264 ("a sum of two injective MPS"). Each sector tensor is injective. -/
theorem kitaevSectorTensor_isInjective (c : ℂ) :
    Kraus.IsInjective (kitaevSectorTensor c) := by
  refine eq_top_iff.2 fun M _ => ?_
  have hM : M = M 0 0 • kitaevSectorTensor c 0 := by
    ext a b; fin_cases a; fin_cases b; simp [kitaevSectorTensor]
  rw [hM]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-- Source: arXiv:2011.12127, Section III.A.4, `Papers/2011.12127/TN-Review-main.tex`
lines 1261–1264 ("can be written as a sum of two injective MPS `|ψ₁⟩ + |ψ₂⟩`"). The
twisted amplitude splits as `i · tr(a₊^w) + (-i) · tr(a₋^w)` over the two injective
sector tensors `a± = (1, ±i)`, the boundary factors `±i` being the eigenvalues of `Y`. -/
theorem kitaevTwistedCoeff_eq_add (w : List (Fin 2)) :
    kitaevTwistedCoeff w =
      Complex.I * coeff (kitaevSectorTensor Complex.I) w +
        -Complex.I * coeff (kitaevSectorTensor (-Complex.I)) w := by
  rw [kitaevTwistedCoeff_eq, coeff_eq, coeff_eq, kitaevSectorTensor_evalWord,
    kitaevSectorTensor_evalWord]
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (w.count 1) <;> rw [hm]
  · simp [pow_mul]
  · rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega]
    simp [pow_succ, pow_mul]
    linear_combination (-2 * (-1 : ℂ) ^ m) * Complex.I_sq

/-! ### Bridge to the even-parity tensor -/

/-- Bridge: the diagonal gauge `diag(1, i)` relating the Kitaev tensor to the even-parity tensor. -/
def kitaevGauge : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, Complex.I]

/-- Bridge: the gauge `diag(1, i)` is invertible, with inverse `diag(1, -i)`. -/
theorem kitaevGauge_mul_inv :
    kitaevGauge * Matrix.diagonal ![1, -Complex.I] = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [kitaevGauge]

/-- Bridge: after the on-site phase `diag(1, i)` on the physical index and the rescaling
by `√2`, the Kitaev tensor is conjugate to `evenParityTensor` by the gauge `diag(1, i)`:
`Aⁱ X = (√2 · φᵢ) X Eⁱ` with `φ = (1, i)`, `X = diag(1, i)`, `E = evenParityTensor`. -/
theorem kitaevTensor_mul_kitaevGauge (i : Fin 2) :
    kitaevTensor i * kitaevGauge =
      ((Real.sqrt 2 : ℂ) * ![1, Complex.I] i) • (kitaevGauge * evenParityTensor i) := by
  have h2 : (Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2) = 1 := by
    have : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    field_simp
  rw [evenParityTensor, Matrix.mul_smul, smul_smul, mul_right_comm, h2, one_mul]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [kitaevTwist, kitaevGauge, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

end MPSTensor
