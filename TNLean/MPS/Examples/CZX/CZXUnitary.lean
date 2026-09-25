/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.Examples.CZX.CZXAnomaly
import TNLean.MPS.MPU.GroupRepresentation

/-!
# Unitarity of the undecorated CZX matrix product operator

For every periodic chain of `L > 0` qubits, the tensor
`M^{ij} = δ_{i,1 ⊕ j} T_j` generates the computational-basis action
`U_L |t⟩ = (-1)^{∑_j t_j t_{j+1}} |1-t⟩`.
Thus `U_L = X^{⊗ L} D_L`, where `D_L` is the diagonal cyclic controlled-`Z` phase.
The first physical index is the output row and the second is the input column.
The cyclic sum gives `D_1 = Z` and `D_2 = I` (the two-site edge is counted twice).
The monomial-matrix formula proves unitarity and `U_L² = (-1)^L I` for all positive
lengths, without an even-length restriction.

The review arXiv:2011.12127 displays `D_L X^{⊗ L}`, differing by `(-1)^L`.
The CZX operator of arXiv:2405.00439, Section III.D, also carries Pauli `Z` factors;
it is not the undecorated operator used here. The explicit tensor and compression data
are recorded in `Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`,
`ex:p5ft-czx`.

The stacked square has a word-level compression onto `-δ`, but its sitewise intertwiner
spaces vanish. `CZXAnomaly` uses this nonsplitting obstruction to prove failure of star
closure for the virtual algebra in these coordinates. The conjunction with physical
unitarity below does not identify star-closure failure with an anomaly invariant.
An anomaly class requires a separate fusion-associator three-cocycle calculation,
such as that discussed in arXiv:2405.00439, Section III.D; none is computed here.

## Main definitions

* `CZXCompression.spinFlip`: the global spin flip of a periodic configuration.
* `CZXCompression.czExponent`: the number of neighboring pairs of ones around the periodic
  chain, the exponent of the controlled-`Z` sign.

## Main results

* `CZXCompression.mpo_czxTensor_apply`, `CZXCompression.mpo_czxTensor`: the periodic operator
  is the monomial matrix of the global spin flip with the controlled-`Z` sign.
* `CZXCompression.mpo_czxTensor_mul_self`, `CZXCompression.mpo_mulTensor_czxTensor`: the
  operator squares to `(-1)^N` times the identity, the operator form of the word-trace
  identity of Example D.
* `CZXCompression.czxTensor_isMPUPos`: the undecorated CZX tensor is a matrix product unitary
  on every periodic chain of positive length.
* `CZXCompression.czxTensor_isMPUPos_and_czxSquare_not_starClosed`: the operator is unitary
  although the virtual algebra of the stacked square is not closed under conjugate
  transposition.
-/

noncomputable section

open scoped BigOperators Matrix

namespace CZXCompression

open MPSTensor

/-! ### The entrywise form of the tensor -/

/-- The bond-two coordinates: output `i` is the flip of input `j`, the outgoing bond
carries `j`, and the incoming bond `l` contributes `(-1)^{l j}`. -/
theorem czxTensor_apply (i j l r : Fin 2) :
    czxTensor i j l r = if i = j.rev ∧ r = j then (-1 : ℂ) ^ (l.val * j.val) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [czxTensor, czxIntTensor, complexOfInt, Fin.rev]

/-! ### The periodic operator -/

/-- The global spin flip `X^{⊗ N}` on periodic configurations of `N` qubits. -/
def spinFlip (N : ℕ) : Equiv.Perm (Fin N → Fin 2) :=
  Equiv.piCongrRight fun _ ↦ Fin.revPerm

theorem spinFlip_apply {N : ℕ} (t : Fin N → Fin 2) (n : Fin N) :
    spinFlip N t n = (t n).rev := rfl

/-- The global spin flip is an involution. -/
theorem spinFlip_mul_self {N : ℕ} : spinFlip N * spinFlip N = 1 := by
  ext t n
  simp [Equiv.Perm.mul_apply, spinFlip_apply]

variable {N : ℕ} [NeZero N]

/-- The controlled-`Z` exponent of a periodic configuration: the number of neighboring pairs
of ones, the site after the last being the first. -/
def czExponent (t : Fin N → Fin 2) : ℕ :=
  ∑ n, (t n).val * (t (n + 1)).val

/-- **The periodic CZX operator entrywise**: the entry at `(s, t)` vanishes unless `s` is the
spin flip of `t`, and then equals the controlled-`Z` sign of `t`. This is the closed-chain
contraction of the tensor along the unique bond configuration `g_n = t_{n-1}` that survives
(construction note, `ex:p5ft-czx`). -/
theorem mpo_czxTensor_apply (s t : Fin N → Fin 2) :
    MPOTensor.mpo czxTensor N s t =
      if s = spinFlip N t then (-1 : ℂ) ^ czExponent t else 0 := by
  let g0 : Fin N → Fin 2 := fun n ↦ t (n - 1)
  rw [MPOTensor.mpo_apply_eq_prod_of_forced_bond czxTensor s t g0 fun g hg ↦ by
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    refine ⟨n - 1, ?_⟩
    rw [czxTensor_apply, ite_eq_right]
    intro h
    apply hn
    simpa [g0] using h.2]
  by_cases hst : s = spinFlip N t
  · have hp : ∀ n, s n = (t n).rev := fun n ↦ congrFun hst n
    rw [ite_eq_left hst]
    calc
      _ = ∏ n, (-1 : ℂ) ^ ((t (n - 1)).val * (t n).val) := by
        refine Finset.prod_congr rfl fun n _ ↦ ?_
        rw [czxTensor_apply, ite_eq_left ⟨hp n, by simp [g0]⟩]
      _ = (-1 : ℂ) ^ ∑ n, (t (n - 1)).val * (t n).val := Finset.prod_pow_eq_pow_sum _ _ _
      _ = _ := by
        congr 1
        exact Fintype.sum_equiv (Equiv.subRight 1) _ _ fun n ↦ by simp
  · rw [ite_eq_right hst]
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hst
    refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
    rw [czxTensor_apply, ite_eq_right]
    exact fun h ↦ hn h.1

/-- **The periodic CZX operator is a monomial matrix**: the global spin flip with the
controlled-`Z` sign attached to the input configuration (construction note, `ex:p5ft-czx`). -/
theorem mpo_czxTensor :
    MPOTensor.mpo czxTensor N =
      Matrix.monomial (spinFlip N) fun t ↦ (-1 : ℂ) ^ czExponent t := by
  ext s t
  rw [mpo_czxTensor_apply, Matrix.monomial_apply]

/-- The periodic CZX operator is unitary at every positive length. -/
theorem mpo_czxTensor_mem_unitaryGroup :
    MPOTensor.mpo czxTensor N ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  rw [mpo_czxTensor]
  refine Matrix.monomial_mem_unitaryGroup _ _ fun t ↦ ?_
  rw [star_pow, star_neg, star_one, ← mul_pow]
  simp

/-! ### The square of the operator -/

private theorem site_sign (a b : Fin 2) :
    (-1 : ℂ) ^ (a.rev.val * b.rev.val) * (-1 : ℂ) ^ (a.val * b.val) =
      -((-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val) := by
  fin_cases a <;> fin_cases b <;> simp [Fin.rev]

/-- The controlled-`Z` signs of a configuration and of its spin flip multiply to `(-1)^N`:
sitewise, `(1 - a)(1 - b) + ab` has the parity of `1 + a + b`, and the single-site signs
cancel in pairs around the periodic chain. -/
theorem neg_one_pow_czExponent_spinFlip_mul (t : Fin N → Fin 2) :
    (-1 : ℂ) ^ czExponent (spinFlip N t) * (-1 : ℂ) ^ czExponent t = (-1 : ℂ) ^ N := by
  simp only [czExponent, spinFlip_apply]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  simp only [site_sign]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
    Fintype.prod_equiv (Equiv.subRight (1 : Fin N)) (fun n ↦ (-1 : ℂ) ^ (t n).val)
      (fun n ↦ (-1 : ℂ) ^ (t (n + 1)).val) (fun n ↦ by simp),
    ← Finset.prod_mul_distrib]
  refine (mul_right_eq_self₀.mpr (Or.inl (Finset.prod_eq_one fun n _ ↦ ?_)))
  rw [← mul_pow]
  simp

/-- **The periodic CZX operator squares to `(-1)^N`** at every positive length; this is the
operator form of the word-trace identity of Example D (construction note, `ex:p5ft-czx`). -/
theorem mpo_czxTensor_mul_self :
    MPOTensor.mpo czxTensor N * MPOTensor.mpo czxTensor N = ((-1 : ℂ) ^ N) • 1 := by
  rw [mpo_czxTensor, Matrix.monomial_mul_monomial, spinFlip_mul_self, ← Matrix.monomial_one,
    Matrix.smul_monomial]
  congr 1
  funext t
  rw [Pi.smul_apply, smul_eq_mul, mul_one]
  exact neg_one_pow_czExponent_spinFlip_mul t

/-- **The stacked square of the undecorated CZX tensor is `(-1)^N` times the identity** as an
operator at every positive length (construction note, `ex:p5ft-czx`). -/
theorem mpo_mulTensor_czxTensor :
    MPOTensor.mpo (MPOTensor.mulTensor czxTensor czxTensor) N = ((-1 : ℂ) ^ N) • 1 := by
  rw [MPOTensor.mpo_mulTensor, mpo_czxTensor_mul_self]

/-! ### The matrix product unitary -/

/-- **The undecorated CZX tensor is a matrix product unitary on every periodic chain of
positive length** (construction note, `ex:p5ft-czx`; the symmetry of CZX type is that of
arXiv:2405.00439, Section III.D, without its additional product of Pauli `Z` factors). -/
theorem czxTensor_isMPUPos : MPOTensor.IsMPUPos czxTensor := by
  intro N hN
  let : NeZero N := ⟨by omega⟩
  exact mpo_czxTensor_mem_unitaryGroup

/-- The undecorated CZX tensor satisfies the established all-`N > 1` unitarity predicate. -/
theorem czxTensor_isMPU : MPOTensor.IsMPU czxTensor :=
  czxTensor_isMPUPos.isMPU

/-- Physical unitarity at every positive length together with failure of star closure of
the stacked-square virtual algebra in these coordinates. The second property follows from
the absence of sitewise intertwiners with the target `-δ`, not from a three-cocycle
calculation, and is not asserted to be an anomaly invariant. -/
theorem czxTensor_isMPUPos_and_czxSquare_not_starClosed :
    MPOTensor.IsMPUPos czxTensor ∧
      ¬ ∀ i, (czxSquare i)ᴴ ∈ Algebra.adjoin ℂ (Set.range czxSquare) :=
  ⟨czxTensor_isMPUPos, czxSquare_not_starClosed⟩

end CZXCompression
