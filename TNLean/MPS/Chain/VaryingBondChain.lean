/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinOrderedProduct
import TNLean.MPS.Chain.BlockTensor
import TNLean.MPS.Chain.VaryingBondOBC
import TNLean.MPS.Overlap.Basic

/-!
# Periodic chains with bond dimensions at most `D`

A periodic chain on a ring of `N` sites whose bond dimensions `D_0, …, D_{N-1}` may vary along
the ring and are at most `D` (`VaryingBondChain`): site `k` carries rectangular matrices `A_k^i`
of size `D_k × D_{k+1}`, the bond `k` being the one to the left of site `k`, and the state has
coefficients `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})`. This is the periodic counterpart of the
open-boundary chains `OBCChainTensor` of `TNLean.MPS.Chain.VaryingBondOBC`.

Padding every matrix with zeros to a `D × D` matrix (`VaryingBondChain.zeroPad`, built from
`Matrix.zeroPad`) gives a chain with the common bond dimension `D` and, on a ring of `N ≥ 1`
sites, the same state (`VaryingBondChain.coeff_zeroPad`). A product of padded matrices along
consecutive sites vanishes outside the rectangle of the bonds at its two ends
(`MPSChainTensor.eval_eq_zero_of_support`, `MPSChainTensor.blockTensor_eq_zero_of_support`).

This is the setting of arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS",
for matrix product states "with bond dimension at most `D`".

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
-/

open scoped BigOperators Matrix

/-- A periodic chain of tensors on a ring of `N` sites with **bond dimensions at most `D`**: the
bond `k`, to the left of site `k`, has dimension `D_k ≤ D`, and site `k` carries the rectangular
matrices `A_k^i` of size `D_k × D_{k+1}`, indices taken cyclically.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": a sequence of matrix
product states "with bond dimension at most `D`", not translation invariant. -/
structure VaryingBondChain (d D N : ℕ) where
  /-- The dimension of the bond to the left of each site. -/
  bondDim : Fin N → ℕ
  /-- Every bond dimension is at most `D`: arXiv:2307.01696, paragraph "Inhomogeneous
  short-range correlated MPS", matrix product states "with bond dimension at most `D`". -/
  bondDim_le : ∀ k, bondDim k ≤ D
  /-- The rectangular matrix of a site and a physical index. -/
  tensor : ∀ k : Fin N, Fin d → Matrix (Fin (bondDim k)) (Fin (bondDim (finRotate N k))) ℂ

namespace VaryingBondChain

open MPSTensor

variable {d D N : ℕ}

/-- The coefficient `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})` of the state of the chain, written as the
sum over the cyclic bond configurations `α` of `∏ₖ (A_k^{s_k})_{α_k α_{k+1}}`. -/
def coeff (A : VaryingBondChain d D N) (s : Fin N → Fin d) : ℂ :=
  ∑ α : (k : Fin N) → Fin (A.bondDim k), ∏ k, A.tensor k (s k) (α k) (α (finRotate N k))

/-- The state `|φ_N⟩ = ∑_s Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}}) |s⟩` of the chain. -/
noncomputable def state (A : VaryingBondChain d D N) : MPVSpace d N :=
  (EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm fun s => coeff A s

@[simp] theorem state_apply (A : VaryingBondChain d D N) (s : Cfg d N) :
    state A s = coeff A s := by
  simp [state, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- **Zero padding**: every matrix `A_k^i` of size `D_k × D_{k+1}` is extended by zeros to a
`D × D` matrix (`Matrix.zeroPad`), giving a chain with the common bond dimension `D`. -/
def zeroPad (A : VaryingBondChain d D N) : MPSChainTensor d D N :=
  fun k i => Matrix.zeroPad D (A.tensor k i)

/-- An entry of a padded matrix outside the rectangle `[0, D_k) × [0, D_{k+1})` vanishes. -/
theorem zeroPad_eq_zero (A : VaryingBondChain d D N) {k : Fin N} {i : Fin d} {a b : Fin D}
    (h : ¬(a.val < A.bondDim k ∧ b.val < A.bondDim (finRotate N k))) : zeroPad A k i a b = 0 :=
  Matrix.zeroPad_apply_eq_zero _ h

/-- **Zero padding preserves the state**: on a ring of `N ≥ 1` sites the padded chain has the
coefficients `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})` of the chain. -/
theorem coeff_zeroPad [NeZero N] (A : VaryingBondChain d D N) (s : Fin N → Fin d) :
    MPSChainTensor.coeff (zeroPad A) s = coeff A s := by
  classical
  rw [MPSChainTensor.coeff_eq_sum_cyclic, coeff, Fintype.sum_piFin_castLE_extend_zero A.bondDim
    (fun _ => D) _ A.bondDim_le]
  have hrot : ∀ k : Fin N, k + 1 = finRotate N k := fun k => by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne N)).symm⟩
    exact (finRotate_apply k).symm
  refine Finset.sum_congr rfl fun g _ => ?_
  simp_rw [hrot]
  by_cases hlt : ∀ k, (g k).val < A.bondDim k
  · rw [dite_eq_left hlt]
    exact Finset.prod_congr rfl fun k _ =>
      Matrix.zeroPad_apply_of_lt _ (hlt k) (hlt (finRotate N k))
  · rw [dite_eq_right hlt]
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hlt
    exact Finset.prod_eq_zero (Finset.mem_univ k) (zeroPad_eq_zero A fun h => hk h.1)

/-- The state of the chain is the state of the padded chain. -/
theorem state_eq_chainState_zeroPad [NeZero N] (A : VaryingBondChain d D N) (s : Cfg d N) :
    state A s = MPSChainTensor.coeff (zeroPad A) s := by
  rw [state_apply, coeff_zeroPad]

end VaryingBondChain

namespace MPSChainTensor

variable {d D : ℕ}

/-- A product of `n + 1` matrices whose factor `j` is supported on `[0, b_j) × [0, b_{j+1})` is
supported on `[0, b_0) × [0, b_{n+1})`. -/
theorem eval_eq_zero_of_support {n : ℕ} (C : MPSChainTensor d D (n + 1)) (b : Fin (n + 2) → ℕ)
    (hC : ∀ j i (α β : Fin D), ¬(α.val < b j.castSucc ∧ β.val < b j.succ) → C j i α β = 0)
    (σ : Fin (n + 1) → Fin d) {α β : Fin D} (h : ¬(α.val < b 0 ∧ β.val < b (Fin.last (n + 1)))) :
    eval C σ α β = 0 := by
  rcases not_and_or.mp h with hα | hβ
  · rw [eval_succ, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun γ _ => by
      rw [hC 0 _ α γ fun h' => hα h'.1, zero_mul]
  · rw [eval, Fin.prod_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun γ _ => ?_
    rw [hC (Fin.last n) _ γ β fun h' => hβ (by simpa using h'.2), mul_zero]

/-- A blocked tensor of a chain of `q ≥ 1` sites whose site `j` is supported on
`[0, b_j) × [0, b_{j+1})` is supported on `[0, b_0) × [0, b_q)`. -/
theorem blockTensor_eq_zero_of_support {q : ℕ} (C : MPSChainTensor d D q) (hq : 0 < q)
    (b : Fin (q + 1) → ℕ)
    (hC : ∀ j i (α β : Fin D), ¬(α.val < b j.castSucc ∧ β.val < b j.succ) → C j i α β = 0)
    (t : Fin (MPSTensor.blockPhysDim d q)) {α β : Fin D}
    (h : ¬(α.val < b 0 ∧ β.val < b (Fin.last q))) :
    blockTensor C t α β = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact eval_eq_zero_of_support C b hC _ h

end MPSChainTensor
