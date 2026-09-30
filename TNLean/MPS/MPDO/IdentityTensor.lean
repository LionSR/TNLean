/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs

/-!
# The identity matrix product operator tensor

The tensor with trivial bond whose letters are the Kronecker deltas `δ_{ij}` generates the
identity operator at every system size. It is the empty vertical stack of
`TNLean/MPS/MPDO/StackedLayers.lean`, and worked examples identify their own identity tensors
with it.

## Main definitions

* `MPOTensor.idTensor`: the trivial-bond tensor with letters `δ_{ij}`.

## Main results

* `MPOTensor.mpo_idTensor`: its periodic operator is the identity at every length.
-/

namespace MPOTensor

/-- The MPO tensor with trivial bond whose letters are $\delta_{ij}$.  It
generates the identity operator at every system size (`mpo_idTensor`) and
serves as the empty vertical stack in `MPOTensor.stackedTensor`. -/
noncomputable def idTensor (d : ℕ) : MPOTensor d 1 :=
  fun i j => if i = j then 1 else 0

/-- The identity tensor generates the identity operator at every system
size. -/
theorem mpo_idTensor (d N : ℕ) : mpo (idTensor d) N = 1 := by
  refine Matrix.ext fun σ τ => ?_
  simp only [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.one_apply]
  by_cases h : σ = τ
  · subst h
    rw [ite_eq_left rfl, List.prod_eq_one, Matrix.trace_one, Fintype.card_fin,
      Nat.cast_one]
    intro X hX
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hX
    simp [idTensor]
  · rw [ite_eq_right h]
    obtain ⟨l, hl⟩ : ∃ l, σ l ≠ τ l := Function.ne_iff.mp h
    have hzero : (0 : Matrix (Fin 1) (Fin 1) ℂ) ∈
        List.ofFn fun l => idTensor d (σ l) (τ l) :=
      List.mem_ofFn.mpr ⟨l, by simp [idTensor, hl]⟩
    rw [List.prod_eq_zero hzero, Matrix.trace_zero]

end MPOTensor
