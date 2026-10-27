/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSProduct

/-!
# Applications of site products and bond-one representations

The scalar cap retains a nonzero empty-chain coefficient. An actual zero
internal bond produces the zero state. A nonzero one-site matrix unit placed
at the middle of a three-site chain has bond bound one.
-/

open Matrix
open scoped BigOperators
open TNLean.MPS.AreaLaw

noncomputable section

private def vacuumChain : OBCChainTensor 0 1 0 where
  bondDim := fun _ ↦ 1
  bondDim_le := fun _ ↦ le_rfl
  left_dim := rfl
  right_dim := rfl
  tensor := fun v ↦ v.elim0

example (c : ℂ) : ∃ c' : ℂ, ∃ f : Fin 0 → Fin 0 → ℂ,
    ∀ w : Fin 0 → Fin 0, c = c' * ∏ v, f v (w v) := by
  have h : IsOpenMPS 0 0 1 (fun _ ↦ c) :=
    ⟨vacuumChain, c, fun _ _ _ ↦ le_rfl,
      fun w ↦ by simp [OBCChainTensor.coeff_zero]⟩
  exact h.exists_eq_mul_prod

private def zeroBondChain : OBCChainTensor 2 1 2 where
  bondDim := fun k ↦ if k = 1 then 0 else 1
  bondDim_le := fun k ↦ by split <;> decide
  left_dim := by decide
  right_dim := by decide
  tensor := fun _ _ ↦ 0

example (w : Fin 2 → Fin 2) : zeroBondChain.coeff w = 0 :=
  zeroBondChain.coeff_eq_zero_of_bondDim_eq_zero w 1 (by decide)

example : ∃ c : ℂ, ∃ f : Fin 2 → Fin 2 → ℂ,
    ∀ w, zeroBondChain.coeff w = c * ∏ v, f v (w v) := by
  have h : IsOpenMPS 2 2 1 (fun w ↦ zeroBondChain.coeff w) :=
    ⟨zeroBondChain, 1, fun k _ _ ↦ zeroBondChain.bondDim_le k,
      fun w ↦ (one_mul _).symm⟩
  exact h.exists_eq_mul_prod

private def excitedMiddle (b : Fin 2) (v : Fin 3) : Fin 2 :=
  if v = 1 then b else 0

open Classical in
example : IsOpenMPS 3 (2 * 2) 1 (fun w ↦
    QuantumCircuit.embedOp (fun _ : Fin 1 ↦ (1 : Fin 3))
      (Matrix.single (fun _ : Fin 1 ↦ (0 : Fin 2)) (fun _ ↦ 1) 1)
      (fun v ↦ (w v).divNat) (fun v ↦ (w v).modNat)) :=
  isOpenMPS_operator_entries_embed_one_site 1 _

open Classical in
example : QuantumCircuit.embedOp (fun _ : Fin 1 ↦ (1 : Fin 3))
    (Matrix.single (fun _ : Fin 1 ↦ (0 : Fin 2)) (fun _ ↦ 1) 1)
    (excitedMiddle 0) (excitedMiddle 1) = 1 := by
  classical
  have hagree : QuantumCircuit.AgreeOff (fun _ : Fin 1 ↦ (1 : Fin 3))
      (excitedMiddle 0) (excitedMiddle 1) := by
    intro v hv
    have hne : v ≠ 1 := (hv 0).symm
    simp [excitedMiddle, hne]
  rw [QuantumCircuit.embedOp_apply, ite_eq_left hagree]
  simp [excitedMiddle, Function.comp_def]

end
