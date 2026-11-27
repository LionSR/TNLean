/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Defs

/-!
# GHZ tensors and their one-dimensional product sectors

The binary diagonal tensor and its two bond-one sectors, with their word evaluations and
periodic vectors. Symmetry and transfer-map properties are proved in the GHZ example.
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

namespace MPSTensor

/-- The GHZ MPS tensor: $A^0 = |0\rangle\langle 0|$, $A^1 = |1\rangle\langle 1|$. -/
def ghzTensor : MPSTensor 2 2 := fun i => Matrix.diagonal (Pi.single i 1)

@[simp] lemma ghzTensor_apply (i : Fin 2) :
    ghzTensor i = Matrix.diagonal (Pi.single i 1) := rfl

/-- The one-dimensional GHZ sector labeled by `x`. It is supported only at
physical value `x`. -/
def ghzSectorTensor (x : Fin 2) : MPSTensor 2 1 := fun p =>
  if p = x then 1 else 0

/-- The GHZ sector labeled by `x` equals the one-dimensional identity at `x`. -/
@[simp] theorem ghzSectorTensor_apply_same (x : Fin 2) :
    ghzSectorTensor x x = 1 := by
  simp [ghzSectorTensor]

/-- Word evaluation of a GHZ sector: one on the constant word of its label, zero otherwise. -/
theorem evalWord_ghzSectorTensor (x : Fin 2) {N : ℕ} (σ : Fin N → Fin 2) :
    Kraus.evalWord (ghzSectorTensor x) (List.ofFn σ) =
      if σ = (fun _ ↦ x) then 1 else 0 := by
  induction N with
  | zero => simp [Subsingleton.elim σ (fun _ ↦ x)]
  | succ N ih =>
      rw [List.ofFn_succ, Kraus.evalWord_cons, ih (fun i ↦ σ i.succ)]
      have key : (σ = fun _ ↦ x) ↔ (σ 0 = x ∧ (fun i : Fin N ↦ σ i.succ) = fun _ ↦ x) := by
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · rintro ⟨h0, hs⟩
          funext i
          exact Fin.cases h0 (fun j ↦ congrFun hs j) i
      by_cases h0 : σ 0 = x <;>
        by_cases hs : (fun i : Fin N ↦ σ i.succ) = (fun _ ↦ x) <;>
          simp [ghzSectorTensor, h0, hs, key]

/-- The periodic vector of a GHZ sector, a product state, is the indicator of the constant
configuration. -/
theorem mpv_ghzSectorTensor (x : Fin 2) {N : ℕ} :
    (fun σ : Fin N → Fin 2 ↦ MPTensor.mpv (ghzSectorTensor x) σ) =
      Pi.single (fun _ ↦ x) 1 := by
  funext σ
  rw [MPTensor.mpv, MPTensor.coeff, evalWord_ghzSectorTensor, Pi.single_apply]
  split_ifs <;> simp

/-- Every one-dimensional GHZ sector is injective. -/
theorem ghzSectorTensor_isInjective (x : Fin 2) :
    Kraus.IsInjective (ghzSectorTensor x) := by
  rw [Kraus.IsInjective]
  apply top_unique
  intro M _
  have hOne : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Submodule.span ℂ (Set.range (ghzSectorTensor x)) :=
    Submodule.subset_span ⟨x, ghzSectorTensor_apply_same x⟩
  have hM : M = M 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hM]
  exact Submodule.smul_mem _ _ hOne

end MPSTensor
