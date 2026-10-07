/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentPhysicalProductRangeSupport

/-! # Product-range regressions with dependent alphabets -/

open scoped BigOperators Matrix
open TNLean.PEPS

noncomputable section
set_option linter.hashCommand false

-- All local alphabets are genuinely dependent and may have different cardinalities.
example {Site : Type*} [Fintype Site] [DecidableEq Site]
    {In Out : Site → Type*} [∀ v, Fintype (In v)] [∀ v, Finite (Out v)]
    (F : (v : Site) → Matrix (Out v) (In v) ℂ) (ψ : ((v : Site) → Out v) → ℂ) :
    ψ ∈ LinearMap.range (dependentPhysicalProductFamilyMap F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin (F v)) :=
  mem_range_dependentPhysicalProductFamilyMap_iff F ψ

-- Empty sites impose no restriction, including for empty local alphabets.
example (F : Empty → Matrix Empty Empty ℂ) (ψ : (Empty → Empty) → ℂ) :
    ψ ∈ LinearMap.range (dependentPhysicalProductFamilyMap F) := by
  apply (mem_range_dependentPhysicalProductFamilyMap_iff F ψ).2
  intro v
  exact v.elim

-- Rectangular maps may have independent input and output dimensions at both sites.
example (F : (v : Bool) → Matrix (Fin (if v then 3 else 2)) (Fin (if v then 2 else 1)) ℂ)
    (ψ : ((v : Bool) → Fin (if v then 3 else 2)) → ℂ) :
    ψ ∈ LinearMap.range (dependentPhysicalProductFamilyMap F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin (F v)) :=
  mem_range_dependentPhysicalProductFamilyMap_iff F ψ

-- A single empty input fiber suffices to force the product range to be zero.
example (F : (v : Bool) → Matrix (Fin (if v then 3 else 2)) (Fin (if v then 2 else 0)) ℂ)
    (ψ : ((v : Bool) → Fin (if v then 3 else 2)) → ℂ) :
    ψ ∈ LinearMap.range (dependentPhysicalProductFamilyMap F) ↔ ψ = 0 := by
  let : IsEmpty ((v : Bool) → Fin (if v then 2 else 0)) :=
    ⟨fun σ => Fin.elim0 (σ false)⟩
  have hmap : dependentPhysicalProductFamilyMap F = 0 := by
    ext χ τ
    simp [dependentPhysicalProductFamilyMap_apply]
  simp [hmap]

-- A single empty output fiber makes the coefficient space zero-dimensional.
example (F : (v : Bool) → Matrix (Fin (if v then 3 else 0)) (Fin (if v then 2 else 1)) ℂ)
    (ψ : ((v : Bool) → Fin (if v then 3 else 0)) → ℂ) :
    ψ ∈ LinearMap.range (dependentPhysicalProductFamilyMap F) := by
  apply (mem_range_dependentPhysicalProductFamilyMap_iff F ψ).2
  intro v τ
  exact Fin.elim0 (τ false)

-- A nonzero image with unequal input and output alphabets at different sites.
example : (fun _ : (v : Bool) → Fin (if v then 3 else 2) => (1 : ℂ)) ∈
    LinearMap.range (dependentPhysicalProductFamilyMap
      (fun (v : Bool) (_ : Fin (if v then 3 else 2)) (_ : Fin (if v then 2 else 1)) => 1)) := by
  classical
  let σ : (v : Bool) → Fin (if v then 2 else 1) := fun v => ⟨0, by cases v <;> decide⟩
  refine ⟨Pi.single σ 1, ?_⟩
  ext τ
  simp [dependentPhysicalProductFamilyMap, dependentPhysicalProductFamilyMatrix,
    Matrix.mulVec_single, Matrix.col]

/--
info: 'TNLean.PEPS.mem_range_dependentPhysicalProductFamilyMap_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.mem_range_dependentPhysicalProductFamilyMap_iff
