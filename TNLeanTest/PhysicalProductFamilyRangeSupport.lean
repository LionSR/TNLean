/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PhysicalProductFamilyRangeSupport

/-! # Site-dependent product-range regressions -/

open scoped BigOperators Matrix
open TNLean.PEPS

noncomputable section
set_option linter.hashCommand false

-- The generic statement needs no rank assumptions and only finiteness of Out.
example {Site In Out : Type*} [Fintype Site] [DecidableEq Site]
    [Fintype In] [Finite Out] (F : Site → Matrix Out In ℂ)
    (ψ : (Site → Out) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin (F v)) :=
  mem_range_physicalProductFamilyMap_iff F ψ

-- All alphabets and the site set can be empty simultaneously.
example (F : Empty → Matrix Empty Empty ℂ) (ψ : (Empty → Empty) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap F) := by
  apply (mem_range_physicalProductFamilyMap_iff F ψ).2
  intro v
  exact v.elim

-- Empty sites impose no support restriction, even with an empty input alphabet.
example (F : Empty → Matrix Bool Empty ℂ) (ψ : (Empty → Bool) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap F) := by
  apply (mem_range_physicalProductFamilyMap_iff F ψ).2
  intro v
  exact v.elim

-- With a genuine site and empty input, the product range is zero.
example (F : Bool → Matrix Bool Empty ℂ) (ψ : (Bool → Bool) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap F) ↔ ψ = 0 := by
  have hmap : physicalProductFamilyMap F = 0 := by
    ext χ τ
    simp [physicalProductFamilyMap_apply]
  simp [hmap]

-- A genuine site with empty output has the zero-dimensional coefficient space.
example (F : Unit → Matrix Empty Bool ℂ) (ψ : (Unit → Empty) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap F) := by
  apply (mem_range_physicalProductFamilyMap_iff F ψ).2
  intro v τ
  exact (τ v).elim

-- The local matrices may have different ranks, here zero and two.
private def differentRanks (v : Bool) : Matrix Bool Bool ℂ := if v then 1 else 0

example (ψ : (Bool → Bool) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap differentRanks) ↔ ψ = 0 := by
  constructor
  · intro hψ
    have hslice := (mem_range_physicalProductFamilyMap_iff differentRanks ψ).1 hψ false
    funext τ
    have hzero := hslice τ
    simp only [differentRanks, Bool.false_eq_true, ↓reduceIte, Matrix.mulVecLin_zero,
      LinearMap.range_zero, Submodule.mem_bot] at hzero
    simpa only [Function.update_eq_self, Pi.zero_apply] using congr_fun hzero (τ false)
  · rintro rfl
    exact Submodule.zero_mem _

-- A nonzero proper range at one site can coexist with a full range at another.
private def nonzeroDifferentRanks (v : Bool) : Matrix Bool Bool ℂ :=
  if v then 1 else Matrix.diagonal (fun s => if s then 0 else 1)

private def supportedVector (τ : Bool → Bool) : ℂ := if τ false then 0 else 1

example : supportedVector ∈ LinearMap.range
    (physicalProductFamilyMap nonzeroDifferentRanks) := by
  refine ⟨supportedVector, physicalProductFamilyMap_fixed_of_slices_fixed _ _ ?_⟩
  intro v τ
  cases v
  · ext s
    cases s <;> simp [nonzeroDifferentRanks, supportedVector, Matrix.mulVec_diagonal]
  · simp [nonzeroDifferentRanks]

-- The intended horizontal/vertical family can vary at every physical bond.
example {In Out : Type*} [Fintype In] [Finite Out]
    (Uh Uv : TorusVertex 2 2 → Matrix Out In ℂ)
    (ψ : ((TorusVertex 2 2 × Bool) → Out) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap
      (fun b : TorusVertex 2 2 × Bool => if b.2 then Uv b.1 else Uh b.1)) ↔
      ∀ b τ, (fun s => ψ (Function.update τ b s)) ∈
        LinearMap.range (Matrix.mulVecLin (if b.2 then Uv b.1 else Uh b.1)) :=
  mem_range_physicalProductFamilyMap_iff _ _

/--
info: 'TNLean.PEPS.mem_range_physicalProductFamilyMap_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.mem_range_physicalProductFamilyMap_iff
