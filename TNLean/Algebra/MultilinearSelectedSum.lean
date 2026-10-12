/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Basic.Complex.Basic

/-!
# Finite sums in selected multilinear arguments

Expanding a finite collection of arguments of a complex multilinear map gives
a sum over their independent choices. All other arguments remain fixed.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

namespace MultilinearMap

/-- Expand a finite family of selected arguments of a multilinear map.
The unselected arguments are left at their recorded values. -/
theorem map_piecewise_sum_smul {I : Type} [DecidableEq I]
    {V : I → Type} [∀ i, AddCommMonoid (V i)] [∀ i, Module ℂ (V i)]
    {K : I → Type} [∀ i, Fintype (K i)]
    {M : Type} [AddCommMonoid M] [Module ℂ M]
    (F : MultilinearMap ℂ V M) (S : Finset I)
    (c : ∀ i, K i → ℂ) (v : ∀ i, K i → V i) (X : ∀ i, V i) :
    F (S.piecewise (fun i ↦ ∑ j, c i j • v i j) X) =
      ∑ z : ∀ i : S, K i, (∏ i : S, c i (z i)) •
        F (fun i ↦ if h : i ∈ S then v i (z ⟨i, h⟩) else X i) := by
  classical
  let G := F.domDomRestrict (fun i ↦ i ∈ S) (fun i ↦ X i)
  change G (fun i ↦ ∑ j, c i j • v i j) = _
  rw [G.map_sum]
  simp_rw [G.map_smul_univ]
  rfl

end MultilinearMap
