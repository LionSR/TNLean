/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorComponents
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Unique initial regions on closed-half components

The target assigns one unique actual initial open region to each connected
component of the closed square of half-radius after deleting the actual
identifier-change radial segments. The origin, valid pitch residues, fine
cell, and mark are arbitrary under the initial-region hypotheses. Different
components may carry the same initial identifier, and the change set may be
empty.

This is an unfinished draft target. The proof remains incomplete.
It does not establish the full isolated-star or
recursive two-family assertion.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 333–370, especially 361–370,
and `prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently stated from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Unproved draft target: every connected component of the actual cut closed
square of half-radius lies in a unique initial open region. Distinct
components may have the same initial identifier.

Local auxiliary to OpenAI, Section 11, `geometry:initial-stars`, lines
333–370, especially 361–370, and `prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proof remains incomplete. -/
theorem exists_unique_initialRegion_of_closedHalf_component
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let I := InitialRegionIndex o k₀ Z C a b hC h₀
    let σ : J → I :=
      initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
    let L : Set (ℝ × ℝ) :=
      ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
        segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
    let Ω := Metric.closedBall v (r / 2) \ L
    ∀ q : ConnectedComponents Ω, ∃! i : I,
      ∀ x : Ω, ConnectedComponents.mk x = q →
        x.val ∈ initialOpenRegion o k₀ Z C a b hC h₀ i := by
  classical
  intro ℓ r oSmall J I σ L Ω q
  done

end TNLean.PEPS.AreaLaw.Geometry
