/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage

/-!
# Facts about the chosen initial repair marks

The initial repair stage uses one joint choice of belt residues, a finite
mark set, and incident scales. The theorem below records the sparse cell
counts, finite layer support, incidence, scale minimality, separation, and
injectivity for those same choices. It introduces no new mark family or
choice of residues. Its incidence and scale facts serve both the geometric
induction and the weighted count of descendants.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:belt-count` and
`geometry:initial-stars`, lines 212–233 and 325–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The sparse cells and geometric properties attached to the actual initial
repair stage, with the exact residue choices used in its definition.
Source: area-law Section 11, `geometry:belt-count` and
`geometry:initial-stars`, lines 212–233 and 325–363. -/
theorem initialRepairStage_mark_spec (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
      o Λ A C k₀ hC h₀
    let a := Classical.choose h
    let hb := Classical.choose_spec h
    let b := Classical.choose hb
    let F := fun k => beltCellIndices
      (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
    let D := initialRepairStage o Λ A C k₀ hC h₀
    (∀ k, ((F k).card : ℝ) ≤
      64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) ∧
    Set.Finite {k | (F k).Nonempty} ∧
    (∀ p : D.markIndex, 0 < D.scale p ∧ ∃ k z,
      k₀ ≤ k ∧ z ∈ F k ∧ D.location p ∈ beltCellMarks o (fineScaleIndex k) z ∧
        D.scale p = (2 : ℝ) ^ fineScaleIndex k) ∧
    (∀ (p : D.markIndex) (k : ℕ) (z : ℤ × ℤ),
      k₀ ≤ k → z ∈ F k → D.location p ∈ beltCellMarks o (fineScaleIndex k) z →
        D.scale p ≤ (2 : ℝ) ^ fineScaleIndex k) ∧
    (∀ p q : D.markIndex, p ≠ q →
      max (D.scale p) (D.scale q) / 4 ≤ dist (D.location p) (D.location q)) ∧
    Function.Injective D.location := by
  let hchoice := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let hab := Classical.choose_spec (Classical.choose_spec hchoice)
  let hspec := Classical.choose_spec (Classical.choose_spec hab.2.2).2.2
  exact ⟨hab.1, hab.2.1, hspec.1, hspec.2.1, hspec.2.2, Subtype.val_injective⟩

end TNLean.PEPS.AreaLaw.Geometry
