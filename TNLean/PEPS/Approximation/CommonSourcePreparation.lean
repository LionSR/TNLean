/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonPairSources
import TNLean.PEPS.Approximation.PairSourceOrdering
import TNLean.PEPS.Approximation.SourcePairMaps
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Preparation and recovery in common source spaces

The source slots of a finite family have one fixed layout after their endpoint
spaces are embedded into the corresponding finite orthogonal sums. A concrete
composition of coordinate projections recovers each branch's original source
preparation. These projections are allowed local contractions and create no sources.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, common private slot spaces, lines 253–267.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P ι : Type} [Fintype ι]

/-- The register layout determined by the slots and their halfspaces, independent
of the prepared vectors. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267. -/
def slotLayout (R : SourceInventory P) (U V : Fin R.length → HSpace) : Layout P :=
  (ofSlots R U V (fun _ ↦ 0)).layout

/-- Preparation in the fixed source layout.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
def prepareSlots (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) : Word ℓ (slotLayout R U V ++ ℓ) :=
  ((ofSlots R U V η).prepare ℓ).castLayouts rfl
    (congrArg (· ++ ℓ) (layout_ofSlots_eq R U V η (fun _ ↦ 0)))

/-- Recover one source by its two local coordinate projections, preserving the tail.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 260–267. -/
private theorem common_pair_cons_expands (r : PairSource P) (U V : ι → HSpace)
    (η : ∀ ξ, U ξ ⊗[ℂ] V ξ) (ξ : ι) (T : SourceInventory P) :
    Expands
      (⟨r.left, r.right, r.distinct, PairSource.commonSpace U, PairSource.commonSpace V,
        PairSource.commonVector U V η ξ⟩ :: T)
      (⟨r.left, r.right, r.distinct, U ξ, V ξ, η ξ⟩ :: T) := by
  intro ℓ
  refine ⟨Word.mapPair r.left r.right
    (PairSource.commonProjection U ξ) (PairSource.commonProjection V ξ) (T.layout ++ ℓ),
    (Word.mapPair_spec _ _ _ _ (PairSource.norm_commonProjection_le _ _)
      (PairSource.norm_commonProjection_le _ _) _).1,
    (Word.mapPair_spec _ _ _ _ (PairSource.norm_commonProjection_le _ _)
      (PairSource.norm_commonProjection_le _ _) _).2, ?_⟩
  have h := Word.eval_mapPair_source r.distinct (PairSource.commonProjection U ξ)
    (PairSource.commonProjection V ξ) (PairSource.commonVector U V η ξ) (T.layout ++ ℓ)
  simp only [PairSource.mapL_commonProjection_commonVector] at h
  exact (comp_assoc _ _ _).symm.trans (congrArg (· ∘L (T.prepare ℓ).eval) h)

/-- Coordinate projections recover every branch preparation from the common pair
spaces by actual allowed operations containing no sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
theorem common_ofSlots_expands (R : SourceInventory P) (U V : ι → Fin R.length → HSpace)
    (η : ∀ ξ i, U ξ i ⊗[ℂ] V ξ i) (ξ : ι) :
    (ofSlots R (fun i ↦ PairSource.commonSpace (fun ζ ↦ U ζ i))
      (fun i ↦ PairSource.commonSpace (fun ζ ↦ V ζ i))
      (fun i ↦ PairSource.commonVector (fun ζ ↦ U ζ i) (fun ζ ↦ V ζ i)
        (fun ζ ↦ η ζ i) ξ)).Expands (ofSlots R (U ξ) (V ξ) (η ξ)) := by
  induction R with
  | nil => exact Expands.refl []
  | cons r R ih =>
      rw [ofSlots_cons, ofSlots_cons]
      exact (common_pair_cons_expands r (fun ζ ↦ U ζ 0) (fun ζ ↦ V ζ 0)
        (fun ζ ↦ η ζ 0) ξ _).trans
        (Expands.cons _ (ih (fun ζ i ↦ U ζ i.succ) (fun ζ i ↦ V ζ i.succ)
          (fun ζ i ↦ η ζ i.succ)))

end TNLean.PEPS.PairEffect.SourceInventory
