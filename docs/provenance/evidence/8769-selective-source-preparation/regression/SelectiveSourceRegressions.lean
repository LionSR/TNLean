import TNLean.PEPS.Approximation.SelectiveSourceFactorization
import TNLean.PEPS.Approximation.UnitPairSource

/-! Concrete source masks with an interior free slot, reversed endpoints, and spectators. -/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
open TNLean.PEPS.PairEffect
open TNLean.PEPS.PairEffect.SourceInventory

namespace SelectiveSourceRegressions

def refs : SourceInventory (Fin 3) :=
  [PairSource.unit 1 2 (by decide), PairSource.unit 0 1 (by decide),
    PairSource.unit 2 1 (by decide)]

def half : Fin refs.length → HSpace := fun _ ↦ HSpace.of ℂ

def mixed : Fin refs.length → Bool := fun i ↦ decide (i.val = 1)

def unitVector : ℂ ⊗[ℂ] ℂ := (1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)

def fixed (free : Fin refs.length → Bool) :
    ∀ i, free i = false → half i ⊗[ℂ] half i := fun _ _ ↦ unitVector

theorem fixed_normalized (free : Fin refs.length → Bool) :
    ∀ i h, ‖fixed free i h‖ = 1 := by
  intro i h
  exact (TensorProduct.norm_tmul (1 : ℂ) (1 : ℂ)).trans (by simp)

theorem mixed_free_layout :
    freeSlotLayout refs half half mixed =
      [⟨0, HSpace.of ℂ⟩, ⟨1, HSpace.of ℂ⟩] := rfl

theorem mixed_fixed_order (ℓ : Layout (Fin 3)) :
    ((prepareSelected refs half half mixed (fixed mixed) ℓ).sources.map
      (fun s ↦ (s.left, s.right))) = [(1, 2), (2, 1)] := by
  rw [sources_prepareSelected]
  rfl

theorem all_free_sources (ℓ : Layout (Fin 3)) :
    (prepareSelected refs half half (fun _ ↦ true) (fixed fun _ ↦ true) ℓ).sources =
      [] := by
  rw [sources_prepareSelected]
  rfl

theorem all_fixed_sources (ℓ : Layout (Fin 3)) :
    (prepareSelected refs half half (fun _ ↦ false) (fixed fun _ ↦ false) ℓ).sources =
      refs := by
  rw [sources_prepareSelected]
  rfl

theorem all_fixed_input : freeSlotLayout refs half half (fun _ ↦ false) = [] := rfl

theorem mixed_recovery (ζ : ∀ i, half i ⊗[ℂ] half i) (ℓ : Layout (Fin 3)) :
    (prepareSelected refs half half mixed (fixed mixed) ℓ).eval ∘L
        (prepareFreeSlots refs half half mixed ζ ℓ).eval =
      (prepareSlots refs half half
        (fun i ↦ if i.val = 1 then ζ i else unitVector) ℓ).eval := by
  have hfill : fillSourceVectors refs half half mixed (fixed mixed) ζ =
      fun i ↦ if i.val = 1 then ζ i else unitVector := by
    funext i
    by_cases h : i.val = 1 <;> simp [fillSourceVectors, mixed, fixed, h]
    rfl
  rw [← hfill]
  exact eval_prepareSelected_prepareFreeSlots refs half half mixed (fixed mixed) ζ ℓ

theorem mixed_allowed (ℓ : Layout (Fin 3)) :
    (prepareSelected refs half half mixed (fixed mixed) ℓ).IsAllowed :=
  isAllowed_prepareSelected refs half half mixed (fixed mixed) (fixed_normalized mixed) ℓ

def side (p : Fin 3) : Bool := decide (p.val = 0)

theorem mixed_internal :
    ∀ i, mixed i = false → side (refs.get i).left = side (refs.get i).right := by
  decide

def split (ℓ : Layout (Fin 3)) :=
  isoL (Layout.partitionIso (fun b : Bool ↦ b) (Layout.mapOwner side ℓ)) ∘L
    isoL (Layout.mapOwnerIso side ℓ)

theorem mixed_partition (ℓ : Layout (Fin 3)) :
    let L := freeSlotLayout refs half half mixed ++ ℓ
    let M := slotLayout refs half half ++ ℓ
    ∃ A : Mem (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner side L)) →L[ℂ]
        Mem (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner side M)),
      ∃ B : Mem (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner side L)) →L[ℂ]
          Mem (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner side M)),
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        ∀ ζ : ∀ i, half i ⊗[ℂ] half i,
          split M ∘L (prepareSlots refs half half
              (fillSourceVectors refs half half mixed (fixed mixed) ζ) ℓ).eval =
            TensorProduct.mapL A B ∘L split L ∘L
              (prepareFreeSlots refs half half mixed ζ ℓ).eval := by
  obtain ⟨a, b, _, _, _, _, ha, hb, _, he⟩ :=
    Word.exists_selective_partition side refs half half mixed (fixed mixed)
      (fixed_normalized mixed) mixed_internal ℓ
      (Word.id (slotLayout refs half half ++ ℓ)) trivial rfl
  refine ⟨a.eval, b.eval, ha, hb, ?_⟩
  intro ζ
  simpa only [Word.eval, id_comp, split] using he ζ

end SelectiveSourceRegressions
