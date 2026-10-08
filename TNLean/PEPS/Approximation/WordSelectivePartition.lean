/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SelectiveSourceFactorization

/-!
# Selective factorization of the original sources of a composition

Enumerate the pair sources of an allowed composition and divide the parties into
two sides. Retain as free every source crossing the division, together with any
chosen internal sources. Preparing all remaining original source vectors leaves
a tensor product of two contractions on the entire free input space. These
contractions are chosen before the vectors supplied to the free source registers.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source preparation at lines 246–251 and separation on all
free inputs at lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace SourceInventory

/-- Enumerating the entries of an inventory recovers the original source records.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–251. -/
private theorem ofSlots_actual (R : SourceInventory P) :
    ofSlots R (fun i ↦ (R.get i).leftSpace) (fun i ↦ (R.get i).rightSpace)
      (fun i ↦ (R.get i).vector) = R := by
  exact List.ofFn_get R

/-- The slots of the original sources have precisely their original register layout.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–251. -/
private theorem slotLayout_actual (R : SourceInventory P) :
    slotLayout R (fun i ↦ (R.get i).leftSpace) (fun i ↦ (R.get i).rightSpace) = R.layout := by
  exact (layout_ofSlots_eq R _ _ (fun _ ↦ 0) (fun i ↦ (R.get i).vector)).trans
    (congrArg SourceInventory.layout (ofSlots_actual R))

/-- Preparing the source records in their own coordinate spaces agrees with the
original ordered preparation. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–251. -/
private theorem prepareSlots_actual (R : SourceInventory P) (ℓ : Layout P) :
    prepareSlots R (fun i ↦ (R.get i).leftSpace) (fun i ↦ (R.get i).rightSpace)
      (fun i ↦ (R.get i).vector) ℓ =
        (R.prepare ℓ).castLayouts rfl (congrArg (· ++ ℓ) (slotLayout_actual R).symm) := by
  unfold prepareSlots
  have hc : ∀ (S : SourceInventory P), S = R → ∀ (a : Layout P)
      (hS : S.layout ++ ℓ = a) (hR : R.layout ++ ℓ = a),
      (S.prepare ℓ).castLayouts rfl hS = (R.prepare ℓ).castLayouts rfl hR := by
    intro S h a hS hR
    cases h
    rfl
  exact hc _ (ofSlots_actual R) _ _ _
end SourceInventory

namespace Word
open SourceInventory

/-- Preparing the original ordered source list recovers an allowed composition
through an allowed composition containing no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–251. -/
private theorem exists_prepareSlots_actual {ℓ ℓ' : Layout P}
    (w : Word ℓ ℓ') (hw : w.IsAllowed) :
    let R := w.sources
    let U := fun i : Fin R.length ↦ (R.get i).leftSpace
    let V := fun i : Fin R.length ↦ (R.get i).rightSpace
    let η : ∀ i, U i ⊗[ℂ] V i := fun i ↦ (R.get i).vector
    ∃ v : Word (slotLayout R U V ++ ℓ) ℓ',
      v.IsAllowed ∧ v.sources = [] ∧
      v.eval ∘L (prepareSlots R U V η ℓ).eval = w.eval := by
  intro R U V η
  let h : R.layout ++ ℓ = slotLayout R U V ++ ℓ :=
    congrArg (· ++ ℓ) (SourceInventory.slotLayout_actual R).symm
  let v : Word (slotLayout R U V ++ ℓ) ℓ' := w.localPart.castLayouts h rfl
  have hv : v.IsAllowed := by
    simpa only [v, isAllowed_castLayouts] using isAllowed_localPart w hw
  have hs : v.sources = [] := by simp only [v, sources_castLayouts, sources_localPart]
  have he : v.eval ∘L (prepareSlots R U V η ℓ).eval = w.eval := by
    rw [SourceInventory.prepareSlots_actual R ℓ]
    ext x
    simp only [v, eval_castLayouts, comp_apply, isoL_apply]
    change w.localPart.eval ((Layout.memCongr h).symm
      (Layout.memCongr h ((R.prepare ℓ).eval x))) = w.eval x
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact eval_localPart_prepare w x
  exact ⟨v, hv, hs, he⟩

/-- A fixed preparation recovers the original operator from the two
contractions on all remaining free inputs. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–434. -/
private theorem exists_selective_partition_recovery (f : P → Bool)
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (hη : ∀ i, ‖η i‖ = 1)
    (free : Fin R.length → Bool)
    (hmask : ∀ i, free i = false → f (R.get i).left = f (R.get i).right)
    (ℓ : Layout P) {ℓ' : Layout P} (v : Word (slotLayout R U V ++ ℓ) ℓ')
    (hv : v.IsAllowed) (hs : v.sources = [])
    (F : Mem ℓ →L[ℂ] Mem ℓ')
    (he : v.eval ∘L (prepareSlots R U V η ℓ).eval = F) :
    let fixed : ∀ i, free i = false → U i ⊗[ℂ] V i := fun i _ ↦ η i
    let L := freeSlotLayout R U V free ++ ℓ
    let split (a : Layout P) :=
      isoL (Layout.partitionIso (fun b : Bool ↦ b) (Layout.mapOwner f a)) ∘L
        isoL (Layout.mapOwnerIso f a)
    ∃ a : Word (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f L))
        (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f ℓ')),
      ∃ b : Word (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f L))
          (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f ℓ')),
        a.IsAllowed ∧ b.IsAllowed ∧ a.sources = [] ∧ b.sources = [] ∧
        ‖a.eval‖ ≤ 1 ∧ ‖b.eval‖ ≤ 1 ∧
        split ℓ' ∘L (v.eval ∘L (prepareSelected R U V free fixed ℓ).eval) =
          TensorProduct.mapL a.eval b.eval ∘L split L ∧
        split ℓ' ∘L F = TensorProduct.mapL a.eval b.eval ∘L split L ∘L
          (prepareFreeSlots R U V free η ℓ).eval ∧
        ∀ ζ : ∀ i, U i ⊗[ℂ] V i,
          split ℓ' ∘L (v.eval ∘L
              (prepareSlots R U V (fillSourceVectors R U V free fixed ζ) ℓ).eval) =
            TensorProduct.mapL a.eval b.eval ∘L split L ∘L
              (prepareFreeSlots R U V free ζ ℓ).eval := by
  intro fixed L split
  have hfixed : ∀ i h, ‖fixed i h‖ = 1 := fun i _ ↦ hη i
  obtain ⟨a, b, ha, hb, hsa, hsb, hna, hnb, hall, hζ⟩ :=
    exists_selective_partition f R U V free fixed hfixed hmask ℓ v hv hs
  refine ⟨a, b, ha, hb, hsa, hsb, hna, hnb, hall, ?_, hζ⟩
  have hfill : fillSourceVectors R U V free fixed η = η := by
    funext i
    simp [fillSourceVectors, fixed]
  simpa only [hfill, he] using hζ η

-- Elaborating the dependent source-space signature and proof together avoids
-- repeated normalization of their memory instances within the default limit.
set_option Elab.async false in
/-- The original source inventory of an allowed composition admits selective
preparation followed by two local contractions. Every source crossing the party
division is retained as free. The factors are chosen before all replacement free
vectors, and filling the free slots with their original vectors recovers the
original composition. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–251 and 409–434. -/
theorem exists_selective_partition_of_word (f : P → Bool) {ℓ ℓ' : Layout P}
    (w : Word ℓ ℓ') (hw : w.IsAllowed) (free : Fin w.sources.length → Bool)
    (hmask : ∀ i, free i = false →
      f (w.sources.get i).left = f (w.sources.get i).right) :
    let R := w.sources
    let U := fun i : Fin R.length ↦ (R.get i).leftSpace
    let V := fun i : Fin R.length ↦ (R.get i).rightSpace
    let η : ∀ i, U i ⊗[ℂ] V i := fun i ↦ (R.get i).vector
    let fixed : ∀ i, free i = false → U i ⊗[ℂ] V i := fun i _ ↦ η i
    let L := freeSlotLayout R U V free ++ ℓ
    let split (a : Layout P) :=
      isoL (Layout.partitionIso (fun b : Bool ↦ b) (Layout.mapOwner f a)) ∘L
        isoL (Layout.mapOwnerIso f a)
    ∃ v : Word (slotLayout R U V ++ ℓ) ℓ',
      v.IsAllowed ∧ v.sources = [] ∧
      v.eval ∘L (prepareSlots R U V η ℓ).eval = w.eval ∧
      ∃ a : Word (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f L))
          (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f ℓ')),
        ∃ b : Word (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f L))
            (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f ℓ')),
          a.IsAllowed ∧ b.IsAllowed ∧ a.sources = [] ∧ b.sources = [] ∧
          ‖a.eval‖ ≤ 1 ∧ ‖b.eval‖ ≤ 1 ∧
          split ℓ' ∘L (v.eval ∘L (prepareSelected R U V free fixed ℓ).eval) =
            TensorProduct.mapL a.eval b.eval ∘L split L ∧
          split ℓ' ∘L w.eval = TensorProduct.mapL a.eval b.eval ∘L split L ∘L
            (prepareFreeSlots R U V free η ℓ).eval ∧
          ∀ ζ : ∀ i, U i ⊗[ℂ] V i,
            split ℓ' ∘L (v.eval ∘L
                (prepareSlots R U V (fillSourceVectors R U V free fixed ζ) ℓ).eval) =
              TensorProduct.mapL a.eval b.eval ∘L split L ∘L
                (prepareFreeSlots R U V free ζ ℓ).eval := by
  dsimp only
  obtain ⟨v, hv, hs, he⟩ := exists_prepareSlots_actual w hw
  refine ⟨v, hv, hs, he, ?_⟩
  exact exists_selective_partition_recovery f w.sources
    (fun i ↦ (w.sources.get i).leftSpace) (fun i ↦ (w.sources.get i).rightSpace)
    (fun i ↦ (w.sources.get i).vector)
    (fun i ↦ isNormalized_sources w hw (w.sources.get i) (List.get_mem w.sources i))
    free hmask ℓ v hv hs w.eval he
end Word
end TNLean.PEPS.PairEffect
