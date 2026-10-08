/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutOwnerMap
import TNLean.PEPS.Approximation.LocalPairSource
import TNLean.PEPS.Approximation.SourceOwnerMap
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Grouping parties in an actual composition

A map of party labels preserves the memory operator of a composition. A pair
whose owners become equal is retained as a local preparation of the same vector;
only pairs with distinct new owners remain in the pair-source inventory.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the affected and exterior calculations, lines 383–448.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

variable {P Q : Type}

/-- A list of registers at one owner remains local after changing owner labels. -/
private theorem homogeneous_mapOwner (f : P → Q) {p : P} {ℓ : Layout P}
    (h : ∀ r ∈ ℓ, r.owner = p) :
    ∀ r ∈ Layout.mapOwner f ℓ, r.owner = f p := by
  rintro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  exact congrArg f (h s hs)

/-- Change the owners of the operations, retaining internal pair vectors as local
preparations. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
def mapOwner (f : P → Q) : {ℓ ℓ' : Layout P} → Word ℓ ℓ' →
    Word (Layout.mapOwner f ℓ) (Layout.mapOwner f ℓ')
  | _, _, .id ℓ => .id (Layout.mapOwner f ℓ)
  | _, _, .comp w v => .comp (mapOwner f w) (mapOwner f v)
  | _, _, @Word.localMap _ p a b ha hb A ℓ =>
      (Word.localMap (f p) (homogeneous_mapOwner f ha) (homogeneous_mapOwner f hb)
        (isoL (Layout.mapOwnerIso f b) ∘L A ∘L isoL (Layout.mapOwnerIso f a).symm)
        (Layout.mapOwner f ℓ)).castLayouts
          (Layout.mapOwner_append f a ℓ).symm (Layout.mapOwner_append f b ℓ).symm
  | _, _, @Word.source _ p q hpq U V η ℓ => by
      classical
      exact if h : f p = f q then
        (localPairSource (f p) U V η (Layout.mapOwner f ℓ)).castLayouts rfl
          (by simp only [Layout.mapOwner_cons, h])
      else .source h U V η (Layout.mapOwner f ℓ)
  | _, _, .swap r s ℓ => .swap ⟨f r.owner, r.space⟩ ⟨f s.owner, s.space⟩
      (Layout.mapOwner f ℓ)
  | _, _, .frame r w => .frame ⟨f r.owner, r.space⟩ (mapOwner f w)

/-- Grouping owners preserves allowedness of the actual operations.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem isAllowed_mapOwner (f : P → Q) {ℓ ℓ' : Layout P}
    (w : Word ℓ ℓ') (hw : w.IsAllowed) : (w.mapOwner f).IsAllowed := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw hw.1, ihv hw.2⟩
  | @localMap p a b ha hb A ℓ =>
    rw [mapOwner, isAllowed_castLayouts]
    change ‖isoL (Layout.mapOwnerIso f b) ∘L A ∘L
      isoL (Layout.mapOwnerIso f a).symm‖ ≤ 1
    have ho : ‖isoL (Layout.mapOwnerIso f b)‖ ≤ 1 :=
      LinearIsometry.norm_toContinuousLinearMap_le _
    have hi : ‖isoL (Layout.mapOwnerIso f a).symm‖ ≤ 1 :=
      LinearIsometry.norm_toContinuousLinearMap_le _
    change ‖A‖ ≤ 1 at hw
    exact norm_comp_le_one ho (norm_comp_le_one (f := A) hw hi)
  | @source p q hpq U V η ℓ =>
    dsimp only [mapOwner]
    split
    · exact (isAllowed_castLayouts _ _ _).mpr (localPairSource_spec _ _ _ _ hw _).1
    · exact hw
  | swap => trivial
  | frame r w ih => exact ih hw

/-- The pair-source inventory consists exactly of the sources crossing the new
owner classes, in their original order. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
theorem sources_mapOwner (f : P → Q) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (w.mapOwner f).sources = SourceInventory.mapOwner f w.sources := by
  induction w with
  | id => rfl
  | comp w v ihw ihv => simp only [mapOwner, sources, SourceInventory.mapOwner_append, ihw, ihv]
  | localMap => simp only [mapOwner, sources_castLayouts, sources, SourceInventory.mapOwner_nil]
  | @source p q hpq U V η ℓ =>
    classical
    by_cases h : f p = f q
    · simp only [mapOwner, dite_eq_left h, sources_castLayouts]
      simp [SourceInventory.mapOwner, PairSource.mapOwner, h, sources, localPairSource]
    · simp [mapOwner, h, SourceInventory.mapOwner, PairSource.mapOwner, sources]
  | swap => rfl
  | frame r w ih => exact ih

private theorem memCongr_symm {a b : Layout Q} (h : a = b) :
    Layout.memCongr h.symm = (Layout.memCongr h).symm := by
  cases h
  rfl

private theorem localMap_owner_naturality (f : P → Q) (p : P) (a b ℓ : Layout P)
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (hfa : ∀ r ∈ Layout.mapOwner f a, r.owner = f p)
    (hfb : ∀ r ∈ Layout.mapOwner f b, r.owner = f p)
    (A : Mem a →L[ℂ] Mem b) (x : Mem (a ++ ℓ)) :
    ((Word.localMap (f p) hfa hfb
      (isoL (Layout.mapOwnerIso f b) ∘L A ∘L isoL (Layout.mapOwnerIso f a).symm)
      (Layout.mapOwner f ℓ)).castLayouts
        (Layout.mapOwner_append f a ℓ).symm (Layout.mapOwner_append f b ℓ).symm).eval
        (Layout.mapOwnerIso f (a ++ ℓ) x) =
      Layout.mapOwnerIso f (b ++ ℓ) ((Word.localMap p ha hb A ℓ).eval x) := by
  have he :
      ((Word.localMap (f p) hfa hfb
        (isoL (Layout.mapOwnerIso f b) ∘L A ∘L isoL (Layout.mapOwnerIso f a).symm)
        (Layout.mapOwner f ℓ)).castLayouts
          (Layout.mapOwner_append f a ℓ).symm (Layout.mapOwner_append f b ℓ).symm).eval ∘L
          isoL (Layout.mapOwnerIso f (a ++ ℓ)) ∘L isoL (appendIso a ℓ).symm =
        isoL (Layout.mapOwnerIso f (b ++ ℓ)) ∘L (Word.localMap p ha hb A ℓ).eval ∘L
          isoL (appendIso a ℓ).symm := by
    apply clm_ext_tmul
    intro u z
    simp only [eval_castLayouts, memCongr_symm (Layout.mapOwner_append f a ℓ),
      memCongr_symm (Layout.mapOwner_append f b ℓ), LinearIsometryEquiv.symm_symm,
      eval, comp_apply, isoL_apply]
    rw [Layout.mapOwnerIso_append_tmul]
    simp only [LinearIsometryEquiv.apply_symm_apply, rTensor_tmul, comp_apply,
      isoL_apply, LinearIsometryEquiv.symm_apply_apply]
    apply (Layout.memCongr (Layout.mapOwner_append f b ℓ)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, Layout.mapOwnerIso_append_tmul]
  have h := DFunLike.congr_fun he ((appendIso a ℓ) x)
  simpa only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply] using h


private theorem swap_mapOwnerIso (f : P → Q) (r s : Reg P) (ℓ : Layout P) :
    (Word.swap ⟨f r.owner, r.space⟩ ⟨f s.owner, s.space⟩ (Layout.mapOwner f ℓ)).eval ∘L
      isoL (Layout.mapOwnerIso f (r :: s :: ℓ)) =
    isoL (Layout.mapOwnerIso f (s :: r :: ℓ)) ∘L (Word.swap r s ℓ).eval := by
  apply clm_ext_tmul₃
  intro x y z
  change leftCommL r.space s.space (Mem (Layout.mapOwner f ℓ))
    (x ⊗ₜ (y ⊗ₜ Layout.mapOwnerIso f ℓ z)) =
      y ⊗ₜ (x ⊗ₜ Layout.mapOwnerIso f ℓ z)
  exact leftCommL_tmul x y (Layout.mapOwnerIso f ℓ z)

private theorem mapOwnerIso_assocL (f : P → Q) (p q : P) (U V : HSpace)
    (ℓ : Layout P) (η : U ⊗[ℂ] V) (x : Mem ℓ) :
    Layout.mapOwnerIso f (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ)
      (assocL U V (Mem ℓ) (η ⊗ₜ x)) =
    assocL U V (Mem (Layout.mapOwner f ℓ)) (η ⊗ₜ Layout.mapOwnerIso f ℓ x) := by
  apply (TensorProduct.assocIsometry ℂ U V (Mem (Layout.mapOwner f ℓ))).symm.injective
  rw [show Layout.mapOwnerIso f (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ) =
    ((Layout.mapOwnerIso f ℓ).lTensor V).lTensor U from rfl]
  rw [iso_lTensor_apply (E := U) ((Layout.mapOwnerIso f ℓ).lTensor V), isoL_lTensor]
  rw [lTensor_lTensor_assoc_symm]
  simp only [assocL, isoL_apply, LinearIsometryEquiv.symm_apply_apply, lTensor_tmul]

private theorem source_mapOwnerIso (f : P → Q) {p q : P} (hpq : p ≠ q)
    (hf : f p ≠ f q) (U V : HSpace) (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    (Word.source hf U V η (Layout.mapOwner f ℓ)).eval ∘L
      isoL (Layout.mapOwnerIso f ℓ) =
    isoL (Layout.mapOwnerIso f (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ)) ∘L
      (Word.source hpq U V η ℓ).eval := by
  ext x
  exact (mapOwnerIso_assocL f p q U V ℓ η x).symm
private theorem memCongr_pair_owner (a b : Q) (h : a = b) (U V : HSpace)
    (ℓ : Layout Q) (z : Mem (⟨a, U⟩ :: ⟨a, V⟩ :: ℓ)) :
    Layout.memCongr (show ⟨a, U⟩ :: ⟨a, V⟩ :: ℓ = ⟨a, U⟩ :: ⟨b, V⟩ :: ℓ by
      rw [h]) z = z := by
  cases h
  rfl

private theorem localSource_mapOwnerIso (f : P → Q) {p q : P} (hpq : p ≠ q)
    (hf : f p = f q) (U V : HSpace) (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    ((Word.localPairSource (f p) U V η (Layout.mapOwner f ℓ)).castLayouts rfl
      (show ⟨f p, U⟩ :: ⟨f p, V⟩ :: Layout.mapOwner f ℓ =
        Layout.mapOwner f (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ) by
          simp only [Layout.mapOwner_cons, hf])).eval ∘L
        isoL (Layout.mapOwnerIso f ℓ) =
    isoL (Layout.mapOwnerIso f (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ)) ∘L
      (Word.source hpq U V η ℓ).eval := by
  ext x
  rw [Word.eval_castLayouts]
  simp only [comp_apply, isoL_apply, Word.eval_localPairSource, appendLeft_apply,
    Word.eval_source]
  change Layout.memCongr (a := ⟨f p, U⟩ :: ⟨f p, V⟩ :: Layout.mapOwner f ℓ)
    (b := ⟨f p, U⟩ :: ⟨f q, V⟩ :: Layout.mapOwner f ℓ) _
    (assocL U V (Mem (Layout.mapOwner f ℓ))
    (η ⊗ₜ Layout.mapOwnerIso f ℓ x)) = _
  rw [memCongr_pair_owner (f p) (f q) hf]
  exact (mapOwnerIso_assocL f p q U V ℓ η x).symm

/-- Grouping owners intertwines the actual memory operators by the canonical
isometries. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem eval_mapOwner (f : P → Q) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (x : Mem ℓ) :
    (w.mapOwner f).eval (Layout.mapOwnerIso f ℓ x) =
      Layout.mapOwnerIso f ℓ' (w.eval x) := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
    simp only [mapOwner, eval_comp, comp_apply, ihw, ihv]
  | @localMap p a b ha hb A ℓ =>
    exact localMap_owner_naturality f p a b ℓ ha hb
      (homogeneous_mapOwner f ha) (homogeneous_mapOwner f hb) A x
  | @source p q hpq U V η ℓ =>
    classical
    by_cases h : f p = f q
    · simp only [mapOwner, dite_eq_left h]
      exact DFunLike.congr_fun (localSource_mapOwnerIso f hpq h U V η ℓ) x
    · simp only [mapOwner, dite_eq_right h]
      exact DFunLike.congr_fun (source_mapOwnerIso f hpq h U V η ℓ) x
  | swap r s ℓ =>
    exact DFunLike.congr_fun (swap_mapOwnerIso f r s ℓ) x
  | @frame r ℓ ℓ' w ih =>
    have he : (mapOwner f (frame r w)).eval ∘L
        isoL (Layout.mapOwnerIso f (r :: ℓ)) =
        isoL (Layout.mapOwnerIso f (r :: ℓ')) ∘L (frame r w).eval := by
      apply clm_ext_tmul
      intro u z
      change u ⊗ₜ (w.mapOwner f).eval (Layout.mapOwnerIso f ℓ z) =
        u ⊗ₜ Layout.mapOwnerIso f ℓ' (w.eval z)
      rw [ih]
    exact DFunLike.congr_fun he x

/-- The operator identity for grouping owners, in continuous-linear-map form.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem eval_mapOwner_comp (f : P → Q) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (w.mapOwner f).eval ∘L isoL (Layout.mapOwnerIso f ℓ) =
      isoL (Layout.mapOwnerIso f ℓ') ∘L w.eval := by
  ext x
  exact eval_mapOwner f w x

end TNLean.PEPS.PairEffect.Word
