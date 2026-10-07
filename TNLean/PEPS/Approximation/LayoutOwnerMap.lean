/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyPartition

/-!
# Changing the owners of registers

Changing party labels leaves the register spaces and their order unchanged.
The resulting memory identification is the tensor product of identities. It
commutes with the canonical identification for concatenated register lists.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the affected and exterior systems at lines 383–427.
-/
/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-party-coarsening-layout-layout.mapowner
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwner

Provenance-ID: 8769-party-coarsening-layout-layout.mapowner_nil
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwner_nil

Provenance-ID: 8769-party-coarsening-layout-layout.mapowner_cons
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwner_cons

Provenance-ID: 8769-party-coarsening-layout-layout.mapowner_append
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwner_append

Provenance-ID: 8769-party-coarsening-layout-layout.mapowneriso
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwnerIso

Provenance-ID: 8769-party-coarsening-layout-layout.mapowneriso_nil_apply
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwnerIso_nil_apply

Provenance-ID: 8769-party-coarsening-layout-layout.mapowneriso_cons_tmul
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwnerIso_cons_tmul

Provenance-ID: 8769-party-coarsening-layout-layout.mapowneriso_append_tmul
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwnerIso_append_tmul

Provenance-ID: 8769-party-coarsening-layout-layout.mapowneriso_append
Downstream declaration: TNLean.PEPS.PairEffect.Layout.mapOwnerIso_append
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Layout
open ContinuousLinearMap
variable {P Q : Type}

/-- Change each owner label, preserving every register space and position. -/
@[reducible] def mapOwner (f : P → Q) (ℓ : Layout P) : Layout Q :=
  ℓ.map (fun r ↦ ⟨f r.owner, r.space⟩)

@[simp] theorem mapOwner_nil (f : P → Q) : mapOwner f [] = [] := rfl

@[simp] theorem mapOwner_cons (f : P → Q) (r : Reg P) (ℓ : Layout P) :
    mapOwner f (r :: ℓ) = ⟨f r.owner, r.space⟩ :: mapOwner f ℓ := rfl

@[simp] theorem mapOwner_append (f : P → Q) (a b : Layout P) :
    mapOwner f (a ++ b) = mapOwner f a ++ mapOwner f b := List.map_append

/-- The canonical memory isometry induced by changing owner labels. -/
def mapOwnerIso (f : P → Q) : (ℓ : Layout P) → Mem ℓ ≃ₗᵢ[ℂ] Mem (mapOwner f ℓ)
  | [] => LinearIsometryEquiv.refl ℂ ℂ
  | r :: ℓ => (mapOwnerIso f ℓ).lTensor r.space

@[simp] theorem mapOwnerIso_nil_apply (f : P → Q) (z : ℂ) :
    mapOwnerIso f [] z = z := rfl

@[simp] theorem mapOwnerIso_cons_tmul (f : P → Q) (r : Reg P) (ℓ : Layout P)
    (x : r.space) (y : Mem ℓ) : mapOwnerIso f (r :: ℓ) (x ⊗ₜ y) =
      x ⊗ₜ mapOwnerIso f ℓ y := rfl

/-- Appending a head register commutes with the equality identification of the tail. -/
private theorem memCongr_cons_tmul (r : Reg Q) {a b : Layout Q} (h : a = b)
    (x : r.space) (y : Mem a) :
    memCongr (congrArg (r :: ·) h) (x ⊗ₜ y) = x ⊗ₜ memCongr h y := by
  cases h
  rfl

/-- Changing owners respects the canonical tensor product for concatenated layouts.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem mapOwnerIso_append_tmul (f : P → Q) (a b : Layout P)
    (x : Mem a) (y : Mem b) :
    memCongr (mapOwner_append f a b)
      (mapOwnerIso f (a ++ b) ((appendIso a b).symm (x ⊗ₜ y))) =
      (appendIso (mapOwner f a) (mapOwner f b)).symm
        (mapOwnerIso f a x ⊗ₜ mapOwnerIso f b y) := by
  induction a with
  | nil =>
    change mapOwnerIso f b (x • y) = x • mapOwnerIso f b y
    exact map_smul (mapOwnerIso f b) x y
  | cons r a ih =>
    induction x using TensorProduct.inductionOn with
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul u x =>
      change memCongr (congrArg ((⟨f r.owner, r.space⟩ : Reg Q) :: ·)
        (mapOwner_append f a b))
        (u ⊗ₜ mapOwnerIso f (a ++ b) ((appendIso a b).symm (x ⊗ₜ y))) =
        u ⊗ₜ (appendIso (mapOwner f a) (mapOwner f b)).symm
          (mapOwnerIso f a x ⊗ₜ mapOwnerIso f b y)
      rw [memCongr_cons_tmul _ (mapOwner_append f a b), ih]

/-- The memory identification intertwines the concatenation isometries as linear maps.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem mapOwnerIso_append (f : P → Q) (a b : Layout P) :
    isoL (memCongr (mapOwner_append f a b)) ∘L isoL (mapOwnerIso f (a ++ b)) ∘L
      isoL (appendIso a b).symm =
    isoL (appendIso (mapOwner f a) (mapOwner f b)).symm ∘L
      TensorProduct.mapL (isoL (mapOwnerIso f a)) (isoL (mapOwnerIso f b)) := by
  apply clm_ext_tmul
  intro x y
  simpa only [comp_apply, isoL_apply, TensorProduct.mapL_tmul] using
    mapOwnerIso_append_tmul f a b x y

end TNLean.PEPS.PairEffect.Layout
