/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordOwnerMap
import TNLean.PEPS.Approximation.WordSelectedRestriction

/-!
# Restricting an allowed monomial to the parties it uses

An allowed monomial (`PartyChain`) that uses only selected parties acts, in the canonical
partition of the registers into selected and complementary ones, as the tensor product of a
monomial on the selected registers and a word on the complementary registers
(`PartyChain.partitionIso_eval`). Its pair effects join selected parties, so they stay in the
selected part, together with its pair sources (`Word.selectedPart`).

The owners of an allowed monomial may also be relabelled, as long as the two endpoints of each
pair effect keep distinct labels (`PartyChain.mapOwner`); the operator is transported by the
canonical identifications (`PartyChain.eval_mapOwner`). This is how a monomial on the registers
of a list of parties becomes a monomial indexed by these parties alone.

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
  lines 21–43, and the factorization `eq:compression-source-gate`, lines 233–251.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace Layout

theorem restrict_pair {f : P → Bool} {p q : P} (hp : f p = true) (hq : f q = true)
    (α β : Type) [Fintype α] [Fintype β] (ℓ : Layout P) :
    restrict f (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ) = ⟨p, euc α⟩ :: ⟨q, euc β⟩ :: restrict f ℓ := by
  simp [restrict_cons, hp, hq]

theorem restrict_not_pair {f : P → Bool} {p q : P} (hp : f p = true) (hq : f q = true)
    (α β : Type) [Fintype α] [Fintype β] (ℓ : Layout P) :
    restrict (fun p ↦ !f p) (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ) = restrict (fun p ↦ !f p) ℓ := by
  simp [restrict_cons, hp, hq]

end Layout

namespace PartyChain

/-! ### The selected and complementary parts -/

/-- The selected part of a monomial that uses only selected parties: the selected parts of its
words, with its pair effects. -/
def selectedPart (f : P → Bool) : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    M.UsesOnly {p | f p = true} → PartyChain (Layout.restrict f ℓX) (Layout.restrict f ℓY)
  | _, _, final w, h => final (w.selectedPart f (w.sources_selected_of_usesOnly h))
  | _, _, effect hpq α β ℓS w η rest, h =>
      effect hpq α β (Layout.restrict f ℓS)
        ((w.selectedPart f (w.sources_selected_of_usesOnly h.2.2.1)).castLayouts rfl
          (Layout.restrict_pair h.1 h.2.1 α β ℓS))
        η (selectedPart f rest h.2.2.2)

/-- The complementary part of a monomial that uses only selected parties: the composition of
the complementary parts of its words. -/
def complementPart (f : P → Bool) : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    M.UsesOnly {p | f p = true} →
      Word (Layout.restrict (fun p ↦ !f p) ℓX) (Layout.restrict (fun p ↦ !f p) ℓY)
  | _, _, final w, h => w.complementPart f (w.sources_selected_of_usesOnly h)
  | _, _, effect _ α β ℓS w _ rest, h =>
      .comp ((w.complementPart f (w.sources_selected_of_usesOnly h.2.2.1)).castLayouts rfl
          (Layout.restrict_not_pair h.1 h.2.1 α β ℓS))
        (complementPart f rest h.2.2.2)

theorem isAllowed_selectedPart (f : P → Bool) {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY)
    (h : M.UsesOnly {p | f p = true}) (hM : M.IsAllowed) : (M.selectedPart f h).IsAllowed := by
  induction M with
  | final w => exact w.isAllowed_selectedPart f _ hM
  | effect hpq α β ℓS w η rest ih =>
      exact ⟨(Word.isAllowed_castLayouts _ _ _).2 (w.isAllowed_selectedPart f _ hM.1), hM.2.1,
        ih h.2.2.2 hM.2.2⟩

@[simp] theorem effectCount_selectedPart (f : P → Bool) {ℓX ℓY : Layout P}
    (M : PartyChain ℓX ℓY) (h : M.UsesOnly {p | f p = true}) :
    (M.selectedPart f h).toEffectChain.effectCount = M.toEffectChain.effectCount := by
  induction M with
  | final w => rfl
  | effect hpq α β ℓS w η rest ih =>
      simp only [selectedPart, toEffectChain, EffectChain.effectCount] at ih ⊢
      rw [ih]

private theorem mapL_memCongr_apply_of_heq {X₁ Y₁ X₂ Y₂ : Layout P} {E F : HSpace}
    (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) (A : Mem Y₁ →L[ℂ] E) (B : Mem Y₂ →L[ℂ] F)
    {u : Mem X₁ ⊗[ℂ] Mem X₂} {u₁ : Mem Y₁} {u₂ : Mem Y₂} (hu : HEq u (u₁ ⊗ₜ[ℂ] u₂)) :
    TensorProduct.mapL (A ∘L isoL (Layout.memCongr h₁)) (B ∘L isoL (Layout.memCongr h₂)) u =
      A u₁ ⊗ₜ B u₂ := by
  cases h₁
  cases h₂
  cases hu
  rfl

/-- A pair effect on two selected registers acts on the selected factor of the partition. -/
private theorem partitionIso_effect {f : P → Bool} {p q : P} (hp : f p = true) (hq : f q = true)
    (α β : Type) [Fintype α] [Fintype β] (η : EuclideanSpace ℂ (α × β)) (ℓ : Layout P) :
    isoL (Layout.partitionIso f ℓ) ∘L effectMap η (Mem ℓ) ∘L
        isoL (pairHeadIso (p := p) (q := q) ℓ) =
      TensorProduct.mapL
        ((effectMap η (Mem (Layout.restrict f ℓ)) ∘L
          isoL (pairHeadIso (p := p) (q := q) (Layout.restrict f ℓ))) ∘L
            isoL (Layout.memCongr (Layout.restrict_pair hp hq α β ℓ)))
        (ContinuousLinearMap.id ℂ _ ∘L
          isoL (Layout.memCongr (Layout.restrict_not_pair hp hq α β ℓ)))
        ∘L isoL (Layout.partitionIso f (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) := by
  apply clm_ext_tmul₃
  intro x y s
  obtain ⟨z, rfl⟩ := (Layout.partitionIso f ℓ).symm.surjective s
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
  | tmul a b =>
      simp only [comp_apply, isoL_apply]
      rw [mapL_memCongr_apply_of_heq (Layout.restrict_pair hp hq α β ℓ)
        (Layout.restrict_not_pair hp hq α β ℓ) _ _
        (Layout.partitionIso_cons_cons_true_true_tmul f _ _ ℓ hp hq x y a b)]
      rw [comp_apply, isoL_apply, id_apply]
      erw [pairHeadIso_tmul, pairHeadIso_tmul]
      rw [effectMap_tmul, effectMap_tmul, map_smul, LinearIsometryEquiv.apply_symm_apply,
        TensorProduct.smul_tmul']

/-- **Factorization of a monomial using selected parties.** In the canonical partition of the
registers, a monomial that uses only selected parties acts as the tensor product of its selected
part and its complementary part.
Polynomial-PEPS manuscript, `eq:compression-source-gate`, `04-compression.tex`,
lines 233–251. -/
theorem partitionIso_eval (f : P → Bool) {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY)
    (h : M.UsesOnly {p | f p = true}) :
    isoL (Layout.partitionIso f ℓY) ∘L M.toEffectChain.eval =
      TensorProduct.mapL (M.selectedPart f h).toEffectChain.eval (M.complementPart f h).eval ∘L
        isoL (Layout.partitionIso f ℓX) := by
  induction M with
  | final w => exact w.partitionIso_eval_of_usesOnly f h
  | effect hpq α β ℓS w η rest ih =>
      have hw := w.partitionIso_eval_of_usesOnly f h.2.2.1
      have he := partitionIso_effect (f := f) h.1 h.2.1 α β η ℓS
      simp only [toEffectChain, EffectChain.eval, selectedPart, complementPart,
        Word.eval_castLayouts, Word.eval_comp]
      calc isoL (Layout.partitionIso f _) ∘L rest.toEffectChain.eval ∘L effectMap η (Mem ℓS) ∘L
            isoL (pairHeadIso ℓS) ∘L w.eval
          = TensorProduct.mapL (rest.selectedPart f h.2.2.2).toEffectChain.eval
              (rest.complementPart f h.2.2.2).eval ∘L
              ((isoL (Layout.partitionIso f ℓS) ∘L effectMap η (Mem ℓS) ∘L
                isoL (pairHeadIso ℓS)) ∘L w.eval) := by
            rw [← comp_assoc, ih h.2.2.2]
            simp only [comp_assoc]
        _ = _ := by
            rw [he]
            simp only [comp_assoc]
            rw [hw]
            simp only [← comp_assoc, ← TensorProduct.mapL_comp]
            rfl

/-! ### Relabelling the owners -/

/-- Relabel the owners of a monomial whose pair effects keep distinct endpoint labels. Pair
sources whose endpoints receive the same label become local preparations (`Word.mapOwner`). -/
def mapOwner {Q : Type} (g : P → Q) : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (∀ e ∈ M.effectParties, g e.1 ≠ g e.2) →
      PartyChain (Layout.mapOwner g ℓX) (Layout.mapOwner g ℓY)
  | _, _, final w, _ => final (w.mapOwner g)
  | _, _, effect (p := p) (q := q) _ α β ℓS w η rest, h =>
      effect (h (p, q) List.mem_cons_self) α β (Layout.mapOwner g ℓS) (w.mapOwner g) η
        (mapOwner g rest fun e he => h e (List.mem_cons_of_mem _ he))

theorem isAllowed_mapOwner {Q : Type} (g : P → Q) {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY)
    (h : ∀ e ∈ M.effectParties, g e.1 ≠ g e.2) (hM : M.IsAllowed) :
    (M.mapOwner g h).IsAllowed := by
  induction M with
  | final w => exact w.isAllowed_mapOwner g hM
  | effect hpq α β ℓS w η rest ih =>
      exact ⟨w.isAllowed_mapOwner g hM.1, hM.2.1, ih _ hM.2.2⟩

@[simp] theorem effectCount_mapOwner {Q : Type} (g : P → Q) {ℓX ℓY : Layout P}
    (M : PartyChain ℓX ℓY) (h : ∀ e ∈ M.effectParties, g e.1 ≠ g e.2) :
    (M.mapOwner g h).toEffectChain.effectCount = M.toEffectChain.effectCount := by
  induction M with
  | final w => rfl
  | effect hpq α β ℓS w η rest ih =>
      simp only [mapOwner, toEffectChain, EffectChain.effectCount] at ih ⊢
      rw [ih]

/-- Relabelling owners intertwines the operators by the canonical identifications. -/
theorem eval_mapOwner {Q : Type} (g : P → Q) {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY)
    (h : ∀ e ∈ M.effectParties, g e.1 ≠ g e.2) :
    (M.mapOwner g h).toEffectChain.eval ∘L isoL (Layout.mapOwnerIso g ℓX) =
      isoL (Layout.mapOwnerIso g ℓY) ∘L M.toEffectChain.eval := by
  induction M with
  | final w => exact w.eval_mapOwner_comp g
  | @effect ℓX ℓY p q hpq α β _ _ ℓS w η rest ih =>
      have he : effectMap η (Mem (Layout.mapOwner g ℓS)) ∘L
            isoL (pairHeadIso (p := g p) (q := g q) (Layout.mapOwner g ℓS)) ∘L
              isoL (Layout.mapOwnerIso g (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓS)) =
          isoL (Layout.mapOwnerIso g ℓS) ∘L effectMap η (Mem ℓS) ∘L
            isoL (pairHeadIso (p := p) (q := q) ℓS) := by
        apply clm_ext_tmul₃
        intro x y s
        simp only [comp_apply, isoL_apply]
        rw [Layout.mapOwnerIso_cons_tmul, Layout.mapOwnerIso_cons_tmul]
        erw [pairHeadIso_tmul, pairHeadIso_tmul]
        rw [effectMap_tmul, effectMap_tmul, map_smul]
      have he' := congrArg (fun T => T ∘L w.eval) he
      have ih' := congrArg
        (fun T => T ∘L (effectMap η (Mem ℓS) ∘L isoL (pairHeadIso (p := p) (q := q) ℓS) ∘L
          w.eval)) (ih fun e he => h e (List.mem_cons_of_mem _ he))
      simp only [mapOwner, toEffectChain, EffectChain.eval]
      simp only [comp_assoc] at he' ih' ⊢
      rw [w.eval_mapOwner_comp g, he', ih']

end PartyChain

end TNLean.PEPS.PairEffect
