/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.FrontRegisters
import TNLean.Lattice.PartyCircuit.PartyFactorization
import TNLean.Lattice.PartyCircuit.SourcePreparation

/-!
# Restricting a word to the parties it uses

`Word.restrict` restricts a word without pair sources to any selection of parties
(`TNLean.PEPS.Approximation.WordRestriction`), and `Word.partitionIso_eval` factors the word
into its selected and complementary restrictions. This file extends both to a word whose pair
sources join selected parties only, which is the case for every word that uses only selected
parties (`Word.UsesOnly`). The pair sources are prepared first (`Word.localPart`), the
source-free remainder is restricted as before, and the prepared registers join the selected
part.

* `Word.selectedPart` prepares the pair sources and applies the selected restriction of the
  remainder; `Word.complementPart` is the complementary restriction of the remainder.
* `Word.partitionIso_eval_of_usesOnly`: in the canonical partition of the registers, the word
  acts as the tensor product of the two parts.
* `Layout.partitionWord` reorders a layout into its selected registers followed by the others,
  by exchanges of tensor factors only.

This is how a bounded change that uses a fixed list of parties acts on the registers of these
parties alone, so that it is a gate of the protocol whose participants are these parties
(`06-geometry.tex`, lines 574–583).

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
  lines 21–43, and the factorization `eq:compression-source-gate`, lines 233–251.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-! ### Pair sources of a word using selected parties -/

namespace Word

/-- Every pair source of a word that uses only selected parties joins two selected parties. -/
theorem sources_selected_of_usesOnly {f : P → Bool} {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hw : w.UsesOnly {p | f p = true}) : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true := by
  induction w with
  | id => simp [sources]
  | comp w w' ih ih' =>
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact ih' hw.2 s hs
      · exact ih hw.1 s hs
  | localMap => simp [sources]
  | source hpq U V η ℓ =>
      intro s hs
      rw [sources, List.mem_singleton] at hs
      subst hs
      exact hw
  | swap => simp [sources]
  | frame r w ih => exact ih hw

end Word

namespace SourceInventory

theorem owner_selected_of_mem_layout {f : P → Bool} {S : SourceInventory P}
    (hS : ∀ s ∈ S, f s.left = true ∧ f s.right = true) : ∀ r ∈ S.layout, f r.owner = true := by
  intro r hr
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
  simp only [PairSource.layout, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hS s hs).1
  · exact (hS s hs).2

theorem restrict_layout_append {f : P → Bool} {S : SourceInventory P}
    (hS : ∀ s ∈ S, f s.left = true ∧ f s.right = true) (ℓ : Layout P) :
    Layout.restrict f (S.layout ++ ℓ) = S.layout ++ Layout.restrict f ℓ := by
  rw [Layout.restrict_append]
  congr 1
  exact List.filter_eq_self.mpr fun r hr => owner_selected_of_mem_layout hS r hr

theorem restrict_not_layout_append {f : P → Bool} {S : SourceInventory P}
    (hS : ∀ s ∈ S, f s.left = true ∧ f s.right = true) (ℓ : Layout P) :
    Layout.restrict (fun p ↦ !f p) (S.layout ++ ℓ) = Layout.restrict (fun p ↦ !f p) ℓ := by
  have h : Layout.restrict (fun p ↦ !f p) S.layout = [] :=
    List.filter_eq_nil_iff.mpr fun r hr => by simp [owner_selected_of_mem_layout hS r hr]
  rw [Layout.restrict_append, h, List.nil_append]

end SourceInventory

/-! ### The selected and complementary parts -/

namespace Word

/-- The selected part of a word whose pair sources join selected parties: prepare the pair
sources, then apply the selected restriction of the source-free remainder.
Polynomial-PEPS manuscript, `eq:compression-source-gate`, `04-compression.tex`,
lines 233–251. -/
def selectedPart (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hS : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true) :
    Word (Layout.restrict f ℓ) (Layout.restrict f ℓ') :=
  .comp (w.sources.prepare (Layout.restrict f ℓ))
    ((w.localPart.restrict f w.sources_localPart).castInput
      (SourceInventory.restrict_layout_append hS ℓ))

/-- The complementary part of a word whose pair sources join selected parties: the
complementary restriction of the source-free remainder.
Polynomial-PEPS manuscript, `eq:compression-source-gate`, `04-compression.tex`,
lines 233–251. -/
def complementPart (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hS : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true) :
    Word (Layout.restrict (fun p ↦ !f p) ℓ) (Layout.restrict (fun p ↦ !f p) ℓ') :=
  (w.localPart.restrict (fun p ↦ !f p) w.sources_localPart).castInput
    (SourceInventory.restrict_not_layout_append hS ℓ)

theorem isAllowed_selectedPart (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hS : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true) (hw : w.IsAllowed) :
    (w.selectedPart f hS).IsAllowed :=
  ⟨(SourceInventory.isAllowed_prepare_iff _ _).2 (w.isNormalized_sources hw),
    (isAllowed_castInput _ _).2 (isAllowed_restrict f _ _ (isAllowed_localPart w hw))⟩

end Word

/-- A layout whose registers are all selected is its own selected part, and the complementary
part is the empty memory. -/
theorem Layout.partitionIso_append_selected_tmul (f : P → Bool) (a ℓ : Layout P)
    (ha : ∀ r ∈ a, f r.owner = true)
    (s : Mem a) (x : Mem (Layout.restrict f ℓ)) (y : Mem (Layout.restrict (fun p ↦ !f p) ℓ)) :
    HEq (Layout.partitionIso f (a ++ ℓ)
      ((appendIso a ℓ).symm (s ⊗ₜ[ℂ] (Layout.partitionIso f ℓ).symm (x ⊗ₜ[ℂ] y))))
      ((appendIso a (Layout.restrict f ℓ)).symm (s ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y) := by
  have hself : ∀ {b : Layout P}, (∀ r ∈ b, f r.owner = true) → Layout.restrict f b = b :=
    fun hb => List.filter_eq_self.mpr fun r hr => hb r hr
  have hnil : ∀ {b : Layout P}, (∀ r ∈ b, f r.owner = true) →
      Layout.restrict (fun p ↦ !f p) b = [] :=
    fun hb => List.filter_eq_nil_iff.mpr fun r hr => by simp [hb r hr]
  induction a with
  | nil => simp [appendIso, TensorProduct.smul_tmul]
  | cons r a ih =>
      induction s using TensorProduct.inductionOn with
      | add u v hu hv =>
          simp only [TensorProduct.add_tmul, map_add]
          exact Layout.add_heq
            (A := HSpace.of (Mem (Layout.restrict f ((r :: a) ++ ℓ)) ⊗[ℂ]
              Mem (Layout.restrict (fun p ↦ !f p) ((r :: a) ++ ℓ))))
            (B := HSpace.of (Mem ((r :: a) ++ Layout.restrict f ℓ) ⊗[ℂ]
              Mem (Layout.restrict (fun p ↦ !f p) ℓ)))
            (by rw [Layout.restrict_append, hself ha, Layout.restrict_append, hnil ha,
              List.nil_append]) hu hv
      | tmul u v =>
          rw [appendIso_symm_cons_tmul]
          apply (Layout.partitionIso_cons_true_tmul f r (a ++ ℓ) (ha r (by simp)) u _).trans
          have ha' : ∀ t ∈ a, f t.owner = true := fun t ht ↦ ha t (List.mem_cons_of_mem r ht)
          apply (Layout.selectedHead_heq r
            (by rw [Layout.restrict_append, hself ha'])
            (by rw [Layout.restrict_append, hnil ha', List.nil_append]) u (ih ha' v)).trans
          rfl

private theorem mapL_eval_apply_of_heq {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Layout P} (A : Word X₁ Z₁)
    (B : Word X₂ Z₂) (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) {u : Mem X₁ ⊗[ℂ] Mem X₂} {u₁ : Mem Y₁}
    {u₂ : Mem Y₂} (hu : HEq u (u₁ ⊗ₜ[ℂ] u₂)) :
    TensorProduct.mapL A.eval B.eval u = (A.castInput h₁).eval u₁ ⊗ₜ (B.castInput h₂).eval u₂ := by
  cases h₁
  cases h₂
  cases hu
  rfl

namespace Word

/-- **Factorization of a word using selected parties.** In the canonical partition of the
registers into selected and complementary ones, a word whose pair sources join selected parties
acts as the tensor product of its selected and complementary parts.
Polynomial-PEPS manuscript, `eq:compression-source-gate`, `04-compression.tex`,
lines 233–251. -/
theorem partitionIso_eval_of_sources_selected (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hS : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true) :
    isoL (Layout.partitionIso f ℓ') ∘L w.eval =
      TensorProduct.mapL (w.selectedPart f hS).eval (w.complementPart f hS).eval ∘L
        isoL (Layout.partitionIso f ℓ) := by
  suffices H : (isoL (Layout.partitionIso f ℓ') ∘L w.eval) ∘L isoL (Layout.partitionIso f ℓ).symm =
      (TensorProduct.mapL (w.selectedPart f hS).eval (w.complementPart f hS).eval ∘L
        isoL (Layout.partitionIso f ℓ)) ∘L isoL (Layout.partitionIso f ℓ).symm by
    ext1 x
    simpa using DFunLike.congr_fun H (Layout.partitionIso f ℓ x)
  apply clm_ext_tmul
  intro y z
  have hlp := DFunLike.congr_fun (w.localPart.partitionIso_eval f w.sources_localPart)
    ((w.sources.prepare ℓ).eval ((Layout.partitionIso f ℓ).symm (y ⊗ₜ z)))
  simp only [comp_apply, isoL_apply] at hlp
  simp only [comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply,
    TensorProduct.mapL_tmul]
  rw [← eval_localPart_prepare w, hlp, SourceInventory.eval_prepare_eq_appendIso_symm]
  refine (mapL_eval_apply_of_heq _ _ (SourceInventory.restrict_layout_append hS ℓ)
    (SourceInventory.restrict_not_layout_append hS ℓ)
    (Layout.partitionIso_append_selected_tmul f _ ℓ
      (SourceInventory.owner_selected_of_mem_layout hS) _ y z)).trans ?_
  simp only [selectedPart, complementPart, eval_comp, comp_apply,
    SourceInventory.eval_prepare_eq_appendIso_symm]

/-- The factorization for a word that uses only selected parties. -/
theorem partitionIso_eval_of_usesOnly (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hw : w.UsesOnly {p | f p = true}) :
    isoL (Layout.partitionIso f ℓ') ∘L w.eval =
      TensorProduct.mapL (w.selectedPart f (w.sources_selected_of_usesOnly hw)).eval
        (w.complementPart f (w.sources_selected_of_usesOnly hw)).eval ∘L
        isoL (Layout.partitionIso f ℓ) :=
  w.partitionIso_eval_of_sources_selected f _

end Word

end TNLean.PEPS.PairEffect
