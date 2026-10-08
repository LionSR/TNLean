/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceGrouping

/-!
# One-dimensional sources for unused pairs

The normalized vector `1 ⊗ 1` on two scalar registers can be prepared and then
removed by local contractions at its two endpoint parties. This leaves every
other register unchanged. Consequently, adding such a source to an inventory
does not change the operator obtained after its removal.

Source: polynomial-PEPS manuscript (September 24, 2026),
`eq:compression-source-gate`, `04-compression.tex`, lines 233–251, especially
the one-dimensional sources for unused pairs at lines 243–245.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-- The normalized scalar source on an otherwise unused pair of parties.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
def PairSource.unit (p q : P) (hpq : p ≠ q) : PairSource P :=
  ⟨p, q, hpq, HSpace.of ℂ, HSpace.of ℂ, (1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)⟩

/-- The added scalar source belongs to its prescribed unordered pair. -/
@[simp] theorem PairSource.partyPair_unit (p q : P) (hpq : p ≠ q) :
    (PairSource.unit p q hpq).partyPair = s(p, q) := rfl

/-- The scalar pair vector has norm one.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
@[simp] theorem PairSource.norm_unit_vector (p q : P) (hpq : p ≠ q) :
    ‖(PairSource.unit p q hpq).vector‖ = 1 := by
  exact (TensorProduct.norm_tmul (1 : ℂ) (1 : ℂ)).trans (by simp)

/-- Both halves of the added source have complex dimension one.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
theorem PairSource.finrank_unit_spaces (p q : P) (hpq : p ≠ q) :
    Module.finrank ℂ (PairSource.unit p q hpq).leftSpace = 1 ∧
      Module.finrank ℂ (PairSource.unit p q hpq).rightSpace = 1 := by
  exact ⟨Module.finrank_self ℂ, Module.finrank_self ℂ⟩

/-- Remove a scalar register by the local identification `ℂ ⊗ ℂ ≃ ℂ`. -/
private def eraseUnit (p : P) (ℓ : Layout P) :
    Word (⟨p, HSpace.of ℂ⟩ :: ℓ) ℓ :=
  .localMap p (ℓ₁ := [⟨p, HSpace.of ℂ⟩]) (ℓ₂ := [])
    (by simp) (by simp) (isoL (TensorProduct.lidIsometry ℂ ℂ)) ℓ

/-- A scalar register in the vector `1` can be removed without changing its spectators. -/
private theorem eval_eraseUnit (p : P) (ℓ : Layout P) (x : Mem ℓ) :
    (eraseUnit p ℓ).eval ((1 : ℂ) ⊗ₜ x) = x := by
  simp [eraseUnit, Word.eval, appendIso]

/-- Remove the two scalar registers by local isometries at their owners.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
def Word.eraseUnitPair (p q : P) (ℓ : Layout P) :
    Word (⟨p, HSpace.of ℂ⟩ :: ⟨q, HSpace.of ℂ⟩ :: ℓ) ℓ :=
  .comp (eraseUnit p (⟨q, HSpace.of ℂ⟩ :: ℓ)) (eraseUnit q ℓ)

/-- Removing a scalar pair uses only allowed local maps and exactly undoes its preparation.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
theorem Word.eraseUnitPair_spec (p q : P) (hpq : p ≠ q) (ℓ : Layout P) :
    (Word.eraseUnitPair p q ℓ).IsAllowed ∧
      (Word.eraseUnitPair p q ℓ).sources = [] ∧
      (Word.eraseUnitPair p q ℓ).eval ∘L
        (Word.source hpq (HSpace.of ℂ) (HSpace.of ℂ)
          (PairSource.unit p q hpq).vector ℓ).eval = ContinuousLinearMap.id ℂ (Mem ℓ) := by
  refine ⟨⟨LinearIsometry.norm_toContinuousLinearMap_le _,
    LinearIsometry.norm_toContinuousLinearMap_le _⟩, rfl, ?_⟩
  ext x
  change (eraseUnit q ℓ).eval
    ((eraseUnit p (⟨q, HSpace.of ℂ⟩ :: ℓ)).eval ((1 : ℂ) ⊗ₜ ((1 : ℂ) ⊗ₜ x))) = x
  rw [eval_eraseUnit, eval_eraseUnit]

/-- Adding a scalar source before an inventory can be undone by allowed operations
containing no pair sources, uniformly over all spectator registers.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
theorem SourceInventory.Expands.unit_cons (p q : P) (hpq : p ≠ q)
    (S : SourceInventory P) : SourceInventory.Expands (PairSource.unit p q hpq :: S) S := by
  intro ℓ
  obtain ⟨ha, hs, he⟩ := Word.eraseUnitPair_spec p q hpq (S.layout ++ ℓ)
  refine ⟨Word.eraseUnitPair p q (S.layout ++ ℓ), ha, hs, ?_⟩
  change (Word.eraseUnitPair p q (S.layout ++ ℓ)).eval ∘L
    ((Word.source hpq (HSpace.of ℂ) (HSpace.of ℂ)
      (PairSource.unit p q hpq).vector (S.layout ++ ℓ)).eval ∘L (S.prepare ℓ).eval) = _
  rw [← comp_assoc, he, id_comp]

end TNLean.PEPS.PairEffect
