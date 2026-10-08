/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparation

/-!
# Pair vectors prepared at one party

When both endpoints of a pair belong to the same side of a partition, the pair
is prepared by one local operation on that side. Its vector and its action on
all spectator registers are unchanged.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, internal source preparations, lines 409–417.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

variable {P : Type}

/-- Prepare both halves of a pair vector at one owner as a local operation.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
def localPairSource (p : P) (U V : HSpace) (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    Word ℓ (⟨p, U⟩ :: ⟨p, V⟩ :: ℓ) :=
  .localMap p (ℓ₁ := []) (ℓ₂ := [⟨p, U⟩, ⟨p, V⟩])
    (by simp) (by simp) (assocL U V ℂ ∘L appendLeft η) ℓ

/-- A normalized internal pair is prepared by an allowed operation containing
no pair source between distinct parties. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
theorem localPairSource_spec (p : P) (U V : HSpace) (η : U ⊗[ℂ] V)
    (hη : ‖η‖ = 1) (ℓ : Layout P) :
    (localPairSource p U V η ℓ).IsAllowed ∧ (localPairSource p U V η ℓ).sources = [] := by
  refine ⟨?_, rfl⟩
  exact norm_comp_le_one norm_assocL_le ((norm_appendLeft_le η).trans hη.le)

/-- The local preparation tensors the given pair vector with the unchanged
spectator input. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem eval_localPairSource (p : P) (U V : HSpace) (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    (localPairSource p U V η ℓ).eval = assocL U V (Mem ℓ) ∘L appendLeft η := by
  ext x
  induction η using TensorProduct.inductionOn with
  | add η ζ hη hζ =>
    simp only [localPairSource, eval, appendIso, comp_apply, appendLeft, map_add,
      comp_add, rTensor_add, add_apply] at hη hζ ⊢
    exact congrArg₂ (· + ·) hη hζ
  | tmul u v =>
    simp [localPairSource, eval, appendIso, appendLeft_apply, assocL_tmul,
      LinearIsometryEquiv.symm_lTensor]

end TNLean.PEPS.PairEffect.Word
