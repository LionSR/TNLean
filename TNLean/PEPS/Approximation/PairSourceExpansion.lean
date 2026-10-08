/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyLayout

/-!
# Expanding a tensor product of two pair sources

The tensor product of two sources on the same pair of parties can be prepared
as one pair source. Local isometries then separate each party's two registers,
and one exchange restores their original order.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127.
The proof is independent of the source vectors and imposes no rank bound.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
lem:effects.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open ContinuousLinearMap

variable {P : Type}

/-- Split the registers of a combined pair source by local isometries, then restore
alternating party order. Source: polynomial-PEPS Lemma 5.1,
`04-compression.tex`, lines 125–127. -/
def expandCombinedPair (p q : P) (U V U' V' : HSpace) (ℓ : Layout P) :
    Word (⟨p, HSpace.of (U ⊗[ℂ] U')⟩ :: ⟨q, HSpace.of (V ⊗[ℂ] V')⟩ :: ℓ)
      (⟨p, U⟩ :: ⟨q, V⟩ :: ⟨p, U'⟩ :: ⟨q, V'⟩ :: ℓ) :=
  .comp (.localMap p (ℓ₁ := [⟨p, HSpace.of (U ⊗[ℂ] U')⟩])
    (ℓ₂ := [⟨p, U⟩, ⟨p, U'⟩]) (by simp) (by simp)
    (isoL (mergeIso p U U').symm) (⟨q, HSpace.of (V ⊗[ℂ] V')⟩ :: ℓ)) <|
    .comp (.frame _ (.frame _ (.localMap q
      (ℓ₁ := [⟨q, HSpace.of (V ⊗[ℂ] V')⟩]) (ℓ₂ := [⟨q, V⟩, ⟨q, V'⟩])
      (by simp) (by simp) (isoL (mergeIso q V V').symm) ℓ))) <|
      .frame _ (.swap _ _ _)

/-- The expansion uses only local isometries and exchanges. -/
theorem isAllowed_expandCombinedPair (p q : P) (U V U' V' : HSpace) (ℓ : Layout P) :
    (expandCombinedPair p q U V U' V' ℓ).IsAllowed :=
  ⟨LinearIsometry.norm_toContinuousLinearMap_le _,
    LinearIsometry.norm_toContinuousLinearMap_le _, trivial⟩

/-- Expanding the regrouped tensor product recovers the two original pair sources.
Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 125–127. -/
theorem eval_expandCombinedPair {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace)
    (η : U ⊗[ℂ] V) (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    (expandCombinedPair p q U V U' V' ℓ).eval ∘L
        (Word.source hpq _ _ (pairRegroup U V U' V' (η ⊗ₜ η')) ℓ).eval =
      (Word.comp (Word.source hpq U' V' η' ℓ) (Word.source hpq U V η _)).eval := by
  ext1 x
  induction η using TensorProduct.inductionOn with
  | add a b ha hb =>
      simp only [Word.eval_comp, Word.eval_source, comp_apply, appendLeft_apply,
        TensorProduct.add_tmul, map_add] at ha hb ⊢
      exact congrArg₂ (· + ·) ha hb
  | tmul u v =>
      induction η' using TensorProduct.inductionOn with
      | add a b ha hb =>
          simp only [Word.eval_comp, Word.eval_source, comp_apply, appendLeft_apply,
            TensorProduct.tmul_add, TensorProduct.add_tmul, map_add] at ha hb ⊢
          exact congrArg₂ (· + ·) ha hb
      | tmul u' v' =>
          simp [expandCombinedPair, Word.eval, appendIso, mergeIso, pairRegroup_tmul,
            TensorProduct.assoc_symm_tmul, TensorProduct.lid_symm_apply,
            LinearIsometryEquiv.symm_lTensor]

/-- Reversing the two endpoint spaces and exchanging the resulting registers gives
exactly the original source. Source: polynomial-PEPS Lemma 5.1,
`04-compression.tex`, lines 68–70 and 125–127. -/
theorem eval_swap_reversedSource {p q : P} (hpq : p ≠ q) (U V : HSpace)
    (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    (Word.swap ⟨q, V⟩ ⟨p, U⟩ ℓ).eval ∘L
        (Word.source hpq.symm V U ((TensorProduct.commIsometry ℂ U V) η) ℓ).eval =
      (Word.source hpq U V η ℓ).eval := by
  ext1 x
  refine DFunLike.congr_fun
    (f := leftCommL V U (Mem ℓ) ∘L assocL V U (Mem ℓ) ∘L
      appendRight x ∘L isoL (TensorProduct.commIsometry ℂ U V))
    (g := assocL U V (Mem ℓ) ∘L appendRight x)
    (clm_ext_tmul fun u v ↦ ?_) η
  simp only [comp_apply, isoL_apply, TensorProduct.commIsometry_apply,
    TensorProduct.comm_tmul, appendRight_apply, assocL_tmul, leftCommL_tmul]

end TNLean.PEPS.PairEffect
