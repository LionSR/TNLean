/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceGrouping

/-!
# Local maps on the two halves of a pair source

Applying a contraction to each half of a freshly prepared pair source is an allowed
composition. Its operator is the preparation of the source vector transformed by
the tensor product of those contractions. This identity applies to the coordinate
projections from common private source spaces back to one monomial's spaces.

Source: polynomial-PEPS manuscript, September 24, 2026, Theorem 5.2,
`04-compression.tex`, common private slot spaces, lines 253–267.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-commonsource-pairmaps-word.mappair
Downstream declaration: TNLean.PEPS.PairEffect.Word.mapPair

Provenance-ID: 8769-commonsource-pairmaps-word.mappair_spec
Downstream declaration: TNLean.PEPS.PairEffect.Word.mapPair_spec

Provenance-ID: 8769-commonsource-pairmaps-word.eval_mappair_tmul
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_mapPair_tmul

Provenance-ID: 8769-commonsource-pairmaps-word.eval_mappair_source
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_mapPair_source
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-- Apply one map at each endpoint of a pair, leaving the remaining registers untouched.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 253–267. -/
def Word.mapPair (p q : P) {U V U' V' : HSpace}
    (A : U →L[ℂ] U') (B : V →L[ℂ] V') (ℓ : Layout P) :
    Word (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ) (⟨p, U'⟩ :: ⟨q, V'⟩ :: ℓ) :=
  .comp (.localMap p (ℓ₁ := [⟨p, U⟩]) (ℓ₂ := [⟨p, U'⟩])
    (by simp) (by simp) (A.rTensor ℂ) (⟨q, V⟩ :: ℓ))
    (.frame ⟨p, U'⟩ (.localMap q (ℓ₁ := [⟨q, V⟩]) (ℓ₂ := [⟨q, V'⟩])
      (by simp) (by simp) (B.rTensor ℂ) ℓ))

/-- Local contractions give an allowed composition containing no pair sources.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 253–267. -/
theorem Word.mapPair_spec (p q : P) {U V U' V' : HSpace}
    (A : U →L[ℂ] U') (B : V →L[ℂ] V') (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ℓ : Layout P) :
    (Word.mapPair p q A B ℓ).IsAllowed ∧ (Word.mapPair p q A B ℓ).sources = [] :=
  ⟨⟨(norm_rTensor_le _ _).trans hA, (norm_rTensor_le _ _).trans hB⟩, rfl⟩

/-- The two endpoint maps act on their corresponding elementary tensor factors.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 253–267. -/
theorem Word.eval_mapPair_tmul (p q : P) {U V U' V' : HSpace}
    (A : U →L[ℂ] U') (B : V →L[ℂ] V') (ℓ : Layout P)
    (u : U) (v : V) (x : Mem ℓ) :
    (Word.mapPair p q A B ℓ).eval (u ⊗ₜ (v ⊗ₜ x)) = A u ⊗ₜ (B v ⊗ₜ x) := by
  simp [Word.mapPair, Word.eval, appendIso, LinearIsometryEquiv.symm_lTensor]

/-- Applying the endpoint maps after preparation transforms exactly the source vector.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 253–267. -/
theorem Word.eval_mapPair_source {p q : P} (hpq : p ≠ q) {U V U' V' : HSpace}
    (A : U →L[ℂ] U') (B : V →L[ℂ] V') (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    (Word.mapPair p q A B ℓ).eval ∘L (Word.source hpq U V η ℓ).eval =
      (Word.source hpq U' V' (TensorProduct.mapL A B η) ℓ).eval := by
  ext x
  induction η using TensorProduct.inductionOn with
  | add η η' hη hη' =>
      simp only [Word.eval_source, comp_apply, appendLeft_apply, map_add,
        TensorProduct.add_tmul] at hη hη' ⊢
      exact congrArg₂ (· + ·) hη hη'
  | tmul u v =>
      simp only [Word.eval_source, comp_apply, appendLeft_apply, assocL_tmul,
        TensorProduct.mapL_tmul]
      exact Word.eval_mapPair_tmul p q A B ℓ u v x

end TNLean.PEPS.PairEffect
