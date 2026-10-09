/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord

/-!
# Combining pair sources

Two pair sources `η` and `η'` prepared one after the other on the same pair of parties,
followed by merging the two registers of each party into one, are a single pair source of the
regrouped vector `η ⊗ η'`, whose norm is `‖η‖ ‖η'‖` (`eval_combineSources`).  This is the
tensor-product identity that the proof of Lemma 5.1 `lem:effects` gives for its last clause.
The use of this identity in Lemma 5.1, and what of that clause is formalized, are described in
`TNLean.PEPS.Approximation.PartyLayout`.

## Main definitions

* `PairEffect.pairRegroup` : the regrouping `(U ⊗ V) ⊗ (U' ⊗ V') ≅ (U ⊗ U') ⊗ (V ⊗ V')`.
* `PairEffect.combineSources` : two pair sources followed by merging the registers of each
  party.

## Main results

* `PairEffect.eval_combineSources` : two adjacent sources on one pair of parties combine into
  one.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 68–70 and 125–127.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open ContinuousLinearMap

variable {P : Type}

/-- The regrouping `(U ⊗ V) ⊗ (U' ⊗ V') ≅ (U ⊗ U') ⊗ (V ⊗ V')` of two pair vectors on the same
pair of parties. -/
def pairRegroup (U V U' V' : HSpace) :
    (U ⊗[ℂ] V) ⊗[ℂ] (U' ⊗[ℂ] V') ≃ₗᵢ[ℂ] (U ⊗[ℂ] U') ⊗[ℂ] (V ⊗[ℂ] V') :=
  (TensorProduct.assocIsometry ℂ U V (U' ⊗[ℂ] V')).trans <|
    ((((TensorProduct.assocIsometry ℂ V U' V').symm.trans
      (((TensorProduct.commIsometry ℂ V U').rTensor V').trans
        (TensorProduct.assocIsometry ℂ U' V V'))).lTensor U).trans
      (TensorProduct.assocIsometry ℂ U U' (V ⊗[ℂ] V')).symm)

theorem pairRegroup_tmul (U V U' V' : HSpace) (u : U) (v : V) (u' : U') (v' : V') :
    pairRegroup U V U' V' ((u ⊗ₜ v) ⊗ₜ (u' ⊗ₜ v')) = (u ⊗ₜ u') ⊗ₜ (v ⊗ₜ v') := by
  simp only [pairRegroup, LinearIsometryEquiv.trans_apply, iso_lTensor_apply, iso_rTensor_apply,
    TensorProduct.assocIsometry_apply, TensorProduct.assocIsometry_symm_apply,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, lTensor_tmul, rTensor_tmul,
    isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]

/-- Merging two registers of one party into one register. -/
def mergeIso (p : P) (U U' : HSpace) :
    Mem [⟨p, U⟩, ⟨p, U'⟩] ≃ₗᵢ[ℂ] Mem [⟨p, HSpace.of (U ⊗[ℂ] U')⟩] :=
  (TensorProduct.assocIsometry ℂ U U' ℂ).symm

/-- Merging two registers of one party, on a product vector. -/
private theorem eval_localMap_mergeIso (p : P) (U U' : HSpace)
    (h₁ : ∀ r ∈ [(⟨p, U⟩ : Reg P), ⟨p, U'⟩], r.owner = p)
    (h₂ : ∀ r ∈ [(⟨p, HSpace.of (U ⊗[ℂ] U')⟩ : Reg P)], r.owner = p) (ℓ : Layout P) (u : U)
    (u' : U') (z : Mem ℓ) :
    (Word.localMap p h₁ h₂ (isoL (mergeIso p U U')) ℓ).eval (u ⊗ₜ (u' ⊗ₜ z)) =
      (u ⊗ₜ[ℂ] u' : U ⊗[ℂ] U') ⊗ₜ z := by
  simp [Word.eval, appendIso, mergeIso, TensorProduct.assoc_symm_tmul,
    TensorProduct.lid_symm_apply, LinearIsometryEquiv.symm_lTensor]

/-- Two pair sources on the same pair of parties, followed by merging the two registers of each
party. -/
def combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) (η : U ⊗[ℂ] V)
    (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    Word ℓ (⟨p, HSpace.of (U ⊗[ℂ] U')⟩ :: ⟨q, HSpace.of (V ⊗[ℂ] V')⟩ :: ℓ) :=
  .comp (.source hpq U' V' η' ℓ) <| .comp (.source hpq U V η _) <|
    .comp (.frame _ (.swap _ _ _)) <|
    .comp (.localMap p (ℓ₁ := [⟨p, U⟩, ⟨p, U'⟩]) (ℓ₂ := [⟨p, HSpace.of (U ⊗[ℂ] U')⟩])
      (by simp) (by simp) (isoL (mergeIso p U U')) (⟨q, V⟩ :: ⟨q, V'⟩ :: ℓ)) <|
    .frame _ (.localMap q (ℓ₁ := [⟨q, V⟩, ⟨q, V'⟩]) (ℓ₂ := [⟨q, HSpace.of (V ⊗[ℂ] V')⟩])
      (by simp) (by simp) (isoL (mergeIso q V V')) ℓ)

theorem isAllowed_combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) {η : U ⊗[ℂ] V}
    {η' : U' ⊗[ℂ] V'} (hη : ‖η‖ = 1) (hη' : ‖η'‖ = 1) (ℓ : Layout P) :
    (combineSources hpq U V U' V' η η' ℓ).IsAllowed :=
  ⟨hη', hη, trivial, LinearIsometry.norm_toContinuousLinearMap_le _,
    LinearIsometry.norm_toContinuousLinearMap_le _⟩

/-- **Combining pair sources.** Two pair sources `η` and `η'` on the same pair of parties,
followed by merging the two registers of each party, are the single pair source of the
regrouped vector `η ⊗ η'`, whose norm is `‖η‖ ‖η'‖`.

This is the two-source tensor-product identity behind the last clause of Lemma 5.1. The
combination of all sources on one pair of parties, in any order, is
`PairEffect.partyPairEffectElimination_with_grouped_sources`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
68–70 and 125–127. -/
theorem eval_combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) (η : U ⊗[ℂ] V)
    (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    (combineSources hpq U V U' V' η η' ℓ).eval =
        (Word.source hpq _ _ (pairRegroup U V U' V' (η ⊗ₜ η')) ℓ).eval ∧
      ‖pairRegroup U V U' V' (η ⊗ₜ η')‖ = ‖η‖ * ‖η'‖ := by
  refine ⟨?_, by rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul]⟩
  ext1 x
  simp only [combineSources, Word.eval_comp, Word.eval_frame, Word.eval_source, Word.eval.eq_5,
    comp_apply, appendLeft_apply]
  induction η using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul u v =>
      induction η' using TensorProduct.inductionOn with
      | add a b ha hb =>
          simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]
      | tmul u' v' =>
          simp only [assocL_tmul, leftCommL_tmul, lTensor_tmul, pairRegroup_tmul]
          rw [eval_localMap_mergeIso, lTensor_tmul, eval_localMap_mergeIso]

end TNLean.PEPS.PairEffect
