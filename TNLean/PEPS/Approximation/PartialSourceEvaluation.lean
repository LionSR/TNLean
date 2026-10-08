/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedSourceComposition

/-!
# Evaluation of the partial source expansion

Expanding precisely the gates that meet the affected parties preserves the full
chronological operator. The coefficient of a choice is the product of the
original complex gate coefficients. Gates supported outside the affected parties
remain as aggregate contractions on the exterior memory.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 351–417.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word
variable {P ι : Type} [Fintype ι]
/-- Extending a weighted operator sum beside spectators retains each complex coefficient.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem eval_sum_appendTail {a b : Layout P} (c : ι → ℂ) (w : ι → Word a b)
    (tail : Layout P) :
    (∑ ξ, c ξ • ((w ξ).appendTail tail).eval) =
      isoL (appendIso b tail).symm ∘L (∑ ξ, c ξ • (w ξ).eval).rTensor (Mem tail) ∘L
        isoL (appendIso a tail) := by
  classical
  suffices h : (∑ ξ, c ξ • ((w ξ).appendTail tail).eval) ∘L
      isoL (appendIso a tail).symm =
        isoL (appendIso b tail).symm ∘L (∑ ξ, c ξ • (w ξ).eval).rTensor (Mem tail) by
    ext x
    simpa only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply] using
      DFunLike.congr_fun h (appendIso a tail x)
  apply clm_ext_tmul
  intro x y
  simp only [comp_apply, sum_apply, smul_apply, isoL_apply, rTensor_tmul]
  have he (ξ : ι) : ((w ξ).appendTail tail).eval
      ((appendIso a tail).symm (x ⊗ₜ y)) =
        (appendIso b tail).symm ((w ξ).eval x ⊗ₜ y) :=
    DFunLike.congr_fun (eval_appendTail (w ξ) tail) (x ⊗ₜ y)
  simp_rw [he]
  simp [TensorProduct.sum_tmul, TensorProduct.smul_tmul]
end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P C ι : Type} [Fintype C] [Fintype ι]
/-- Partial expansion of a placed gate preserves its complete weighted operator.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem eval_partial_gate (A : P → Bool) (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P) :
    (∑ ξ : Choices A (.gate owner G tail),
      coefficient A (.gate owner G tail) ξ • (partialWord A (.gate owner G tail) ξ).eval) ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) (Layout.mapOwner owner a ++ tail)) =
      isoL (Layout.mapOwnerIso (affectedOwner A) (Layout.mapOwner owner b ++ tail)) ∘L
        (SourceCircuit.gate owner G tail).eval := by
  classical
  by_cases h : ∃ p : C, A (owner p) = true
  · let e : Choices A (.gate owner G tail) ≃ ι := Equiv.cast (by simp [Choices, h])
    have hs : (∑ ξ : Choices A (.gate owner G tail),
        coefficient A (.gate owner G tail) ξ • (partialWord A (.gate owner G tail) ξ).eval) =
        ∑ i : ι, c i • ((((G.branchWord i).mapOwner owner).appendTail tail).mapOwner
          (affectedOwner A)).eval := by
      apply Fintype.sum_equiv e
      intro ξ
      simp only [coefficient, partialWord, dite_eq_left h]
      rfl
    rw [hs, Word.eval_sum_mapOwner_comp, Word.eval_sum_appendTail,
      ← G.evalAtOwners_eq_sum owner]
    rfl
  · have hExt (l : Layout C) : ∀ r ∈ Layout.mapOwner owner l,
        affectedOwner A r.owner = none := by
      rintro r hr
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
      exact (affectedOwner_eq_none A _).mpr
        (Bool.eq_false_iff.mpr (fun hp ↦ h ⟨s.owner, hp⟩))
    let e : Choices A (.gate owner G tail) ≃ Unit := Equiv.cast (by simp [Choices, h])
    let T := (Word.groupedBlockMap (affectedOwner A) none
      (Layout.mapOwner owner a) (Layout.mapOwner owner b) (hExt a) (hExt b)
      (G.evalAtOwners owner) tail).eval
    have hs : (∑ ξ : Choices A (.gate owner G tail),
        coefficient A (.gate owner G tail) ξ • (partialWord A (.gate owner G tail) ξ).eval) =
        T := by
      calc
        _ = ∑ _ : Unit, T := by
          apply Fintype.sum_equiv e
          intro ξ
          simp only [coefficient, partialWord, dite_eq_right h, one_smul]
          rfl
        _ = T := by simp
    rw [hs]
    exact Word.eval_groupedBlockMap (affectedOwner A) none _ _ (hExt a) (hExt b)
      (G.evalAtOwners owner) tail
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}
/-- The weighted sum of the partially expanded chronological operators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def expandedEval (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    Mem (Layout.mapOwner (affectedOwner A) a) →L[ℂ]
      Mem (Layout.mapOwner (affectedOwner A) b) :=
  ∑ ξ, coefficient A w ξ • (partialWord A w ξ).eval

/-- Independent choices at successive gate occurrences multiply their coefficients.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem expandedEval_comp (A : P → Bool) {a b d : Layout P}
    (w : SourceCircuit a b) (v : SourceCircuit b d) :
    expandedEval A (.comp w v) = expandedEval A v ∘L expandedEval A w := by
  classical
  change (∑ ξ : Choices A w × Choices A v,
    (coefficient A w ξ.1 * coefficient A v ξ.2) •
      ((partialWord A v ξ.2).eval ∘L (partialWord A w ξ.1).eval)) =
    (∑ ξ : Choices A v, coefficient A v ξ • (partialWord A v ξ).eval) ∘L
      (∑ ξ : Choices A w, coefficient A w ξ • (partialWord A w ξ).eval)
  simp only [Fintype.sum_prod_type, finsetSum_comp, comp_finsetSum,
    smul_comp, comp_smul, Finset.smul_sum, smul_smul]


/-- A spectator register is unaffected by the partial expansion.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem expandedEval_frame (A : P → Bool) {a b : Layout P}
    (r : Reg P) (w : SourceCircuit a b) :
    expandedEval A (.frame r w) = (expandedEval A w).lTensor r.space := by
  change (∑ ξ : Choices A w,
    coefficient A w ξ • ((partialWord A w ξ).eval.lTensor r.space)) =
      (∑ ξ : Choices A w, coefficient A w ξ • (partialWord A w ξ).eval).lTensor r.space
  apply clm_ext_tmul
  intro x y
  simp only [sum_apply, smul_apply, lTensor_tmul,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul]


/-- Partial expansion preserves the complete chronological operator after identifying
all unaffected parties with one exterior owner. No norm hypothesis is needed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem expandedEval_mapOwner (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    expandedEval A w ∘L isoL (Layout.mapOwnerIso (affectedOwner A) a) =
      isoL (Layout.mapOwnerIso (affectedOwner A) b) ∘L w.eval := by
  classical
  induction w with
  | id a =>
      change (∑ _ : Unit, (1 : ℂ) • (Word.id (Layout.mapOwner (affectedOwner A) a)).eval) ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a) =
          isoL (Layout.mapOwnerIso (affectedOwner A) a) ∘L (Word.id a).eval
      simp only [Fintype.sum_unique, one_smul, Word.eval, id_comp, comp_id]
  | comp w v ihw ihv =>
      rw [expandedEval_comp, comp_assoc, ihw, ← comp_assoc, ihv, comp_assoc]
      rfl
  | localMap p ha hb T tail =>
      change (∑ _ : Unit, (1 : ℂ) •
        ((Word.localMap p ha hb T tail).mapOwner (affectedOwner A)).eval) ∘L _ = _
      simpa only [Fintype.sum_unique, one_smul, eval] using
        Word.eval_mapOwner_comp (affectedOwner A) (Word.localMap p ha hb T tail)
  | @gate C ι _ _ owner a b c G tail => exact eval_partial_gate A owner G tail
  | swap r t tail =>
      change (∑ _ : Unit, (1 : ℂ) •
        ((Word.swap r t tail).mapOwner (affectedOwner A)).eval) ∘L _ = _
      simpa only [Fintype.sum_unique, one_smul, eval] using
        Word.eval_mapOwner_comp (affectedOwner A) (Word.swap r t tail)
  | @frame r a b w ih =>
      rw [expandedEval_frame]
      apply clm_ext_tmul
      intro x y
      change x ⊗ₜ expandedEval A w (Layout.mapOwnerIso (affectedOwner A) a y) =
        x ⊗ₜ Layout.mapOwnerIso (affectedOwner A) b (w.eval y)
      exact congrArg (fun z ↦ x ⊗ₜ z) (DFunLike.congr_fun ih y)

end TNLean.PEPS.PairEffect.SourceCircuit
