/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt
import TNLean.PEPS.Approximation.SourceOwnerSupport
import TNLean.PEPS.Approximation.PartialSourceEvaluation

/-!
# Source substitutions and aggregation of untouched gates

Source vectors may be replaced separately at each original occurrence and local
gate label. The circuit order and all remaining operations are unchanged. Gates
whose sources have not been replaced can still be kept in their aggregate form.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-01
Downstream declaration:
TNLean.PEPS.PairEffect.PreparedSourceGate.branchWithSources

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.evalWithSources

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.partialWithSources

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.evalWithSources_original

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-05
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.partialWithSources_original

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-06
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.evalWithSources_eq_sum_partialWithSources

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-07
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.selectedSourceVectors

Provenance-ID: 8769-source-corrections-sourcecircuitsubstitution-08
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.eval_selectedSourceVectors_eq_sum

-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect

namespace PreparedSourceGate

/-- Prepare arbitrary vectors in the gate's fixed slots before its actual remaining word.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 338–355. -/
def branchWithSources {P ι : Type} [Fintype ι] {c : ι → ℂ} {a b : Layout P}
    (G : PreparedSourceGate c a b) (ξ : ι)
    (η : ∀ i, euc (Fin (G.leftDim i)) ⊗[ℂ] euc (Fin (G.rightDim i))) : Word a b :=
  .comp (SourceInventory.prepareSlots G.slots (fun i ↦ euc (Fin (G.leftDim i)))
    (fun i ↦ euc (Fin (G.rightDim i))) η a) (G.remaining ξ)

end PreparedSourceGate

namespace SourceCircuit
variable {P : Type}

/-- Evaluate the actual circuit with occurrence-local source substitutions.
No norm condition is imposed on the substituted vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–355. -/
def evalWithSources : {a b : Layout P} → (w : SourceCircuit a b) →
    (∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2)) →
    Mem a →L[ℂ] Mem b
  | _, _, .id a, _ => .id ℂ (Mem a)
  | _, _, .comp w v, η =>
      evalWithSources v (fun e ξ ↦ η ⟨Sum.inr e.1, e.2⟩ ξ) ∘L
        evalWithSources w (fun e ξ ↦ η ⟨Sum.inl e.1, e.2⟩ ξ)
  | _, _, .localMap p ha hb T tail, _ => (Word.localMap p ha hb T tail).eval
  | _, _, @SourceCircuit.gate _ C _ι _ _ owner a b c G tail, η =>
      ∑ ξ, c ξ • (((G.branchWithSources ξ (fun i ↦ η ⟨(), i⟩ ξ)).mapOwner
        owner).appendTail tail).eval
  | _, _, .swap r s tail, _ => (Word.swap r s tail).eval
  | _, _, .frame r w, η => (evalWithSources w η).lTensor r.space

/-- Substitute vectors in the expanded gates while retaining untouched aggregate gates.
The substituted vectors depend on original source positions and local labels only.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
def partialWithSources (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    (∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2)) →
    Choices A w → Word (Layout.mapOwner (affectedOwner A) a)
      (Layout.mapOwner (affectedOwner A) b)
  | _, _, .id _, _, _ => .id _
  | _, _, .comp w v, η, ξ =>
      .comp (partialWithSources A w (fun e θ ↦ η ⟨Sum.inl e.1, e.2⟩ θ) ξ.1)
        (partialWithSources A v (fun e θ ↦ η ⟨Sum.inr e.1, e.2⟩ θ) ξ.2)
  | _, _, .localMap p ha hb T tail, _, _ =>
      (Word.localMap p ha hb T tail).mapOwner (affectedOwner A)
  | _, _, @SourceCircuit.gate _ C ι _ _ owner a b c G tail, η, ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have i : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact (((G.branchWithSources i (fun j ↦ η ⟨(), j⟩ i)).mapOwner
          owner).appendTail tail).mapOwner (affectedOwner A)
      · exact Word.groupedBlockMap (affectedOwner A) none
          (Layout.mapOwner owner a) (Layout.mapOwner owner b)
          (Layout.affectedOwner_mapOwner_eq_none A owner h a)
          (Layout.affectedOwner_mapOwner_eq_none A owner h b)
          (G.evalAtOwners owner) tail
  | _, _, .swap r s tail, _, _ =>
      (Word.swap r s tail).mapOwner (affectedOwner A)
  | _, _, .frame r w, η, ξ =>
      .frame ⟨affectedOwner A r.owner, r.space⟩ (partialWithSources A w η ξ)

/-- The original source vectors recover the circuit's original operator.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–355. -/
theorem evalWithSources_original {a b : Layout P} (w : SourceCircuit a b) :
    evalWithSources w (sourceVectorAt w) = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      change evalWithSources v (sourceVectorAt v) ∘L
        evalWithSources w (sourceVectorAt w) = v.eval ∘L w.eval
      rw [ihw, ihv]
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      change (∑ ξ, c ξ • (((G.branchWord ξ).mapOwner owner).appendTail tail).eval) = _
      rw [Word.eval_sum_appendTail, ← G.evalAtOwners_eq_sum]
      rfl
  | swap => rfl
  | frame r w ih => exact congrArg (fun T ↦ T.lTensor r.space) ih

/-- Original source vectors recover each actual partial monomial.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem partialWithSources_original (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    partialWithSources A w (sourceVectorAt w) ξ = partialWord A w ξ := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      change Word.comp (partialWithSources A w (sourceVectorAt w) ξ.1)
        (partialWithSources A v (sourceVectorAt v) ξ.2) =
          Word.comp (partialWord A w ξ.1) (partialWord A v ξ.2)
      rw [ihw, ihv]
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · simp only [partialWithSources, partialWord, dite_eq_left h,
          sourceVectorAt, PreparedSourceGate.branchWithSources, PreparedSourceGate.branchWord]
      · simp only [partialWithSources, partialWord, dite_eq_right h]
  | swap => rfl
  | frame r w ih => exact congrArg (Word.frame ⟨affectedOwner A r.owner, r.space⟩) (ih ξ)

private theorem eval_partialWithSources_gate {C ι : Type} [Fintype C] [Fintype ι]
    (A : P → Bool) (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P)
    (η : ∀ e : sourceLocations (.gate owner G tail),
      branchLabels (.gate owner G tail) e.1 →
        euc (Fin (sourceDims (.gate owner G tail) e).1) ⊗[ℂ]
          euc (Fin (sourceDims (.gate owner G tail) e).2))
    (hη : ∀ e ξ, ¬ IsTouched A (.gate owner G tail) e.1 →
      η e ξ = sourceVectorAt (.gate owner G tail) e ξ) :
    (∑ ξ : Choices A (.gate owner G tail),
      coefficient A (.gate owner G tail) ξ •
        (partialWithSources A (.gate owner G tail) η ξ).eval) ∘L
          isoL (Layout.mapOwnerIso (affectedOwner A) (Layout.mapOwner owner a ++ tail)) =
      isoL (Layout.mapOwnerIso (affectedOwner A) (Layout.mapOwner owner b ++ tail)) ∘L
        evalWithSources (.gate owner G tail) η := by
  classical
  by_cases h : ∃ p : C, A (owner p) = true
  · let e : Choices A (.gate owner G tail) ≃ ι := Equiv.cast (by simp [Choices, h])
    have hs : (∑ ξ : Choices A (.gate owner G tail),
        coefficient A (.gate owner G tail) ξ •
          (partialWithSources A (.gate owner G tail) η ξ).eval) =
        ∑ i : ι, c i • ((((G.branchWithSources i (fun j ↦ η ⟨(), j⟩ i)).mapOwner
          owner).appendTail tail).mapOwner (affectedOwner A)).eval := by
      apply Fintype.sum_equiv e
      intro ξ
      simp only [coefficient, partialWithSources, dite_eq_left h]
      rfl
    rw [hs, Word.eval_sum_mapOwner_comp]
    rfl
  · have hηeq : η = sourceVectorAt (.gate owner G tail) := by
      funext e ξ
      apply hη e ξ
      rcases e with ⟨⟨⟩, i⟩
      exact fun ht ↦ h ((isTouched_gate_iff A owner G tail).mp ht)
    subst η
    simpa only [partialWithSources_original, evalWithSources_original] using
      eval_partial_gate A owner G tail

/-- Source substitutions at touched gates commute with summing back every untouched gate.
The hypothesis records exactly that no source at an untouched gate was changed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem evalWithSources_eq_sum_partialWithSources (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hη : ∀ e ξ, ¬ IsTouched A w e.1 → η e ξ = sourceVectorAt w e ξ) :
    (∑ ξ, coefficient A w ξ • (partialWithSources A w η ξ).eval) ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a) =
      isoL (Layout.mapOwnerIso (affectedOwner A) b) ∘L evalWithSources w η := by
  classical
  induction w with
  | id a =>
      change (∑ _ : Unit, (1 : ℂ) • (Word.id (Layout.mapOwner (affectedOwner A) a)).eval) ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a) =
          isoL (Layout.mapOwnerIso (affectedOwner A) a) ∘L (Word.id a).eval
      simp only [Fintype.sum_unique, one_smul, Word.eval, id_comp, comp_id]
  | comp w v ihw ihv =>
      let ηw := fun (e : sourceLocations w) ξ ↦ η ⟨Sum.inl e.1, e.2⟩ ξ
      let ηv := fun (e : sourceLocations v) ξ ↦ η ⟨Sum.inr e.1, e.2⟩ ξ
      have hw := ihw ηw (fun e ξ he ↦ hη ⟨Sum.inl e.1, e.2⟩ ξ he)
      have hv := ihv ηv (fun e ξ he ↦ hη ⟨Sum.inr e.1, e.2⟩ ξ he)
      have hs : (∑ ξ, coefficient A (.comp w v) ξ •
          (partialWithSources A (.comp w v) η ξ).eval) =
          (∑ ξ, coefficient A v ξ • (partialWithSources A v ηv ξ).eval) ∘L
            (∑ ξ, coefficient A w ξ • (partialWithSources A w ηw ξ).eval) := by
        change (∑ ξ : Choices A w × Choices A v,
          (coefficient A w ξ.1 * coefficient A v ξ.2) •
            ((partialWithSources A v ηv ξ.2).eval ∘L
              (partialWithSources A w ηw ξ.1).eval)) = _
        simp only [Fintype.sum_prod_type, finsetSum_comp, comp_finsetSum,
          smul_comp, comp_smul, Finset.smul_sum, smul_smul]
      rw [hs, comp_assoc, hw, ← comp_assoc, hv, comp_assoc]
      rfl
  | localMap p ha hb T tail =>
      change (∑ _ : Unit, (1 : ℂ) •
        ((Word.localMap p ha hb T tail).mapOwner (affectedOwner A)).eval) ∘L _ = _
      simpa only [Fintype.sum_unique, one_smul, evalWithSources] using
        Word.eval_mapOwner_comp (affectedOwner A) (Word.localMap p ha hb T tail)
  | @gate C ι _ _ owner a b c G tail =>
      exact eval_partialWithSources_gate A owner G tail η hη
  | swap r s tail =>
      change (∑ _ : Unit, (1 : ℂ) •
        ((Word.swap r s tail).mapOwner (affectedOwner A)).eval) ∘L _ = _
      simpa only [Fintype.sum_unique, one_smul, evalWithSources] using
        Word.eval_mapOwner_comp (affectedOwner A) (Word.swap r s tail)
  | @frame r a b w ih =>
      apply clm_ext_tmul
      intro x y
      simp only [comp_apply, sum_apply, smul_apply, isoL_apply, partialWithSources,
        Word.eval_frame, coefficient, evalWithSources, lTensor_tmul]
      change (∑ ξ, coefficient A w ξ •
        (x ⊗ₜ[ℂ] (partialWithSources A w η ξ).eval
          (Layout.mapOwnerIso (affectedOwner A) a y))) =
            x ⊗ₜ[ℂ] Layout.mapOwnerIso (affectedOwner A) b (evalWithSources w η y)
      simpa only [comp_apply, sum_apply, smul_apply, isoL_apply,
        TensorProduct.tmul_sum, TensorProduct.tmul_smul] using
        congrArg (fun z ↦ x ⊗ₜ[ℂ] z) (DFunLike.congr_fun (ih η hη) y)

/-- Replace the selected original positions and retain every other actual source vector.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–355. -/
def selectedSourceVectors {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (e : sourceLocations w) (ξ : branchLabels w e.1) :
    euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2) := by
  classical
  exact if e ∈ S then η e ξ else sourceVectorAt w e ξ

/-- If every selected source meets the affected parties, then its substitutions
reaggregate all untouched gates. The unchanged-source condition is derived from
the selected positions; no equality of operator coefficients is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–381. -/
theorem eval_selectedSourceVectors_eq_sum (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true) :
    (∑ ξ, coefficient A w ξ •
        (partialWithSources A w (selectedSourceVectors w S η) ξ).eval) ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a) =
      isoL (Layout.mapOwnerIso (affectedOwner A) b) ∘L
        evalWithSources w (selectedSourceVectors w S η) := by
  apply evalWithSources_eq_sum_partialWithSources
  intro e ξ hUntouched
  have he : e ∉ S := fun hes ↦
    hUntouched (isTouched_of_source_endpoint A w e (hS e hes))
  simp only [selectedSourceVectors, ite_eq_right he]

end SourceCircuit
end TNLean.PEPS.PairEffect
