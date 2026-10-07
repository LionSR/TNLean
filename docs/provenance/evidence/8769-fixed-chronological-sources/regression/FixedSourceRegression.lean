import TNLean.PEPS.Approximation.SourceCircuitChoiceAt

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.FixedSourceRegression
open SourceCircuit

private abbrev oneSpace : HSpace := HSpace.of ℂ
private abbrev pairOutput : Layout Bool := [⟨false, oneSpace⟩, ⟨true, oneSpace⟩]

private def phaseVector (ξ : Bool) : oneSpace ⊗[ℂ] oneSpace :=
  (if ξ then Complex.I else 1) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))

private def sourceWord (ξ : Bool) : Word ([] : Layout Bool) pairOutput :=
  .source Bool.false_ne_true oneSpace oneSpace (phaseVector ξ) []

private theorem sourceWord_allowed (ξ : Bool) : (sourceWord ξ).IsAllowed := by
  cases ξ <;> simp [sourceWord, Word.IsAllowed, phaseVector, norm_smul, TensorProduct.norm_tmul]

private theorem aggregate_contractive :
    ‖∑ ξ : Bool, (1 / 2 : ℂ) • (sourceWord ξ).eval‖ ≤ 1 := by
  calc
    _ ≤ ∑ ξ : Bool, ‖(1 / 2 : ℂ) • (sourceWord ξ).eval‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Bool, ‖(1 / 2 : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro ξ _
      rw [norm_smul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Word.norm_eval_le_one _ (sourceWord_allowed ξ)) (norm_nonneg (1 / 2 : ℂ))
    _ = 1 := by norm_num [Fintype.sum_bool]

private def sourceGate : PreparedSourceGate (fun _ : Bool ↦ (1 / 2 : ℂ))
    ([] : Layout Bool) pairOutput :=
  Classical.choose (Word.exists_preparedSourceGate (fun _ : Bool ↦ (1 / 2 : ℂ))
    sourceWord sourceWord_allowed aggregate_contractive)

private theorem sourceGate_has_slot : 0 < sourceGate.slots.length := by
  have hk : s(false, true) ∈ sourceGate.slots.map PairSource.partyPair :=
    (sourceGate.pair_complete s(false, true)).mpr (by simp)
  exact List.length_pos_iff.mpr (fun h ↦ by simp [h] at hk)

private abbrev sourceCircuit (tail : Layout Bool) :
    SourceCircuit tail (pairOutput ++ tail) :=
  .gate (Function.Embedding.refl Bool) sourceGate tail

private abbrev repeatedCircuit : SourceCircuit ([] : Layout Bool) (pairOutput ++ pairOutput) :=
  .comp (sourceCircuit []) (sourceCircuit pairOutput)

private def localChoice (ξ : Bool) (tail : Layout Bool) :
    Choices (fun _ ↦ true) (sourceCircuit tail) :=
  Equiv.cast (by simp [Choices]) ξ

private def repeatedChoice : Choices (fun _ ↦ true) repeatedCircuit :=
  (localChoice false [], localChoice true pairOutput)

private def firstSlot (i : Fin sourceGate.slots.length) : sourceLocations repeatedCircuit :=
  ⟨.inl (), i⟩

private def secondSlot (i : Fin sourceGate.slots.length) : sourceLocations repeatedCircuit :=
  ⟨.inr (), i⟩

private theorem first_vector (i : Fin sourceGate.slots.length) :
    sourceVectorAt repeatedCircuit (firstSlot i)
      (choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice (firstSlot i).1
        (isTouched_of_source_endpoint _ _ _ (Or.inl rfl))) = sourceGate.vector false i := by
  simp only [List.cons_append, List.nil_append, repeatedCircuit, sourceCircuit, firstSlot,
    choiceAt, Layout.mapOwner_nil, Layout.mapOwner_cons, Choices, exists_const,
    ↓dreduceIte, repeatedChoice, localChoice, sourceVectorAt]
  exact congrArg (fun ξ ↦ sourceGate.vector ξ i)
    ((Equiv.cast _).symm_apply_apply false)

private theorem second_vector (i : Fin sourceGate.slots.length) :
    sourceVectorAt repeatedCircuit (secondSlot i)
      (choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice (secondSlot i).1
        (isTouched_of_source_endpoint _ _ _ (Or.inl rfl))) = sourceGate.vector true i := by
  simp only [List.cons_append, List.nil_append, repeatedCircuit, sourceCircuit, secondSlot,
    choiceAt, Layout.mapOwner_nil, Layout.mapOwner_cons, Choices, exists_const,
    ↓dreduceIte, repeatedChoice, localChoice, sourceVectorAt]
  exact congrArg (fun ξ ↦ sourceGate.vector ξ i)
    ((Equiv.cast _).symm_apply_apply true)

private def retainedIndex (e : sourceLocations repeatedCircuit) :
    Fin (partialSlots (fun _ ↦ true) repeatedCircuit).length :=
  (partialSlotEquiv (fun _ ↦ true) repeatedCircuit).symm ⟨e, Or.inl rfl⟩

private theorem retained_vector (e : sourceLocations repeatedCircuit) :
    HEq (partialSlotVector (fun _ ↦ true) repeatedCircuit repeatedChoice (retainedIndex e))
      (sourceVectorAt repeatedCircuit e
        (choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice e.1
          (isTouched_of_source_endpoint _ _ _ (Or.inl rfl)))) := by
  have hc {s t : {e : sourceLocations repeatedCircuit //
      (fun _ : Bool ↦ true) (endpoints repeatedCircuit e).1 = true ∨
        (fun _ : Bool ↦ true) (endpoints repeatedCircuit e).2 = true}} (h : s = t) :
      HEq (sourceVectorAt repeatedCircuit s.1
        (choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice s.1.1
          (isTouched_of_source_endpoint _ _ _ s.2)))
        (sourceVectorAt repeatedCircuit t.1
          (choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice t.1.1
            (isTouched_of_source_endpoint _ _ _ t.2))) := by
    cases h
    rfl
  exact hc ((partialSlotEquiv (fun _ ↦ true) repeatedCircuit).apply_symm_apply _)

/-- Two occurrences of a gate constructed from genuine pair preparations retain
independent local labels, even when the gate itself is reused unchanged. -/
theorem repeated_local_labels (i : Fin sourceGate.slots.length) :
    choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice (firstSlot i).1
        (isTouched_of_source_endpoint _ _ _ (Or.inl rfl)) = false ∧
      choiceAt (fun _ ↦ true) repeatedCircuit repeatedChoice (secondSlot i).1
        (isTouched_of_source_endpoint _ _ _ (Or.inl rfl)) = true := by
  constructor
  · change (Equiv.cast _) ((Equiv.cast _) false) = false
    exact (Equiv.cast _).symm_apply_apply false
  · change (Equiv.cast _) ((Equiv.cast _) true) = true
    exact (Equiv.cast _).symm_apply_apply true

/-- The canonical common inventory contains two distinct original occurrences,
and its normalized vector at each is the original vector for that occurrence's
own selected label. The nonempty gate inventory is produced from actual allowed
source words, rather than assumed as preparation data. -/
theorem repeated_fixed_source_vectors :
    ∃ i : Fin sourceGate.slots.length,
      retainedIndex (firstSlot i) ≠ retainedIndex (secondSlot i) ∧
      HEq (partialSlotVector (fun _ ↦ true) repeatedCircuit repeatedChoice
        (retainedIndex (firstSlot i))) (sourceGate.vector false i) ∧
      HEq (partialSlotVector (fun _ ↦ true) repeatedCircuit repeatedChoice
        (retainedIndex (secondSlot i))) (sourceGate.vector true i) := by
  let i : Fin sourceGate.slots.length := ⟨0, sourceGate_has_slot⟩
  refine ⟨i, ?_, (retained_vector _).trans (heq_of_eq (first_vector i)),
    (retained_vector _).trans (heq_of_eq (second_vector i))⟩
  intro h
  have he := congrArg (fun j ↦ ((partialSlotEquiv (fun _ ↦ true) repeatedCircuit) j).1) h
  simp only [retainedIndex, Equiv.apply_symm_apply] at he
  have hg := congrArg Sigma.fst he
  cases hg

/-- Applying the proved canonical preparation to this actual repeated gate gives
a nonempty literal source inventory of the partial monomial. -/
theorem actual_source_inventory_nonempty :
    (partialWord (fun _ ↦ true) repeatedCircuit repeatedChoice).sources ≠ [] := by
  obtain ⟨_, hS, _, _, _, _⟩ :=
    exists_partial_source_preparation_with_original_vectors (fun _ ↦ true)
      repeatedCircuit (show repeatedCircuit.IsAllowed from ⟨trivial, trivial⟩)
  have hlen := congrArg List.length (hS repeatedChoice)
  simp only [SourceInventory.ofSlots, List.length_ofFn] at hlen
  have hi := (retainedIndex (firstSlot ⟨0, sourceGate_has_slot⟩)).isLt
  intro h
  rw [h, List.length_nil] at hlen
  omega

end TNLean.PEPS.PairEffect.FixedSourceRegression
