import TNLean.PEPS.Approximation.ApproximateCircuitPolynomial

/-! Regression checks for noncontractive approximate scalar gates and repeated occurrences. -/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.ApproximateGateRegression

private def scalarList : PartyGate (P := Empty) [] [] :=
  [(2, .final (.id []))]

private def scalarCircuit : EffectCircuit (P := Empty) [] [] :=
  .gate (Function.Embedding.refl Empty) scalarList []

private def originalMap : scalarCircuit.GateMaps := .id ℂ ℂ

/-- The approximate sum is not a contraction; its original target is the identity. -/
theorem raw_scalar_norm_two : ‖gate (toGate scalarList)‖ = 2 := by
  simp only [scalarList, toGate, gate, PartyChain.toEffectChain, EffectChain.eval,
    Word.eval, add_zero, norm_smul, norm_id]
  norm_num

/-- Empty participant sets remain legitimate nonprivate scalar occurrences. -/
theorem scalar_isGateApproximation : scalarCircuit.IsGateApproximation 1 originalMap := by
  change Fintype.card Empty ≠ 1 ∧
    (∀ q ∈ scalarList, q.2.IsAllowed) ∧
    ‖(ContinuousLinearMap.id ℂ ℂ)‖ ≤ 1 ∧
    ‖gate (toGate scalarList) - ContinuousLinearMap.id ℂ ℂ‖ ≤ 1
  refine ⟨by simp, ?_, norm_id_le, ?_⟩
  · intro q hq
    simp only [scalarList, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst q
    trivial
  · simp only [scalarList, toGate, gate, PartyChain.toEffectChain, EffectChain.eval,
      Word.eval, add_zero]
    have he : (2 : ℂ) • ContinuousLinearMap.id ℂ ℂ - ContinuousLinearMap.id ℂ ℂ =
        ContinuousLinearMap.id ℂ ℂ := by simp only [two_smul, add_sub_cancel_right]
    rw [he]
    exact norm_id_le

/-- Repeated approximate scalar gates retain two distinct chronological occurrences. -/
theorem repeated_scalar_count :
    ((scalarCircuit.comp scalarCircuit).rescaledOriginal (by norm_num : (0 : ℝ) ≤ 1)
      (originalMap, originalMap)
      ⟨scalar_isGateApproximation, scalar_isGateApproximation⟩).nonprivateCount = 2 := by
  rfl

/-- Common rescaling corrects the actual noncontractive sum to the identity. -/
theorem rescaled_scalar_operator : gate (toGate (rescalePartyGate 1 scalarList)) =
    ContinuousLinearMap.id ℂ ℂ := by
  rw [gate_rescalePartyGate]
  norm_num [scalarList, toGate, gate, PartyChain.toEffectChain, EffectChain.eval, Word.eval,
    smul_smul]

end TNLean.PEPS.PairEffect.ApproximateGateRegression
