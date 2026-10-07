import TNLean.PEPS.Approximation.PartialSourceEvaluation

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuitRegression
open SourceCircuit

private def emptyGate : PreparedSourceGate (fun _ : Empty ↦ (0 : ℂ))
    ([] : Layout Bool) [] :=
  Classical.choose (Word.exists_preparedSourceGate (fun _ : Empty ↦ (0 : ℂ))
    (fun _ ↦ Word.id ([] : Layout Bool)) (fun _ ↦ trivial) (by simp))

private theorem eval_emptyGate : emptyGate.eval = 0 := by
  exact (Classical.choose_spec (Word.exists_preparedSourceGate (fun _ : Empty ↦ (0 : ℂ))
    (fun _ ↦ Word.id ([] : Layout Bool)) (fun _ ↦ trivial) (by simp))).trans (by simp)

private abbrev emptyCircuit : SourceCircuit ([] : Layout Bool) [] :=
  .gate (Function.Embedding.refl Bool) emptyGate []

/-- An exterior gate with no monomials still has one unexpanded choice, weighted
by one, even though its aggregate operator is zero. -/
theorem exterior_empty_branch :
    Choices (fun _ ↦ false) emptyCircuit = Unit ∧
      Fintype.card (Choices (fun _ ↦ false) emptyCircuit) = 1 ∧
      (∀ ξ : Choices (fun _ ↦ false) emptyCircuit,
        coefficient (fun _ ↦ false) emptyCircuit ξ = 1) ∧
      emptyCircuit.eval = 0 := by
  have he : Choices (fun _ ↦ false) emptyCircuit = Unit := by
    simp [Choices]
  refine ⟨he, ?_, ?_, ?_⟩
  · exact (Fintype.card_congr (Equiv.cast he)).trans (by simp)
  · intro ξ
    simp [coefficient]
  · simp [eval, PreparedSourceGate.evalAtOwners, eval_emptyGate]

private def phaseCoefficient (_ : Bool) : ℂ := Complex.I / 2

private theorem phase_sum :
    (∑ ξ : Bool, phaseCoefficient ξ • (Word.id ([] : Layout Bool)).eval) =
      Complex.I • (Word.id ([] : Layout Bool)).eval := by
  simp only [Fintype.sum_bool, phaseCoefficient, ← add_smul, add_halves]

private def phaseGate : PreparedSourceGate phaseCoefficient ([] : Layout Bool) [] :=
  Classical.choose (Word.exists_preparedSourceGate phaseCoefficient
    (fun _ ↦ Word.id ([] : Layout Bool)) (fun _ ↦ trivial) (by
      rw [phase_sum, norm_smul, Complex.norm_I, one_mul]
      exact norm_id_le))

private theorem eval_phaseGate : phaseGate.eval =
    Complex.I • (Word.id ([] : Layout Bool)).eval := by
  exact (Classical.choose_spec (Word.exists_preparedSourceGate phaseCoefficient
    (fun _ ↦ Word.id ([] : Layout Bool)) (fun _ ↦ trivial) (by
      rw [phase_sum, norm_smul, Complex.norm_I, one_mul]
      exact norm_id_le))).trans phase_sum

private abbrev phaseCircuit : SourceCircuit ([] : Layout Bool) [] :=
  .gate (Function.Embedding.refl Bool) phaseGate []

private theorem eval_phaseCircuit (z : ℂ) : phaseCircuit.eval z = Complex.I * z := by
  simp [eval, PreparedSourceGate.evalAtOwners, eval_phaseGate, Layout.mapOwnerIso,
    appendIso, isoL_apply, Word.eval, LinearIsometryEquiv.refl]

/-- Repeated occurrences of the same two-label gate have independent choices.
Their nonreal coefficients multiply without complex conjugation. -/
theorem repeated_touching_choices :
    Fintype.card (Choices (fun _ ↦ true) (.comp phaseCircuit phaseCircuit)) = 4 ∧
      ∀ ξ ζ : Choices (fun _ ↦ true) phaseCircuit,
        coefficient (fun _ ↦ true) (.comp phaseCircuit phaseCircuit) (ξ, ζ) =
          coefficient (fun _ ↦ true) phaseCircuit ξ *
            coefficient (fun _ ↦ true) phaseCircuit ζ ∧
        coefficient (fun _ ↦ true) (.comp phaseCircuit phaseCircuit) (ξ, ζ) =
          -(1 / 4 : ℂ) := by
  have he : Choices (fun _ ↦ true) phaseCircuit = Bool := by simp [Choices]
  have hc (ξ : Choices (fun _ ↦ true) phaseCircuit) :
      coefficient (fun _ ↦ true) phaseCircuit ξ = Complex.I / 2 := by
    simp [coefficient, phaseCoefficient]
  constructor
  · change Fintype.card (Choices (fun _ ↦ true) phaseCircuit ×
      Choices (fun _ ↦ true) phaseCircuit) = 4
    rw [Fintype.card_prod, Fintype.card_congr (Equiv.cast he)]
    decide
  · intro ξ ζ
    refine ⟨rfl, ?_⟩
    change coefficient (fun _ ↦ true) phaseCircuit ξ *
      coefficient (fun _ ↦ true) phaseCircuit ζ = _
    rw [hc, hc]
    norm_num [div_mul_div_comm, Complex.I_mul_I]

/-- The actual partial expansion retains a nonreal gate phase and its square
under two successive occurrences. -/
theorem phase_partial_expansion :
    expandedEval (fun _ ↦ true) phaseCircuit (1 : ℂ) = Complex.I ∧
      expandedEval (fun _ ↦ true) (.comp phaseCircuit phaseCircuit) (1 : ℂ) = (-1 : ℂ) := by
  constructor
  · have he := DFunLike.congr_fun
      (expandedEval_mapOwner (fun _ ↦ true) phaseCircuit) (1 : ℂ)
    change expandedEval (fun _ ↦ true) phaseCircuit (1 : ℂ) = phaseCircuit.eval 1 at he
    simpa only [mul_one] using he.trans (eval_phaseCircuit (1 : ℂ))
  · have he := DFunLike.congr_fun
      (expandedEval_mapOwner (fun _ ↦ true) (.comp phaseCircuit phaseCircuit)) (1 : ℂ)
    change expandedEval (fun _ ↦ true) (.comp phaseCircuit phaseCircuit) (1 : ℂ) =
      phaseCircuit.eval (phaseCircuit.eval 1) at he
    have hp := (congrArg phaseCircuit.eval (eval_phaseCircuit (1 : ℂ))).trans
      (eval_phaseCircuit (Complex.I * 1))
    simpa only [mul_one, Complex.I_mul_I] using he.trans hp

end TNLean.PEPS.PairEffect.SourceCircuitRegression
