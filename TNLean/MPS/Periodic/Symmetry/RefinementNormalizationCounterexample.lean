/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse
import TNLean.MPS.CanonicalForm.Definitions

/-!
# A scalar counterexample to the printed refinement implication

The forward implication of Theorem 4.1 in arXiv:1708.00029, lines 717--731,
requires trace preservation of the target transfer map. The one-dimensional
tensor with sole letter `4` is a literal positive-weight irreducible-form
block and has a two-site refinement with sole root letter `2`. Its transfer
map multiplies by `16`, so it has no channel square root. See
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private def unitTensor : MPSTensor 1 1 := fun _ => 1

private def rootTensor : MPSTensor 1 1 :=
  fun _ => (2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The one-dimensional target tensor with sole letter four. -/
def refinementScalarCounterexample : MPSTensor 1 1 :=
  fun _ => (4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The normalized one-dimensional block has period one. -/
private theorem unitTensor_periodic : IsPeriodic 1 unitTensor := by
  have hMap : Kraus.transferMap unitTensor = LinearMap.id := by
    ext X i j
    fin_cases i
    fin_cases j
    simp [unitTensor]
  have hNormal := isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    unitTensor hMap
  apply (IsPeriodic.one_iff_primitive unitTensor).2
  refine ⟨hNormal.no_invariant_proj, ?_, hNormal.primitive_transfer⟩
  unfold IsLeftCanonical Kraus.IsTP
  simp [unitTensor]

/-- The target is literally one periodic normalized block with positive weight four. -/
private noncomputable def refinementScalarCounterexample_irreducibleForm :
    IsIrreducibleForm refinementScalarCounterexample := by
  refine {
    r := 1
    dim := fun _ => 1
    blocks := fun _ => unitTensor
    μ := fun _ => 4
    period := fun _ => 1
    periodic := fun _ => unitTensor_periodic
    weight_pos := ?_
    sameMPV := ?_ }
  · intro k
    norm_num
  · intro N σ
    rw [mpv_toTensorFromBlocks_eq_sum]
    change mpv (fun i => (4 : ℂ) • unitTensor i) σ = _
    rw [mpv_smul]
    simp

/-- The target family has a two-site refinement with root letter two. -/
private theorem refinementScalarCounterexample_refinable :
    IsPRefinable refinementScalarCounterexample 2 := by
  apply isPRefinable_of_transferMap_eq_blockTensor refinementScalarCounterexample rootTensor
    (by norm_num)
  have hTensor : refinementScalarCounterexample = blockTensor rootTensor 2 := by
    funext i
    have hw : Kraus.wordOfBlock 1 2 i = List.replicate 2 (0 : Fin 1) := by
      have hdecode : Kraus.decodeBlock 1 2 i = fun _ => (0 : Fin 1) :=
        Subsingleton.elim _ _
      simp only [Kraus.wordOfBlock, hdecode, List.ofFn_const]
    change (4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Kraus.evalWord rootTensor (Kraus.wordOfBlock 1 2 i)
    rw [hw, Kraus.evalWord_replicate]
    ext a b
    fin_cases a
    fin_cases b
    norm_num [rootTensor, pow_two, Matrix.mul_apply]
  exact congrArg Kraus.transferMap hTensor

/-- The target transfer map has no channel square root. -/
private theorem refinementScalarCounterexample_not_divisible :
    ¬ IsPDivisibleChannel (Kraus.transferMap refinementScalarCounterexample) 2 := by
  rintro ⟨E, hE, hpow⟩
  have hChannel : IsChannel (Kraus.transferMap refinementScalarCounterexample) := by
    rw [hpow]
    exact Kraus.isChannel_pow E hE 2
  have hTrace := hChannel.tp (1 : Matrix (Fin 1) (Fin 1) ℂ)
  norm_num [refinementScalarCounterexample, Kraus.transferMap_apply] at hTrace

/-- The positive scalar weight in irreducible form does not force
trace preservation in the printed forward implication of Theorem 4.1.
Source: arXiv:1708.00029, lines 717--731; see
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem refinement_normalization_counterexample :
    Nonempty (IsIrreducibleForm refinementScalarCounterexample) ∧
      (∃ A₀ : MPSTensor 1 1, IsPeriodic 1 A₀ ∧
        ∀ i, refinementScalarCounterexample i = (4 : ℂ) • A₀ i) ∧
      IsPRefinable refinementScalarCounterexample 2 ∧
      ¬ IsPDivisibleChannel (Kraus.transferMap refinementScalarCounterexample) 2 := by
  refine ⟨⟨refinementScalarCounterexample_irreducibleForm⟩,
    ⟨unitTensor, unitTensor_periodic, ?_⟩,
    refinementScalarCounterexample_refinable,
    refinementScalarCounterexample_not_divisible⟩
  intro i
  rfl

end MPSTensor
