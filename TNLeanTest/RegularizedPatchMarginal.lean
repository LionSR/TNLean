import TNLean.PEPS.AreaLaw.RegularizedPatchMarginal
import TNLeanTest.Support.SingleQubitConfig

/-! Heterogeneous dimensions, empty regions, and complex-conjugation regressions
for the canonical reduced states of the actual regularized output. -/

open scoped BigOperators Matrix ComplexOrder
open Matrix TNLean.PEPS TNLeanTest.SingleQubitConfig

section Heterogeneous

private abbrev LocalBasis (v : Fin 2) := Fin (v.val + 2)

example : Fintype.card (LocalBasis 0) = 2 ∧ Fintype.card (LocalBasis 1) = 3 := by
  norm_num [LocalBasis]

example (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset (Fin 2))) → LocalBasis v.1))
    (K : Matrix ((v : ({1} : Finset (Fin 2))) → LocalBasis v.1)
      ((v : ({1} : Finset (Fin 2))) → LocalBasis v.1) ℂ) :
    inner ℂ ξ (WithLp.toLp 2 (dependentRegionOperatorLift {1} K *ᵥ ξ)) =
      Matrix.trace (FiniteProduct.reducedPure LocalBasis
        (dependentGlobalConfigIsometry ξ) {1} * K) :=
  inner_dependentRegionOperatorLift_eq_trace_reducedPure {1} K ξ

example {m : ℕ} (regions : Fin m → Finset (Fin 2)) (a : Fin m → ℝ)
    (ha : ∀ j, 0 ≤ a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset (Fin 2))) → LocalBasis v.1))
    (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → LocalBasis v.1)
      ((v : regions j) → LocalBasis v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    (normalizedRegularizedPatchMarginal regions a b Ω x ∅).PosSemidef ∧
      (normalizedRegularizedPatchMarginal regions a b Ω x ∅).trace = 1 :=
  ⟨normalizedRegularizedPatchMarginal_posSemidef regions a b Ω x ∅,
    trace_normalizedRegularizedPatchMarginal regions a ha hb Ω hΩ hx ∅⟩

/-- The empty filter family still has the canonical trace-one empty marginal. -/
example
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset (Fin 2))) → LocalBasis v.1))
    (hΩ : ‖Ω‖ = 1) :
    (normalizedRegularizedPatchMarginal (Out := LocalBasis)
      (fun j : Fin 0 ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) 1 Ω
      (fun j ↦ Fin.elim0 j) ∅).trace = 1 :=
  trace_normalizedRegularizedPatchMarginal _ _ (fun j ↦ Fin.elim0 j)
    zero_lt_one Ω hΩ (fun j ↦ Fin.elim0 j) ∅

end Heterogeneous

section ComplexOrientation

private noncomputable def complexState : EuclideanSpace ℂ Config :=
  WithLp.toLp 2 fun σ ↦ ![1, Complex.I] (configEquiv.symm σ)

private noncomputable def pauliY : Matrix Config Config ℂ :=
  Matrix.reindex configEquiv configEquiv !![0, -Complex.I; Complex.I, 0]

private theorem pauliY_mulVec_complexState :
    pauliY *ᵥ WithLp.ofLp complexState = WithLp.ofLp complexState := by
  classical
  funext σ
  obtain ⟨i, rfl⟩ := configEquiv.surjective σ
  simp only [Matrix.mulVec, dotProduct, pauliY, Matrix.reindex_apply,
    Matrix.submatrix_apply, complexState, WithLp.ofLp_toLp]
  rw [← configEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  fin_cases i <;> norm_num [Fin.sum_univ_two]

/-- The complex phase makes the conjugation convention observable: reversing
the pure-state outer product would change this expectation from 2 to -2. -/
private theorem complexState_expectation :
    inner ℂ complexState (WithLp.toLp 2
      (dependentRegionOperatorLift (Out := fun _ : Unit ↦ Fin 2)
        Finset.univ pauliY *ᵥ complexState)) = 2 := by
  rw [lift_univ, pauliY_mulVec_complexState]
  rw [WithLp.toLp_ofLp, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ σ : Config, ![1, Complex.I] (configEquiv.symm σ) *
    star (![1, Complex.I] (configEquiv.symm σ))) = 2
  rw [← configEquiv.sum_comp]
  norm_num [Fin.sum_univ_two]

example :
    Matrix.trace (FiniteProduct.reducedPure (fun _ : Unit ↦ Fin 2)
      (dependentGlobalConfigIsometry complexState) Finset.univ * pauliY) = 2 :=
  (inner_dependentRegionOperatorLift_eq_trace_reducedPure (Out := fun _ : Unit ↦ Fin 2)
    Finset.univ pauliY
    complexState).symm.trans complexState_expectation

end ComplexOrientation
