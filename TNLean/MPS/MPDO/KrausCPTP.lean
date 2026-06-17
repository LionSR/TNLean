/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs

/-!
# Trace-preserving completely positive maps in Kraus form

This file records the minimal finite-dimensional predicate for
trace-preserving completely positive maps used in the MPDO RFP development.
The map is represented by rectangular Kraus operators
`Aᵢ : Matrix β α ℂ`, so that it may act between matrix algebras of different
dimensions.

## Main declarations

* `IsKrausCPTP`: a trace-preserving completely positive map in rectangular
  Kraus form.
* `isKrausCPTP_id`: the identity map is trace-preserving completely positive.
* `isKrausCPTP_comp`: composition preserves the trace-preserving completely
  positive property.
-/

open scoped Matrix BigOperators

/-- A **trace-preserving completely positive map** in Kraus form
`S(X) = ∑ᵢ Aᵢ X Aᵢ†` with `∑ᵢ Aᵢ† Aᵢ = I`; rectangular Kraus operators
`Aᵢ : β × α` allow different in/out dimensions. The Kraus form itself gives
completely positive, and the resolution-of-identity condition is exactly trace
preservation. arXiv:1606.00608 Definition 4.1 uses tp-CP maps on the physical
indices. -/
def IsKrausCPTP {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Matrix β α ℂ),
    (∀ X, S X = ∑ i, A i * X * (A i)ᴴ) ∧ (∑ i, (A i)ᴴ * A i = (1 : Matrix α α ℂ))

/-- The identity map is trace-preserving completely positive; the single Kraus
operator is the identity matrix. -/
theorem isKrausCPTP_id {α : Type*} [Fintype α] [DecidableEq α] :
    IsKrausCPTP (LinearMap.id : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) := by
  refine ⟨1, fun _ => 1, ?_, ?_⟩
  · intro X
    simp
  · simp

/-- Composition of trace-preserving completely positive maps is again
trace-preserving completely positive. If `T` has Kraus operators `Bⱼ` and `S`
has Kraus operators `Aᵢ`, then `S ∘ T` has Kraus operators `Aᵢ Bⱼ`, and the
resolution of identity for the composite follows from those of `S` and `T`:
∑ᵢⱼ (AᵢBⱼ)† (AᵢBⱼ) =
∑ⱼ Bⱼ† (∑ᵢ Aᵢ† Aᵢ) Bⱼ = ∑ⱼ Bⱼ† Bⱼ = I. -/
theorem isKrausCPTP_comp {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {S : Matrix β β ℂ →ₗ[ℂ] Matrix γ γ ℂ}
    (hT : IsKrausCPTP T) (hS : IsKrausCPTP S) : IsKrausCPTP (S ∘ₗ T) := by
  obtain ⟨r, A, hA_form, hA_tp⟩ := hS
  obtain ⟨s, B, hB_form, hB_tp⟩ := hT
  refine ⟨r * s, fun k => A (finProdFinEquiv.symm k).1 * B (finProdFinEquiv.symm k).2, ?_, ?_⟩
  · intro X
    rw [LinearMap.comp_apply, hB_form X, hA_form,
      ← finProdFinEquiv.sum_comp (fun k => (A (finProdFinEquiv.symm k).1 *
          B (finProdFinEquiv.symm k).2) * X *
        (A (finProdFinEquiv.symm k).1 * B (finProdFinEquiv.symm k).2)ᴴ)]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rw [← finProdFinEquiv.sum_comp (fun k => (A (finProdFinEquiv.symm k).1 *
        B (finProdFinEquiv.symm k).2)ᴴ *
      (A (finProdFinEquiv.symm k).1 * B (finProdFinEquiv.symm k).2))]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.conjTranspose_mul]
    rw [Finset.sum_comm, ← hB_tp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have step : ∑ i : Fin r, (B j)ᴴ * (A i)ᴴ * (A i * B j)
        = (B j)ᴴ * ((∑ i : Fin r, (A i)ᴴ * A i) * B j) := by
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
    rw [step, hA_tp, Matrix.one_mul]
