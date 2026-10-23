/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyProduct
import QICLean.Analysis.OptimizedPureTraceError

/-!
# Scalar error amplification for products of block vectors

For a unit target and unit block factors, squared fidelity is multiplicative.
Repeating a factor with maximal fidelity therefore gives no larger optimized
scalar error than the original product. If the product error is less than one,
the scalar amplification bound applies to this selected factor.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 421–479. These estimates concern the scalar function of
squared fidelity; they do not assume a matrix optimization formula.
-/

namespace TNLean.MPS.AreaLaw

variable {K L q : ℕ}

/-- Squared fidelities of block products multiply. -/
theorem sq_norm_inner_copyProduct (η θ : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖inner ℂ (copyProduct η) (copyProduct θ)‖ ^ 2 =
      ∏ i, ‖inner ℂ (η i) (θ i)‖ ^ 2 := by
  rw [inner_copyProduct, norm_prod, Finset.prod_pow]

/-- One factor of a product approximation satisfies the scalar amplification bound.
The product error below one supplies the needed smallness condition internally.
Source: arXiv:0705.0292v2, lines 421–479. -/
theorem exists_copy_optimizedPureTraceError_le {η : EuclideanSpace ℂ (Fin L → Fin q)}
    (hη : ‖η‖ = 1) (θ : Fin K → EuclideanSpace ℂ (Fin L → Fin q))
    (hθ : ∀ i, ‖θ i‖ = 1) (hK : 1 ≤ K)
    (hsmall : Real.optimizedPureTraceError
      (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) (copyProduct θ)‖ ^ 2) < 1) :
    ∃ i : Fin K,
      Real.optimizedPureTraceError ((‖inner ℂ η (θ i)‖ ^ 2) ^ K) ≤
        Real.optimizedPureTraceError
          (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) (copyProduct θ)‖ ^ 2) ∧
      Real.sqrt ((K : ℝ) / 4) * Real.optimizedPureTraceError (‖inner ℂ η (θ i)‖ ^ 2) ≤
        Real.optimizedPureTraceError
          (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) (copyProduct θ)‖ ^ 2) := by
  let f : Fin K → ℝ := fun i ↦ ‖inner ℂ η (θ i)‖ ^ 2
  have hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have h : ‖inner ℂ η (θ i)‖ ≤ 1 := by
      simpa [hη, hθ i] using norm_inner_le_norm η (θ i)
    exact ⟨sq_nonneg _, by dsimp only [f]; nlinarith [norm_nonneg (inner ℂ η (θ i))]⟩
  obtain ⟨i, hi⟩ := Real.exists_optimizedPureTraceError_pow_le_prod hK f hf
  have hprod : ‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) (copyProduct θ)‖ ^ 2 =
      ∏ j, f j := sq_norm_inner_copyProduct _ _
  rw [← hprod] at hi
  refine ⟨i, hi, ?_⟩
  exact (Real.sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one
    (hf i).1 (hf i).2 hK (hi.trans_lt hsmall)).trans hi

end TNLean.MPS.AreaLaw
