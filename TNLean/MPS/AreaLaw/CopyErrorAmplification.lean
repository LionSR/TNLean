/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyMPSFactor
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

/-- The squared fidelity of two unit vectors lies in the unit interval. -/
private theorem sq_norm_inner_mem_Icc {α : Type*} [Fintype α]
    {u v : EuclideanSpace ℂ α} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℂ u v‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h : ‖inner ℂ u v‖ ≤ 1 := by simpa [hu, hv] using norm_inner_le_norm u v
  exact ⟨sq_nonneg _, pow_le_one₀ (norm_nonneg _) h⟩

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
  have hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i ↦ sq_norm_inner_mem_Icc hη (hθ i)
  obtain ⟨i, hi⟩ := Real.exists_optimizedPureTraceError_pow_le_prod hK f hf
  have hprod : ‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) (copyProduct θ)‖ ^ 2 =
      ∏ j, f j := sq_norm_inner_copyProduct _ _
  rw [← hprod] at hi
  refine ⟨i, hi, ?_⟩
  exact (Real.sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one
    (hf i).1 (hf i).2 hK (hi.trans_lt hsmall)).trans hi

/-- From a normalized MPS approximation to repeated copies, extract one normalized
block MPS satisfying the scalar error amplification estimate.
Source: arXiv:0705.0292v2, lines 421–479. The result concerns the optimized scalar
error of the squared fidelity; no matrix optimization formula is assumed. -/
theorem IsOpenMPS.exists_copy_error_amplification {D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin (K * L) → Fin q)}
    (hψ : IsOpenMPS (K * L) q D (fun x ↦ ψ x)) (hnorm : ‖ψ‖ = 1)
    {η : EuclideanSpace ℂ (Fin L → Fin q)} (hη : ‖η‖ = 1) (hK : 1 ≤ K)
    (hsmall : Real.optimizedPureTraceError
      (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) ψ‖ ^ 2) < 1) :
    ∃ θ : EuclideanSpace ℂ (Fin L → Fin q),
      IsOpenMPS L q D (fun x ↦ θ x) ∧ ‖θ‖ = 1 ∧
      Real.optimizedPureTraceError ((‖inner ℂ η θ‖ ^ 2) ^ K) ≤
        Real.optimizedPureTraceError
          (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) ψ‖ ^ 2) ∧
      Real.sqrt ((K : ℝ) / 4) * Real.optimizedPureTraceError (‖inner ℂ η θ‖ ^ 2) ≤
        Real.optimizedPureTraceError
          (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) ψ‖ ^ 2) := by
  obtain ⟨θ, hθ, hm, ho⟩ :=
    hψ.exists_unit_copy_product_overlap_ge hnorm hK (fun _ ↦ η)
  have hηcopy : ‖copyProduct (fun _ : Fin K ↦ η)‖ = 1 := by
    simp [norm_copyProduct, hη]
  have hθcopy : ‖copyProduct θ‖ = 1 := by simp [norm_copyProduct, hθ]
  have herr := Real.optimizedPureTraceError_antitoneOn
    (sq_norm_inner_mem_Icc hηcopy hnorm) (sq_norm_inner_mem_Icc hηcopy hθcopy)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ho)
  obtain ⟨i, hp, ha⟩ := exists_copy_optimizedPureTraceError_le hη θ hθ hK
    (herr.trans_lt hsmall)
  exact ⟨θ i, hm i, hθ i, hp.trans herr, ha.trans herr⟩

end TNLean.MPS.AreaLaw
