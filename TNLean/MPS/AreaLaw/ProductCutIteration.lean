/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProductReplacement

/-!
# Product replacement at finitely many cuts

A normalized MPS can be made to factor across each of finitely many cuts at which
the target factors, without decreasing its overlap with that target. Each step
preserves all earlier rank-one cuts because no cut rank increases.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 421–470. This is the finite iteration of the product
replacement argument, before specializing to identical copies.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The inner product of two product vectors factors into the inner products
of their corresponding factors. -/
private theorem inner_tensorVector {α β : Type*} [Fintype α] [Fintype β]
    (a u : EuclideanSpace ℂ α) (b v : EuclideanSpace ℂ β) :
    inner ℂ (euclideanTensorVector a b) (euclideanTensorVector u v) =
      inner ℂ a u * inner ℂ b v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    euclideanTensorVector, Pi.star_apply, star_mul,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Product replacement at finitely many target product cuts preserves normalization
and the MPS bond bound, and does not decrease the overlap with the target.
Source: arXiv:0705.0292v2, lines 421–470. Factorization of the target at the selected
cuts is explicit; in the identical-copy application these are the copy boundaries. -/
theorem IsOpenMPS.exists_rank_one_at_product_cuts {D : ℕ}
    {ψ ξ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) (hnorm : ‖ψ‖ = 1)
    (S : Finset ℕ)
    (hξ : ∀ k ∈ S,
      ∃ (a : EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)))
        (b : EuclideanSpace ℂ ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q)),
        Entropy.cutVector (leftBlock L k) ξ = euclideanTensorVector a b) :
    ∃ χ : EuclideanSpace ℂ (Fin L → Fin q),
      IsOpenMPS L q D (fun x ↦ χ x) ∧ ‖χ‖ = 1 ∧
      ‖inner ℂ ξ ψ‖ ≤ ‖inner ℂ ξ χ‖ ∧
      (∀ j, (cutMatrix χ j).rank ≤ (cutMatrix ψ j).rank) ∧
      ∀ k ∈ S, (cutMatrix χ k).rank ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ψ, hψ, hnorm, le_rfl, fun _ ↦ le_rfl, by simp⟩
  | @insert k S hk ih =>
    obtain ⟨φ, hφ, hnφ, hoφ, hrφ, hsφ⟩ := ih fun j hj ↦ hξ j (Finset.mem_insert_of_mem hj)
    obtain ⟨a, b, hab⟩ := hξ k (Finset.mem_insert_self k S)
    obtain ⟨χ, u, v, hχ, hnχ, hu, hv, hmatrix, hrχ, hov⟩ :=
      hφ.exists_product_overlap_ge hnφ k a b
    have hcut : Entropy.cutVector (leftBlock L k) χ = euclideanTensorVector u v := by
      ext ij
      exact congrArg (fun M ↦ M ij.1 ij.2) hmatrix
    refine ⟨χ, hχ, hnχ, hoφ.trans ?_, fun j ↦ (hrχ j).trans (hrφ j), ?_⟩
    · rw [← inner_cutVector k ξ φ, ← inner_cutVector k ξ χ, hab, hcut,
        inner_tensorVector, norm_mul]
      exact hov
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [hmatrix]
        exact rank_vecMulVec_le _ _
      · exact (hrχ j).trans (hsφ j hj)

end TNLean.MPS.AreaLaw
