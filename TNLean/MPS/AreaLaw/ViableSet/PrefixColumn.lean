/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic

/-!
# A retained prefix column of a viable witness

A target with a fixed right configuration pairs with exactly one cut column.
That column remains in the retained left span and has norm at most one when
the viable witness is unit. Normalizing it improves the target overlap.
This is the prefix extraction used when the successive LVV construction is
applied to a chain extended by product-state ancillary sites.

Source: LVV13, arXiv:1307.5143v1, Definition `def:viable`, lines 240--244,
and the final induction, lines 652--678; this is an algebraic padding auxiliary.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The squared norms of the cut columns sum to the squared norm of the vector.
Auxiliary to prefix extraction from LVV13 viable sets, `def:viable`. -/
theorem sum_norm_cutColumn_sq {N q i : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin q)) :
    ∑ b, ‖cutColumn ψ i b‖ ^ 2 = ‖ψ‖ ^ 2 := by
  classical
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  change (∑ a, ∑ b, ‖ψ
    ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b))‖ ^ 2) = _
  simpa only [Fintype.sum_prod_type] using
    Equiv.sum_comp (Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm
      (fun σ ↦ ‖ψ σ‖ ^ 2)

/-- A cut column has norm at most the norm of its full vector.
Auxiliary to prefix extraction from LVV13 viable sets, `def:viable`. -/
theorem norm_cutColumn_le {N q i : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin q))
    (b : (v : {v : Fin N // v ∉ leftBlock N i}) → Fin q) :
    ‖cutColumn ψ i b‖ ≤ ‖ψ‖ := by
  have h := Finset.single_le_sum (fun b _ ↦ sq_nonneg ‖cutColumn ψ i b‖)
    (Finset.mem_univ b)
  rw [sum_norm_cutColumn_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 2 ≠ 0)).mp h

/-- Attach a fixed right basis configuration to a vector on the retained prefix.
Auxiliary to the product-ancilla use of LVV13, `def:viable`. -/
noncomputable def rightBasisExtension {N q i : ℕ} (v : LeftBlockVector N q i)
    (b : (j : {j : Fin N // j ∉ leftBlock N i}) → Fin q) :
    EuclideanSpace ℂ (Fin N → Fin q) := by
  classical
  exact WithLp.toLp 2 fun σ ↦
    if ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)) σ).2 = b then
      v (((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)) σ).1) else 0

/-- Only the column at the selected right configuration is nonzero.
Auxiliary to the product-ancilla use of LVV13, `def:viable`. -/
theorem cutColumn_rightBasisExtension {N q i : ℕ} (v : LeftBlockVector N q i)
    (b b' : (j : {j : Fin N // j ∉ leftBlock N i}) → Fin q) :
    cutColumn (rightBasisExtension v b) i b' = if b' = b then v else 0 := by
  classical
  ext a
  change (if ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i))
    ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b'))).2 = b then
      v (((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i))
        ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b'))).1) else 0) = _
  rw [Equiv.apply_symm_apply]
  split_ifs <;> rfl

/-- Pairing a right-basis extension selects exactly one cut column.
Auxiliary to the product-ancilla use of LVV13, `def:viable`. -/
theorem inner_rightBasisExtension {N q i : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin q)) (v : LeftBlockVector N q i)
    (b : (j : {j : Fin N // j ∉ leftBlock N i}) → Fin q) :
    ⟪ψ, rightBasisExtension v b⟫_ℂ = ⟪cutColumn ψ i b, v⟫_ℂ := by
  classical
  have heval (a : Entropy.RegionConfig (fun _ : Fin N ↦ q) (leftBlock N i))
      (b' : (j : {j : Fin N // j ∉ leftBlock N i}) → Fin q) :
      rightBasisExtension v b
        ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b')) =
        if b' = b then v a else 0 := by
    change (if ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i))
      ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b'))).2 = b then
        v (((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i))
          ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b'))).1) else 0) = _
    rw [Equiv.apply_symm_apply]
  have hsum := Equiv.sum_comp
    (Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm
    (fun σ ↦ rightBasisExtension v b σ * star (ψ σ))
  simp only [Fintype.sum_prod_type, heval, ite_mul, zero_mul] at hsum
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  change (∑ σ, rightBasisExtension v b σ * star (ψ σ)) =
    ∑ a, v a * star (ψ
      ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N i)).symm (a, b)))
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hsum.symm

/-- Attaching a right basis configuration preserves the Hilbert norm.
Auxiliary to the product-ancilla use of LVV13, `def:viable`. -/
theorem norm_rightBasisExtension {N q i : ℕ} (v : LeftBlockVector N q i)
    (b : (j : {j : Fin N // j ∉ leftBlock N i}) → Fin q) :
    ‖rightBasisExtension v b‖ = ‖v‖ := by
  classical
  have hsq : ‖rightBasisExtension v b‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← sum_norm_cutColumn_sq (i := i)]
    simp [cutColumn_rightBasisExtension, apply_ite]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end TNLean.MPS.AreaLaw
