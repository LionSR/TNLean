/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.MPDO.BoundaryActionCrossTransport

/-!
# Cross-endpoint fusion entries

Equality of the two endpoints' actual raw L matrices yields the entrywise
fusion identity for their mixed operator. The rectangular action-tree
contraction is evaluated against a matrix unit, and its independent finite
sums are reordered into the operator-product contraction.

The physical and state-bond dimensions of the endpoints may differ. No
additional assumptions on the endpoint fusion or action maps are required.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
  `REsubmission.tex`, lines 1667--1685.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d₀ d₁ r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)
  {O₀ : ∀ a, MPOTensor d₀ (χ₀ a)} {A₀ : MPSTensor d₀ D₀}
  {O₁ : ∀ a, MPOTensor d₁ (χ₁ a)} {A₁ : MPSTensor d₁ D₁}
  (hF₀ : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O₀ a) A₀)
    (fun _ : Fin (m a) ↦ A₀) (VA₀ a) (WA₀ a))
  (hF₁ : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O₁ a) A₁)
    (fun _ : Fin (m a) ↦ A₁) (VA₁ a) (WA₁ a))
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- The mixed cross-sector fusion identity, with both physical matrix entries
and all operator bonds explicit. It follows by selecting one matrix unit in
the rectangular action-tree contraction. Source: GLM23, `REsubmission.tex`,
lines 1667--1685. -/
theorem crossEndpoint_fusion_entry_of_actionLMatrix_eq
    (a b : Fin r)
    (hL : actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0)
    (r₀ k₀ : Fin D₀) (s₁ l₁ : Fin D₁)
    (α₀ : Fin (χ₀ a)) (γ₀ : Fin (χ₀ b))
    (β₁ : Fin (χ₁ a)) (δ₁ : Fin (χ₁ b)) :
    (∑ u : Fin D₀, ∑ v : Fin D₁,
      (∑ i : Fin (m a),
        WA₀ a i (finProdFinEquiv (α₀, u)) r₀ *
          VA₁ a i s₁ (finProdFinEquiv (β₁, v))) *
      (∑ j : Fin (m b),
        WA₀ b j (finProdFinEquiv (γ₀, k₀)) u *
          VA₁ b j v (finProdFinEquiv (δ₁, l₁)))) =
    ∑ c : Fin r, ∑ mu : Fin (N a b c),
      ∑ ξ : Fin (χ₀ c), ∑ η : Fin (χ₁ c),
        WF₀ a b c mu (finProdFinEquiv (α₀, γ₀)) ξ *
          (∑ h : Fin (m c),
            WA₀ c h (finProdFinEquiv (ξ, k₀)) r₀ *
              VA₁ c h s₁ (finProdFinEquiv (η, l₁))) *
          VF₁ a b c mu η (finProdFinEquiv (β₁, δ₁)) := by
  classical
  have h := crossEndpoint_actionTree_contraction_apply_of_actionLMatrix_eq
    VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ hF₀ hA₀ hF₁ hA₁
    hInj₀ hInj₁ hD₀ hD₁ a b hL (Matrix.single r₀ s₁ 1)
    α₀ γ₀ k₀ β₁ δ₁ l₁
  simp only [Matrix.single_apply, ite_and, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_const_zero,
    Finset.mem_univ, ite_true] at h
  calc
    _ = ∑ i : Fin (m a), ∑ j : Fin (m b),
        (∑ u : Fin D₀,
          WA₀ b j (finProdFinEquiv (γ₀, k₀)) u *
            WA₀ a i (finProdFinEquiv (α₀, u)) r₀) *
        (∑ v : Fin D₁,
          VA₁ a i s₁ (finProdFinEquiv (β₁, v)) *
            VA₁ b j v (finProdFinEquiv (δ₁, l₁))) := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [Fintype.sum_last_two_first_four]
      refine Finset.sum_congr rfl fun (i : Fin (m a)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (j : Fin (m b)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (u : Fin D₀) _ ↦ ?_
      refine Finset.sum_congr rfl fun (v : Fin D₁) _ ↦ ?_
      ring
    _ = ∑ c : Fin r, ∑ k : Fin (m c), ∑ mu : Fin (N a b c),
        (∑ ξ : Fin (χ₀ c),
          WF₀ a b c mu (finProdFinEquiv (α₀, γ₀)) ξ *
            WA₀ c k (finProdFinEquiv (ξ, k₀)) r₀) *
        (∑ η : Fin (χ₁ c),
          VA₁ c k s₁ (finProdFinEquiv (η, l₁)) *
            VF₁ a b c mu η (finProdFinEquiv (β₁, δ₁))) := h
    _ = _ := by
      refine Finset.sum_congr rfl fun (c : Fin r) _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (mu : Fin (N a b c)) _ ↦ ?_
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (ξ : Fin (χ₀ c)) _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (η : Fin (χ₁ c)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (k : Fin (m c)) _ ↦ ?_
      ring

end MPOTensor
