/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ProductReferenceColumn

/-! Regressions for the same-vector density estimate consumed by literal
column selection on the open square. -/

open scoped Matrix

noncomputable section

namespace TNLean.PEPS.Approximation.Pinned
open TNLean.Lattice.Compression

-- Concrete independent error budgets give a 1/10 phase-error bound on a
-- nonzero, literally equal column of the supplied operator network.
example {L q : ℕ} {b : Type*} [Fintype b]
    (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ψ : EuclideanSpace ℂ ((Vertex L → Fin q) × b))
    (Ω : State L q) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1)
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ 1 / 100)
    (hlower : 1 - 1 / 200 ≤ ‖Ξ‖)
    (hcompression : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ))) ≤
        1 / 50) :
    ∃ z : Vertex L → Fin q,
      contractPEPS D (fixInput D A z) =
        Matrix.toEuclideanLin (operatorMatrix D A) (EuclideanSpace.single z 1) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖ : ℂ)⁻¹) •
        contractPEPS D (fixInput D A z) - Complex.exp (θ * Complex.I) • Ω‖ ≤ 1 / 10 := by
  have h := exists_fixInput_contractPEPS_of_product_reference D A e Ψ Ω Ξ
    hΨ hΩ hΞ herror hlower hcompression (by norm_num)
  norm_num at h ⊢
  exact h

-- The final PEPS keeps the exact original D, including its supplied bound;
-- positivity is concluded from the nonzero column rather than postulated.
example {L q : ℕ} {b : Type*} [Fintype b]
    (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    {B : ℝ} (hDB : ∀ f, (D f : ℝ) ≤ B)
    {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ψ : EuclideanSpace ℂ ((Vertex L → Fin q) × b))
    (Ω : State L q) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1)
    {ε δ κ η : ℝ}
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ ε)
    (hlower : 1 - δ ≤ ‖Ξ‖)
    (hcompression : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ))) ≤ κ)
    (hsmall : κ + 2 * ε + 2 * δ < 1) (hη : 2 * (κ + 2 * ε + 2 * δ) ≤ η) :
    ∃ z : Vertex L → Fin q,
      (∀ f, 0 < D f) ∧ (∀ f, (D f : ℝ) ≤ B) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖⁻¹ : ℝ) : ℂ) •
        contractPEPS D (fixInput D A z) - Complex.exp (θ * Complex.I) • Ω‖ ≤ η := by
  exact exists_peps_of_product_reference
    D A hDB e Ψ Ω Ξ hΨ hΩ hΞ herror hlower hcompression hsmall hη


-- Exact product and compression estimates give zero normalized phase error.
example {L q : ℕ} {b : Type*} [Fintype b]
    (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ψ : EuclideanSpace ℂ ((Vertex L → Fin q) × b))
    (Ω : State L q) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1)
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ 0)
    (hlower : 1 ≤ ‖Ξ‖)
    (hcompression : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ))) ≤ 0) :
    ∃ z : Vertex L → Fin q,
      contractPEPS D (fixInput D A z) =
        Matrix.toEuclideanLin (operatorMatrix D A) (EuclideanSpace.single z 1) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖ : ℂ)⁻¹) •
        contractPEPS D (fixInput D A z) - Complex.exp (θ * Complex.I) • Ω‖ ≤ 0 := by
  have h := exists_fixInput_contractPEPS_of_product_reference D A e Ψ Ω Ξ
    hΨ hΩ hΞ herror (δ := 0) (by simpa only [sub_zero] using hlower)
    hcompression (by norm_num)
  norm_num at h ⊢
  exact h

end TNLean.PEPS.Approximation.Pinned
