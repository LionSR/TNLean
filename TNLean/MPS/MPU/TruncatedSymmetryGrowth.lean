/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StaircaseGates

/-!
# Endpoint contraction and growth of truncated symmetries

The contraction in arXiv:2502.20257, `eq:truncsym` (lines 2062–2100), has
`N` bulk tensors, in addition to its two endpoint triangles. Rows are
(left source, bulk output, right source); columns are
(left physical, bulk input, right physical). The endpoint convention is
arXiv:1703.09188, equations `XY`, `SVDforms2`, and `uu` (lines 510–543).

**Scope restriction:** this file establishes only the endpoint contraction,
its zero-bulk value, and the source-factorization algebra of `eq:move_trunc_sym`
(arXiv:2502.20257, lines 2101–2174). It does not establish all-length unitarity,
the finite-group operator specialization, or the complementary movement equation.
No simplicity, unitarity, normalized Gram, or inverse-gauge premise is needed.
-/

open scoped BigOperators

namespace MPOTensor.SourceFactors

variable {d D : ℕ} {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}

/-- The endpoint contraction of arXiv:2502.20257, `eq:truncsym`, with `N`
bulk sites (not counting the two endpoint triangles). -/
noncomputable def truncatedSymmetry (S : SourceFactors U ρ) (N : ℕ) :
    Matrix (Fin ℓ[U] × (Fin N → Fin d) × Fin r[U])
      (Fin d × (Fin N → Fin d) × Fin d) ℂ :=
  fun (l, σ, r) (a, τ, b) ↦ ∑ α, ∑ β,
    S.Y₂ l (a, α) * evalWord U (List.ofFn σ) (List.ofFn τ) α β * S.Y₁ r (β, b)

/-- With no bulk sites, `eq:truncsym` is precisely the two-triangle gate
`sourceU` of arXiv:1703.09188, equation `uu` (lines 532–543). -/
@[simp] theorem truncatedSymmetry_zero (S : SourceFactors U ρ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (a b : Fin d)
    (σ τ : Fin 0 → Fin d) :
    S.truncatedSymmetry 0 (l, σ, r) (a, τ, b) = sourceU U S (l, r) (a, b) := by
  simp [truncatedSymmetry, Matrix.one_apply, mul_ite]

/-- Adding one bulk site at either end is contraction with the existing
source movement gates. This is the algebraic growth identity of
arXiv:2502.20257, `eq:move_trunc_sym` (lines 2101–2174), using only the
factorizations `X1Y1`, `X2Y2`, and `SVDforms2` of arXiv:1703.09188. -/
theorem truncatedSymmetry_cons_snoc (S : SourceFactors U ρ) {N : ℕ}
    (l : Fin ℓ[U]) (r : Fin r[U]) (i j a b c e : Fin d)
    (σ τ : Fin N → Fin d) :
    S.truncatedSymmetry (N + 2) (l, Fin.cons i (Fin.snoc σ j), r)
        (a, Fin.cons b (Fin.snoc τ c), e) =
      ∑ t, ∑ s, sourceWL U S (l, i) (a, t) *
        S.truncatedSymmetry N (t, σ, s) (b, τ, c) * sourceWR U S (j, r) (s, e) := by
  have hL (α : Fin D) :
      (∑ γ, S.Y₂ l (a, γ) * U i b γ α) =
        ∑ t, sourceWL U S (l, i) (a, t) * S.Y₂ t (b, α) := by
    simp only [sourceWL, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    rw [← X₂_mul_Y₂_apply U S γ i b α, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ ↦ (mul_assoc _ _ _).symm
  have hR (β : Fin D) :
      (∑ δ, U j c β δ * S.Y₁ r (δ, e)) =
        ∑ s, S.Y₁ s (β, c) * sourceWR U S (j, r) (s, e) := by
    simp only [sourceWR, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro δ _
    rw [← X₁_mul_Y₁_apply U S j δ β c, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ ↦ by ac_rfl
  simp only [truncatedSymmetry]
  rw [evalWord_ofFn_cons_snoc]
  trans ∑ α, ∑ β, (∑ γ, S.Y₂ l (a, γ) * U i b γ α) *
    evalWord U (List.ofFn σ) (List.ofFn τ) α β *
      (∑ δ, U j c β δ * S.Y₁ r (δ, e))
  · simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_last_first_four]
    refine Finset.sum_congr₂ fun α _ β _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr₂ fun δ _ γ _ ↦ by ac_rfl
  · simp_rw [hL, hR]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_last_first_four]
    exact Finset.sum_congr₂ fun t _ s _ ↦
      Finset.sum_congr₂ fun α _ β _ ↦ by ac_rfl

end MPOTensor.SourceFactors
