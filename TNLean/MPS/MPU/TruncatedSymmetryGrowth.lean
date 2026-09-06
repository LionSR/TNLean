/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StaircaseGates

/-!
# Endpoint contraction and growth of truncated symmetries

The contraction in arXiv:2502.20257, `eq:truncsym` (lines 2062–2100), has
`N` bulk tensors, in addition to its two endpoint triangles. The source counts
both endpoints in the total length $L=N+2\geq2$ (`eq:truncsym`, lines 2094–2097;
CZX display, lines 4700–4713). Thus the bulk-indexed contraction here corresponds
to $U_g^{N+2}$ in the source, not $U_g^N$; zero bulk has total length two. Rows are
(left source, bulk output, right source); columns are
(left physical, bulk input, right physical). The endpoint convention is
arXiv:1703.09188, equations `XY`, `SVDforms2`, and `uu` (lines 510–543).

**Scope restriction (endpoint contraction and growth):** this file establishes
only the endpoint contraction, its zero-bulk value, and the source-factorization
algebra of `eq:move_trunc_sym` (arXiv:2502.20257, lines 2101–2174).
All-length endpoint-coordinate unitarity is established separately in
`TruncatedSymmetryUnitarity`; this algebraic growth layer does not import that
unitarity layer. This file does not establish the finite-group operator
specialization or the complementary finite-chain relation. Documented in
`docs/paper-gaps/fbc25_truncated_symmetry_endpoint_unitarity_scope.tex`.
The raw endpoint API requires no simplicity, unitarity, normalized Gram, or
inverse-gauge premise: zero bulk needs no factorization, left growth needs
only the second cut factorization, and two-sided growth needs both. The
`SourceFactors` results are specializations to the supplied normalized factors;
no unitarity claim is made for arbitrary factors.
-/

open scoped BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The endpoint contraction of arXiv:2502.20257, `eq:truncsym`, with `N`
bulk sites (not counting the two endpoint triangles). The source total length
is $L=N+2\geq2$, so its length notation is $U_g^{N+2}$, not $U_g^N$
(lines 2094–2097). The parameter `N` remains the bulk count. -/
noncomputable def truncatedSymmetryOfEndpoints (U : MPOTensor d D)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ) (N : ℕ) :
    Matrix (Fin ℓ[U] × (Fin N → Fin d) × Fin r[U])
      (Fin d × (Fin N → Fin d) × Fin d) ℂ :=
  fun (l, σ, r) (a, τ, b) ↦ ∑ α, ∑ β,
    Y₂ l (a, α) * evalWord U (List.ofFn σ) (List.ofFn τ) α β * Y₁ r (β, b)

/-- With no bulk sites (`N = 0`), the source total length is two, not zero.
At this length, `eq:truncsym` is precisely the two-triangle gate
`sourceU` of arXiv:1703.09188, equation `uu` (lines 532–543). -/
@[simp] theorem truncatedSymmetryOfEndpoints_zero (U : MPOTensor d D)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (a b : Fin d)
    (σ τ : Fin 0 → Fin d) :
    truncatedSymmetryOfEndpoints U Y₂ Y₁ 0 (l, σ, r) (a, τ, b) =
      ∑ α, Y₂ l (a, α) * Y₁ r (α, b) := by
  simp [truncatedSymmetryOfEndpoints, Matrix.one_apply, mul_ite]

/-- Two-sided growth for four explicit matrices, assuming only the two cut
factorizations. Total length grows from $N+2$ to $N+4$.
The crossed contractions are the movement gates of FBC25,
`eq:wLR` (lines 811–869). This is the algebraic identity of FBC25,
`eq:move_trunc_sym` (lines 2101–2174), using CPSV17 `eq:sf-svd`, `X1Y1`,
`X2Y2`, and `SVDforms2` (lines 479–530), not their normalization or inverses. -/
theorem truncatedSymmetryOfEndpoints_cons_snoc (U : MPOTensor d D)
    (X₁ : Matrix (Fin d × Fin D) (Fin r[U]) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (hfac1 : sourceCutM₁ U = X₁ * Y₁)
    (hfac2 : sourceCutM₂ U = X₂ * Y₂) {N : ℕ}
    (l : Fin ℓ[U]) (r : Fin r[U]) (i j a b c e : Fin d)
    (σ τ : Fin N → Fin d) :
    truncatedSymmetryOfEndpoints U Y₂ Y₁ (N + 2) (l, Fin.cons i (Fin.snoc σ j), r)
        (a, Fin.cons b (Fin.snoc τ c), e) =
      ∑ t, ∑ s, (∑ γ, Y₂ l (a, γ) * X₂ (γ, i) t) *
        truncatedSymmetryOfEndpoints U Y₂ Y₁ N (t, σ, s) (b, τ, c) *
          (∑ δ, X₁ (j, δ) s * Y₁ r (δ, e)) := by
  let wL := fun t ↦ ∑ γ, Y₂ l (a, γ) * X₂ (γ, i) t
  let wR := fun s ↦ ∑ δ, X₁ (j, δ) s * Y₁ r (δ, e)
  change _ = ∑ t, ∑ s, wL t *
    truncatedSymmetryOfEndpoints U Y₂ Y₁ N (t, σ, s) (b, τ, c) * wR s
  have hentry1 (i : Fin d) (β α : Fin D) (j : Fin d) :
      (X₁ * Y₁) (i, β) (α, j) = U i j α β := by
    rw [← hfac1]
    rfl
  have hentry2 (α : Fin D) (i j : Fin d) (β : Fin D) :
      (X₂ * Y₂) (α, i) (j, β) = U i j α β := by
    rw [← hfac2]
    rfl
  have hL (α : Fin D) :
      (∑ γ, Y₂ l (a, γ) * U i b γ α) =
        ∑ t, wL t * Y₂ t (b, α) := by
    simp only [wL, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    rw [← hentry2 γ i b α, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ ↦ (mul_assoc _ _ _).symm
  have hR (β : Fin D) :
      (∑ δ, U j c β δ * Y₁ r (δ, e)) =
        ∑ s, Y₁ s (β, c) * wR s := by
    simp only [wR, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro δ _
    rw [← hentry1 j δ β c, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ ↦ by ac_rfl
  simp only [truncatedSymmetryOfEndpoints]
  rw [evalWord_ofFn_cons_snoc]
  trans ∑ α, ∑ β, (∑ γ, Y₂ l (a, γ) * U i b γ α) *
    evalWord U (List.ofFn σ) (List.ofFn τ) α β *
      (∑ δ, U j c β δ * Y₁ r (δ, e))
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

/-- Left growth needs only the second cut factorization; the right endpoint
is arbitrary and unchanged. Total length grows from $N+2$ to $N+3$.
The inline crossed contraction is FBC25 `eq:wLR`
(lines 811–869). This is the left-end step of `eq:move_trunc_sym`
(lines 2101–2174), using CPSV17 `X2Y2` and `SVDforms2` (lines 479–530). -/
theorem truncatedSymmetryOfEndpoints_cons (U : MPOTensor d D)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (hfac2 : sourceCutM₂ U = X₂ * Y₂) {N : ℕ}
    (l : Fin ℓ[U]) (r : Fin r[U]) (i a b c : Fin d)
    (σ τ : Fin N → Fin d) :
    truncatedSymmetryOfEndpoints U Y₂ Y₁ (N + 1) (l, Fin.cons i σ, r) (a, Fin.cons b τ, c) =
      ∑ t, (∑ γ, Y₂ l (a, γ) * X₂ (γ, i) t) *
        truncatedSymmetryOfEndpoints U Y₂ Y₁ N (t, σ, r) (b, τ, c) := by
  let wL := fun t ↦ ∑ γ, Y₂ l (a, γ) * X₂ (γ, i) t
  change _ = ∑ t, wL t * truncatedSymmetryOfEndpoints U Y₂ Y₁ N (t, σ, r) (b, τ, c)
  have hentry2 (α : Fin D) (i j : Fin d) (β : Fin D) :
      (X₂ * Y₂) (α, i) (j, β) = U i j α β := by
    rw [← hfac2]
    rfl
  simp only [truncatedSymmetryOfEndpoints, List.ofFn_cons, evalWord_cons, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_reverse_three]
  symm
  simp only [wL, Finset.sum_mul]
  rw [Fintype.sum_reverse_three, Finset.sum_comm]
  refine Finset.sum_congr₂ fun α _ β _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [← hentry2 γ i b α, Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ ↦ by ac_rfl

namespace SourceFactors

variable {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}

/-- The endpoint contraction of arXiv:2502.20257, `eq:truncsym`, with `N`
bulk sites (not counting the two endpoint triangles). The source total length
is $L=N+2\geq2$, so its length notation is $U_g^{N+2}$, not $U_g^N$
(lines 2094–2097). The parameter `N` remains the bulk count. -/
noncomputable def truncatedSymmetry (S : SourceFactors U ρ) (N : ℕ) :
    Matrix (Fin ℓ[U] × (Fin N → Fin d) × Fin r[U])
      (Fin d × (Fin N → Fin d) × Fin d) ℂ :=
  truncatedSymmetryOfEndpoints U S.Y₂ S.Y₁ N

/-- With no bulk sites (`N = 0`), the source total length is two, not zero.
At this length, `eq:truncsym` is precisely the two-triangle gate
`sourceU` of arXiv:1703.09188, equation `uu` (lines 532–543). -/
@[simp] theorem truncatedSymmetry_zero (S : SourceFactors U ρ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (a b : Fin d)
    (σ τ : Fin 0 → Fin d) :
    S.truncatedSymmetry 0 (l, σ, r) (a, τ, b) = sourceU U S (l, r) (a, b) := by
  exact truncatedSymmetryOfEndpoints_zero U S.Y₂ S.Y₁ l r a b σ τ

/-- Adding one bulk site at either end is contraction with the existing
source movement gates. Total length grows from $N+2$ to $N+4$.
This is the algebraic growth identity of
arXiv:2502.20257, `eq:move_trunc_sym` (lines 2101–2174), using only the
factorizations `X1Y1`, `X2Y2`, and `SVDforms2` of arXiv:1703.09188. -/
theorem truncatedSymmetry_cons_snoc (S : SourceFactors U ρ) {N : ℕ}
    (l : Fin ℓ[U]) (r : Fin r[U]) (i j a b c e : Fin d)
    (σ τ : Fin N → Fin d) :
    S.truncatedSymmetry (N + 2) (l, Fin.cons i (Fin.snoc σ j), r)
        (a, Fin.cons b (Fin.snoc τ c), e) =
      ∑ t, ∑ s, sourceWL U S (l, i) (a, t) *
        S.truncatedSymmetry N (t, σ, s) (b, τ, c) * sourceWR U S (j, r) (s, e) := by
  exact truncatedSymmetryOfEndpoints_cons_snoc U S.X₁ S.Y₁ S.X₂ S.Y₂
    S.sourceCutM₁_eq S.sourceCutM₂_eq l r i j a b c e σ τ

/-- Adding one bulk site on the left is contraction with the left movement
gate. Total length grows from $N+2$ to $N+3$.
This is the left-end source-factorization step in arXiv:2502.20257,
`eq:move_trunc_sym` (lines 2101–2174), with the right endpoint unchanged. -/
theorem truncatedSymmetry_cons (S : SourceFactors U ρ) {N : ℕ}
    (l : Fin ℓ[U]) (r : Fin r[U]) (i a b c : Fin d)
    (σ τ : Fin N → Fin d) :
    S.truncatedSymmetry (N + 1) (l, Fin.cons i σ, r) (a, Fin.cons b τ, c) =
      ∑ t, sourceWL U S (l, i) (a, t) *
        S.truncatedSymmetry N (t, σ, r) (b, τ, c) := by
  exact truncatedSymmetryOfEndpoints_cons U S.Y₁ S.X₂ S.Y₂
    S.sourceCutM₂_eq l r i a b c σ τ

end SourceFactors
end MPOTensor
