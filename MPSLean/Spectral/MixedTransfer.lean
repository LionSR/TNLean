/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.Transfer

/-!
# Mixed transfer operator and iterated word formulae

The **mixed (or cross) transfer operator** for two MPS tensors `A` and `B`:
$$F_{AB}(X) = \sum_i A^i \, X \, (B^i)^\dagger$$

When `A = B`, this reduces to the standard transfer map `E_A`.
The mixed transfer operator encodes all cross-correlations between two
MPS tensors and is the key tool for proving block separation in the
multi-block fundamental theorem.

## Main results

* `mixedTransferMap`: definition of `F_{AB}`
* `mixedTransferMap_self`: `F_{AA} = E_A`
* `mixedTransferMap_pow_apply`: `F_{AB}^N(X) = ∑_σ w_A(σ) X w_B(σ)†`
* `trace_mixedTransferMap_pow_identity`: trace formula for MPV cross-correlations

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Mixed transfer operator -/

section MixedTransfer

/-- The **mixed transfer operator** for MPS tensors `A` and `B`:
$$F_{AB}(X) = \sum_i A^i \, X \, (B^i)^\dagger.$$
This is a linear map on `D × D` complex matrices. When `A = B`, it
recovers the standard transfer map `transferMap A`. -/
noncomputable def mixedTransferMap (A B : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d,
    (LinearMap.mulLeft ℂ (A i)).comp (LinearMap.mulRight ℂ (B i)ᴴ)

/-- Explicit formula for the mixed transfer operator. -/
@[simp]
lemma mixedTransferMap_apply (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    mixedTransferMap A B X = ∑ i : Fin d, A i * X * (B i)ᴴ := by
  classical
  simp [mixedTransferMap, Matrix.mul_assoc]

/-- The mixed transfer operator with `A = B` is the standard transfer map. -/
theorem mixedTransferMap_self (A : MPSTensor d D) :
    mixedTransferMap A A = transferMap (d := d) (D := D) A := by
  ext X
  simp [mixedTransferMap_apply, transferMap_apply]

/-- Linearity of the mixed transfer operator in the first argument: if we
scale the first tensor, the map scales linearly. -/
lemma mixedTransferMap_smul_left (c : ℂ) (A B : MPSTensor d D) :
    mixedTransferMap (fun i => c • A i) B = c • mixedTransferMap A B := by
  ext X
  simp only [mixedTransferMap_apply, LinearMap.smul_apply, Matrix.smul_mul]
  rw [← Finset.smul_sum]

/-- Linearity of the mixed transfer operator in the second argument (with conjugation):
scaling B by c conjugates the scalar. -/
lemma mixedTransferMap_smul_right (c : ℂ) (A B : MPSTensor d D) :
    mixedTransferMap A (fun i => c • B i) = starRingEnd ℂ c • mixedTransferMap A B := by
  ext X : 1
  simp only [mixedTransferMap_apply, Matrix.conjTranspose_smul, LinearMap.smul_apply]
  -- Goal: ∑ i, A i * X * (star c • (B i)ᴴ) = starRingEnd ℂ c • ∑ i, A i * X * (B i)ᴴ
  -- Note: star c and (starRingEnd ℂ) c are definitionally equal for ℂ
  simp only [starRingEnd_apply]
  rw [Finset.smul_sum]; congr 1; ext i
  rw [Matrix.mul_smul]

end MixedTransfer

/-! ## Iterated mixed transfer and MPV cross-correlations

The key bridge: iterating the mixed transfer operator `N` times connects
to sums over all words of length `N` of products of word evaluations.
This is the operator-level encoding of the inner product structure
of the MPV spaces.
-/

section IteratedTransfer

/-- Iterating the mixed transfer operator `N` times gives:
$$F_{AB}^N(X) = \sum_{\sigma : \mathrm{Fin}\,N \to \mathrm{Fin}\,d}
  \mathrm{evalWord}(A, \sigma) \cdot X \cdot \mathrm{evalWord}(B, \sigma)^\dagger$$

This connects the spectral theory of the transfer operator to the
combinatorial structure of word evaluations, and hence to MPV coefficients.

**Proof sketch:** By induction on `N`.
- Base case: `F^0(X) = X` and the sum over `Fin 0 → Fin d` has one term
  (the empty word), with `evalWord A [] = 1`.
- Inductive step: Expanding `F^{N+1}(X) = F(F^N(X))`, substitute the
  inductive hypothesis and use that `evalWord A (i :: σ_list)` factors as
  `A i * evalWord A σ_list`. -/
lemma sum_fin_succ_eq {n d : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (n + 1) → Fin d) → M) :
    ∑ σ : Fin (n + 1) → Fin d, f σ =
    ∑ i : Fin d, ∑ τ : Fin n → Fin d, f (Fin.cons i τ) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin d)).symm _ _
    (fun σ => by simp [Fin.consEquiv, Fin.cons_self_tail])

theorem mixedTransferMap_pow_apply (A B : MPSTensor d D) (N : ℕ) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ((mixedTransferMap A B) ^ N) X =
        ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ := by
  induction N with
  | zero =>
    intro X
    simp [evalWord, Finset.univ_unique]
  | succ n ih =>
    intro X
    -- F^{n+1}(X) = F(F^n(X))
    rw [pow_succ']
    change mixedTransferMap A B (((mixedTransferMap A B) ^ n) X) = _
    rw [ih]
    -- Distribute F over the sum, then swap summation order
    simp only [mixedTransferMap_apply, map_sum]
    rw [Finset.sum_comm]
    -- Re-index the RHS using Fin.cons decomposition
    rw [sum_fin_succ_eq]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro τ _
    simp only [List.ofFn_cons, evalWord, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Specialization to the diagonal case**: iterating the standard
transfer map gives the sum over word evaluations. This improves on
`transferMap_pow_eq_blocked` by providing it as a corollary. -/
theorem transferMap_pow_apply' (A : MPSTensor d D) (N : ℕ) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ((transferMap (d := d) (D := D) A) ^ N) X =
        ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) * X * (evalWord A (List.ofFn σ))ᴴ := by
  rw [← mixedTransferMap_self]
  exact mixedTransferMap_pow_apply A A N

/-- **Trace of iterated mixed transfer encodes MPV cross-correlations.**

For `X = 1`:
$$\mathrm{tr}(F_{AB}^N(1)) = \sum_\sigma \mathrm{tr}(\mathrm{evalWord}(A,\sigma)
  \cdot \mathrm{evalWord}(B,\sigma)^\dagger)$$

This is the key quantity for detecting whether two MPS tensors produce the
same (or different) physical states. -/
theorem trace_mixedTransferMap_pow_identity (A B : MPSTensor d D) (N : ℕ) :
    Matrix.trace (((mixedTransferMap A B) ^ N) (1 : Matrix (Fin D) (Fin D) ℂ)) =
      ∑ σ : Fin N → Fin d,
        Matrix.trace (evalWord A (List.ofFn σ) * (evalWord B (List.ofFn σ))ᴴ) := by
  rw [mixedTransferMap_pow_apply]
  simp

/-- **MPV inner product via trace**: when `D = 1` (or more generally when
the trace factors), the cross-correlation simplifies to the inner product
of MPV coefficients. For general `D`, the trace of the word product
doesn't factor, but the formula still captures the relevant overlap. -/
theorem mpv_inner_product_via_trace (A B : MPSTensor d D) (N : ℕ)
    (σ : Fin N → Fin d) :
    Matrix.trace (evalWord A (List.ofFn σ) * (evalWord B (List.ofFn σ))ᴴ) =
      ∑ j : Fin D, ∑ k : Fin D,
        (evalWord A (List.ofFn σ) j k) * starRingEnd ℂ (evalWord B (List.ofFn σ) j k) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]

end IteratedTransfer

end MPSTensor
