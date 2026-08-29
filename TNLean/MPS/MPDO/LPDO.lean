/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.MPS.MPDO.Defs

/-!
# Locally purifiable density operators

This file defines locally purifiable density operators and proves that every
local purification generates positive semidefinite operators on nonempty
chains. The local purification is the Kronecker-product presentation from
arXiv:1606.00608, Section 4.3.

## Main definitions

* `MPOTensor.IsLPDO`: an MPO tensor admitting a local purification tensor.

## Main results

* `MPOTensor.lpdo_prod_decomp`: products of LPDO entries decompose as sums of
  Kronecker products of purifying-tensor products.
* `MPOTensor.IsLPDO.isMPDO`: every LPDO is an MPDO.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.3
-/

open scoped Matrix ComplexOrder BigOperators Kronecker
open Matrix Finset

namespace MPOTensor

variable {d D : ℕ}

/-! ### LPDO: local purification -/

/-- An MPO tensor `M` is an **LPDO** (Locally Purifiable Density Operator) if
there exist a Kraus dimension `dK`, an inner bond dimension `D'`, a purifying
family `A^{(i,k)} ∈ M_{D'}(ℂ)` for `i ∈ Fin d`, `k ∈ Fin dK`, and a bond-space
identification `e : Fin D ≃ Fin D' × Fin D'` such that

  `M^{ij} = (∑_{k} A^{(i,k)} ⊗ₖ (A^{(j,k)})^*).submatrix ↑e ↑e`

for all `i, j`, where `(·)^*` is entrywise complex conjugation and `⊗ₖ` is the
Kronecker product. See arXiv:1606.00608, Section 4.3. -/
def IsLPDO (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e

/-- The list product of LPDO tensor entries decomposes via Kronecker products
of the purifying tensor. This is the key technical lemma for `IsLPDO.isMPDO` and
for the purification identity `mpo_eq_purificationDensity`: the product of
Kronecker sums expands as a Kronecker sum of products, using the mixed-product
property `(A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)`. -/
lemma lpdo_prod_decomp {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D')
    {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    {N : ℕ} (σ τ : Fin N → Fin d) :
    (List.ofFn fun l => M (σ l) (τ l)).prod =
      (∑ κ : Fin N → Fin dK,
        (List.ofFn fun l => A (σ l) (κ l)).prod ⊗ₖ
        ((List.ofFn fun l => A (τ l) (κ l)).prod).map
          (starRingEnd ℂ)).submatrix ↑e ↑e := by
  induction N with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Fintype.sum_unique]
    have h1 : (1 : Matrix (Fin D') (Fin D') ℂ).map ⇑(starRingEnd ℂ) = 1 :=
      (starRingEnd ℂ).mapMatrix.map_one
    rw [h1, Matrix.kroneckerMap_one_one (· * ·) (fun _ => zero_mul _)
      (fun _ => mul_zero _) (one_mul 1), Matrix.submatrix_one_equiv]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [hM (σ 0) (τ 0)]
    have ih_step := ih (σ ∘ Fin.succ) (τ ∘ Fin.succ)
    simp only [Function.comp_def] at ih_step
    rw [ih_step, Matrix.submatrix_mul_equiv _ _ (↑e) e (↑e)]
    -- Strip the submatrix to work at the (Fin D' × Fin D') level
    congr 1
    -- Expand LHS product of sums
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    -- Apply mixed product property
    simp_rw [← Matrix.mul_kronecker_mul]
    -- Combine the conjugated matrices: map star (A) * map star (B) = map star (A * B)
    have map_star_mul : ∀ (P Q : Matrix (Fin D') (Fin D') ℂ),
        P.map ⇑(starRingEnd ℂ) * Q.map ⇑(starRingEnd ℂ) =
        (P * Q).map ⇑(starRingEnd ℂ) :=
      fun P Q => ((starRingEnd ℂ).mapMatrix.map_mul P Q).symm
    simp_rw [map_star_mul]
    -- Reindex RHS: ∑ κ : Fin(n+1) → Fin dK = ∑ k, ∑ κ'
    have reindex : ∀ (F : (Fin (n + 1) → Fin dK) →
        Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ),
      ∑ κ, F κ = ∑ k : Fin dK, ∑ κ' : Fin n → Fin dK,
        F (Fin.cons k κ') := fun F => by
          rw [← Fintype.sum_prod_type']
          exact ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin dK)).sum_comp F).symm
    symm
    rw [reindex]
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- **LPDO implies MPDO**: every LPDO tensor generates positive semidefinite
density operators on all nonempty chains.

The proof uses the Kronecker product structure: the N-site density matrix
decomposes as `ρ^{(N)} = ∑_κ |ψ_κ⟩⟨ψ_κ|` where each `ψ_κ` is an MPS
vector built from the purifying tensor, giving a manifestly PSD sum of
rank-1 positive semidefinite matrices.

See arXiv:1606.00608, Section 4.3. -/
theorem IsLPDO.isMPDO {M : MPOTensor d D} (h : IsLPDO M) : IsMPDO M := by
  obtain ⟨dK, D', A, e, hM⟩ := h
  intro N _hN
  -- Define the MPS coefficient vectors from the purifying tensor
  set ψ : (Fin N → Fin dK) → (Fin N → Fin d) → ℂ :=
    fun κ σ => Matrix.trace ((List.ofFn fun l => A (σ l) (κ l)).prod) with hψ
  -- Show mpo M N = ∑ κ, |ψ_κ⟩⟨ψ_κ|, then conclude PSD
  suffices hmpo : mpo M N = ∑ κ : Fin N → Fin dK,
      Matrix.vecMulVec (ψ κ) (star (ψ κ)) by
    rw [hmpo]
    exact Matrix.posSemidef_sum _ fun κ _ => Matrix.posSemidef_vecMulVec_self_star _
  -- Prove the matrix equality entry-by-entry
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, hψ, evalWord_ofFn]
  -- Apply the Kronecker product decomposition
  rw [lpdo_prod_decomp A e hM σ τ]
  -- trace of submatrix = trace (via equiv reindexing)
  have trace_sub : ∀ (X : Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ),
      Matrix.trace (X.submatrix (↑e) (↑e)) = Matrix.trace X := by
    intro X; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact e.sum_comp (fun p => X p p)
  rw [trace_sub, Matrix.trace_sum]
  simp_rw [Matrix.trace_kronecker]
  -- trace of entrywise conjugate = conjugate of trace: trace(A.map star) = star(trace A)
  simp_rw [← AddMonoidHom.map_trace (starRingEnd ℂ)]
  -- Evaluate the entries of the finite sum of rank-one matrices.
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]


end MPOTensor
