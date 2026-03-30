/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Transfer
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# MPO, MPDO, and LPDO — basic definitions

This file introduces the core tensor types and predicates for mixed-state
tensor networks, following arXiv:1606.00608 §4 (Cirac–Pérez-García–Schuch–
Verstraete):

* **MPO** (Matrix Product Operator): a 4-index tensor `MPOTensor d D` with
  physical ket/bra indices and virtual left/right indices.
* **MPDO** (Matrix Product Density Operator): an MPO whose operator family
  `mpo M N` is positive semidefinite for every system size `N`.
* **LPDO** (Locally Purifiable Density Operator): an MPO that admits a
  local MPS purification `M^{ij} = ∑_k A^{(i,k)} (A^{(j,k)})†`.

## Main definitions

* `MPOTensor d D`: the type of 4-index tensors (ket, bra, left-virtual,
  right-virtual).
* `MPOTensor.evalWord`: word evaluation for MPO tensors (product of 4-index
  matrices along a pair of ket/bra words).
* `MPOTensor.mpo`: the MPO operator family for system size `N`.
* `MPOTensor.transferMap`: the MPO transfer map
  `E_M(X) = ∑_{i,j} M^{ij} X (M^{ij})†`.
* `MPOTensor.IsHermitian`: local hermiticity predicate on the tensor.
* `MPOTensor.IsMPDO`: global positivity predicate.
* `MPOTensor.IsLPDO`: local purification predicate.
* `MPOTensor.toMPSTensor`: view an MPO tensor as an MPS tensor with doubled
  physical index `Fin (d * d)`.

## References

* [CPGSV17] arXiv:1606.00608, §4.1–4.3
* [VGRC04] Verstraete, Garcia-Ripoll, Cirac, PRL 93, 207204 (2004)
* [ZV04] Zwolak, Vidal, PRL 93, 207205 (2004)
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

/-- A (periodic, translation-invariant) **Matrix Product Operator** tensor:
a family of `D × D` matrices indexed by a ket index `i` and a bra index `j`,
both in `Fin d`.

Equivalently, this is an MPS tensor with doubled physical index `Fin d × Fin d`,
but we keep both indices explicit for clarity. -/
abbrev MPOTensor (d D : ℕ) := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPOTensor

variable {d D : ℕ}

/-! ### Conversion to MPS tensor with doubled physical index -/

/-- View an MPO tensor as an MPS tensor with doubled physical index
`Fin (d * d)`, where `Fin.divNat` gives the ket index and `Fin.modNat`
gives the bra index. -/
def toMPSTensor (M : MPOTensor d D) : MPSTensor (d * d) D :=
  fun ij => M (ij.divNat) (ij.modNat)

/-! ### Word evaluation -/

/-- Evaluate a pair of ket/bra words by multiplying the corresponding
4-index matrices: `M^{i₁ j₁} * M^{i₂ j₂} * ⋯ * M^{iₙ jₙ}`.
Returns `1` for the empty word pair, and `0` for mismatched lengths. -/
noncomputable def evalWord (M : MPOTensor d D) :
    List (Fin d) → List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [], [] => 1
  | i :: is, j :: js => M i j * evalWord M is js
  | _, _ => 0

@[simp] lemma evalWord_nil (M : MPOTensor d D) : evalWord M [] [] = 1 := rfl

@[simp] lemma evalWord_cons (M : MPOTensor d D)
    (i j : Fin d) (is js : List (Fin d)) :
    evalWord M (i :: is) (j :: js) = M i j * evalWord M is js := rfl

/-- Word evaluation on `List.ofFn` equals a non-commutative product:
`evalWord M (ofFn σ) (ofFn τ) = (ofFn (fun i => M (σ i) (τ i))).prod`. -/
lemma evalWord_ofFn (M : MPOTensor d D) {N : ℕ} (σ τ : Fin N → Fin d) :
    evalWord M (List.ofFn σ) (List.ofFn τ) =
      (List.ofFn fun i : Fin N => M (σ i) (τ i)).prod := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, evalWord_cons, List.prod_cons]
    congr 1
    exact ih (σ ∘ Fin.succ) (τ ∘ Fin.succ)

/-! ### The MPO operator family -/

/-- The `(σ, τ)` matrix entry of the MPO density operator for system size `N`:
`tr(M^{σ₀ τ₀} * M^{σ₁ τ₁} * ⋯ * M^{σ_{N-1} τ_{N-1}})`. -/
noncomputable def mpoMatrixEntry (M : MPOTensor d D) {N : ℕ}
    (σ τ : Fin N → Fin d) : ℂ :=
  Matrix.trace (evalWord M (List.ofFn σ) (List.ofFn τ))

/-- The **MPO operator family** for system size `N`: the operator
`ρ^{(N)}(M)` on `(ℂ^d)^{⊗N}` with matrix elements
`⟨σ|ρ^{(N)}|τ⟩ = tr(M^{σ₀ τ₀} ⋯ M^{σ_{N-1} τ_{N-1}})`.

This is the `d^N × d^N` matrix indexed by `Fin N → Fin d`. -/
noncomputable def mpo (M : MPOTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  Matrix.of fun σ τ => mpoMatrixEntry M σ τ

@[simp] lemma mpo_apply (M : MPOTensor d D) (N : ℕ)
    (σ τ : Fin N → Fin d) :
    mpo M N σ τ = mpoMatrixEntry M σ τ := rfl

/-! ### Hermiticity -/

/-- An MPO tensor is **Hermitian** if `M^{ij} = (M^{ji})†` for all `i, j`. -/
def IsHermitian (M : MPOTensor d D) : Prop :=
  ∀ i j : Fin d, M i j = (M j i)ᴴ

/-! ### Transfer map -/

/-- The **MPO transfer map** associated to an MPO tensor `M`:
$$E_M(X) = \sum_{i,j} M^{ij} \, X \, (M^{ij})^\dagger.$$ -/
noncomputable def transferMap (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (LinearMap.mulLeft ℂ (M i j)).comp (LinearMap.mulRight ℂ (M i j)ᴴ)

lemma transferMap_apply (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap M X = ∑ i : Fin d, ∑ j : Fin d, M i j * X * (M i j)ᴴ := by
  classical
  simp [transferMap, Matrix.mul_assoc]

/-- The MPO transfer map equals the MPS transfer map of the doubled-index tensor. -/
@[simp] lemma transferMap_eq_toMPSTensor (M : MPOTensor d D) :
    transferMap M = MPSTensor.transferMap (toMPSTensor M) := by
  refine LinearMap.ext fun X => ?_
  simp only [transferMap_apply, MPSTensor.transferMap_apply, toMPSTensor]
  rw [← Fintype.sum_prod_type']
  exact (finProdFinEquiv.symm.sum_comp _).symm

/-- The transfer map of an MPO preserves positive semidefiniteness. -/
theorem transferMap_pos (M : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) :
    (transferMap M X).PosSemidef := by
  rw [transferMap_eq_toMPSTensor]
  exact MPSTensor.transferMap_pos (toMPSTensor M) hX

/-! ### MPDO: global positivity -/

/-- An MPO tensor `M` is an **MPDO** (Matrix Product Density Operator) if
it generates positive semidefinite operators for all system sizes:
`ρ^{(N)}(M) ≥ 0` for all `N`.

See arXiv:1606.00608, §4. -/
def IsMPDO (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, (mpo M N).PosSemidef

/-! ### LPDO: local purification -/

/-- An MPO tensor `M` is an **LPDO** (Locally Purifiable Density Operator) if
there exists an MPS tensor `A` with an enlarged physical index `Fin d × Fin dK`
(where `dK` is the Kraus/ancilla dimension) such that

  `M^{ij} = ∑_k A^{(i,k)} (A^{(j,k)})†`

for all physical indices `i, j`. This is the local purification condition
of Verstraete–Garcia-Ripoll–Cirac (2004).

Not every MPDO is an LPDO (De las Cuevas et al. 2016). -/
def IsLPDO (M : MPOTensor d D) : Prop :=
  ∃ (dK : ℕ) (A : Fin d → Fin dK → Matrix (Fin D) (Fin D) ℂ),
    ∀ i j : Fin d, M i j = ∑ k : Fin dK, A i k * (A j k)ᴴ

/-- An LPDO tensor is automatically Hermitian. -/
theorem IsLPDO.isHermitian {M : MPOTensor d D} (h : IsLPDO M) :
    IsHermitian M := by
  obtain ⟨dK, A, hA⟩ := h
  intro i j
  rw [hA i j, hA j i, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- **TODO** (part 4/5): LPDO implies MPDO. -/
theorem IsLPDO.isMPDO {M : MPOTensor d D} (h : IsLPDO M) : IsMPDO M := by
  sorry

end MPOTensor
