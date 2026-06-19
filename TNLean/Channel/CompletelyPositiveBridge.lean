/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Bridge from Kraus positivity to Mathlib's completely positive maps

This file connects TNLean's concrete Kraus-operator notion of complete positivity
(`IsCPMap`) to Mathlib's abstract C⋆-algebra type `CompletelyPositiveMap`.

A completely positive map in TNLean is a linear map `E : M_D(ℂ) →ₗ[ℂ] M_D(ℂ)`
admitting a Kraus representation `E(X) = ∑ᵢ Kᵢ X Kᵢ†` (`IsCPMap`).  Mathlib's
`CompletelyPositiveMap A₁ A₂` requires that, for every `k`, applying the map
entrywise to a positive `k × k` matrix over `A₁` yields a positive matrix over
`A₂`.  Identifying `M_D(ℂ)` with the C⋆-algebra `CStarMatrix (Fin D) (Fin D) ℂ`,
the entrywise image of a positive block matrix `M` under a single Kraus term
`X ↦ Kᵢ X Kᵢ†` equals the conjugation `dᵢ * M * dᵢ†` by the block-diagonal matrix
`dᵢ` carrying `Kᵢ` on every diagonal entry.  Conjugation preserves positivity
(`star_right_conjugate_nonneg`), and a finite sum of positive elements is positive.

The bridge makes the Kraus/Stinespring characterisation already formalised in
`TNLean/Channel/` visible to Mathlib's abstract positive-map and
completely-positive-map API, without discarding the concrete finite-dimensional
channel interface used for Wolf-style theorems.

## Main results

* `IsCPMap.map_cstarMatrix_nonneg` — the entrywise complete-positivity inequality.
* `IsCPMap.toCompletelyPositiveMap` — packages an `IsCPMap` as a Mathlib
  `CompletelyPositiveMap`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.1][Wolf2012QChannels]
-/

open scoped Matrix CStarAlgebra ComplexOrder MatrixOrder
open Matrix

variable {D : ℕ}

namespace IsCPMap

/-- The block-diagonal `k × k` matrix over `M_D(ℂ)` carrying the operator `W`
on every diagonal entry.  Conjugation of a block matrix by this element realises
the entrywise action of the single Kraus term `X ↦ W * X * Wᴴ`. -/
private def blockDiagConst (k : ℕ) (W : Matrix (Fin D) (Fin D) ℂ) :
    CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin D) (Fin D) ℂ) :=
  Matrix.diagonal (fun _ : Fin k => CStarMatrix.ofMatrix W)

private lemma blockDiagConst_apply (k : ℕ) (W : Matrix (Fin D) (Fin D) ℂ) (a b : Fin k) :
    blockDiagConst k W a b = if a = b then CStarMatrix.ofMatrix W else 0 := by
  simp [blockDiagConst, Matrix.diagonal_apply]

private lemma star_blockDiagConst_apply (k : ℕ) (W : Matrix (Fin D) (Fin D) ℂ) (a b : Fin k) :
    star (blockDiagConst k W) a b = if a = b then star (CStarMatrix.ofMatrix W) else 0 := by
  rw [CStarMatrix.star_apply, blockDiagConst_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]

/-- Conjugating a block matrix `M` by `blockDiagConst k W` acts entrywise as the
single Kraus term `X ↦ W * X * Wᴴ`. -/
private lemma conjugate_blockDiagConst_apply (k : ℕ) (W : Matrix (Fin D) (Fin D) ℂ)
    (M : CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin D) (Fin D) ℂ)) (a b : Fin k) :
    (blockDiagConst k W * M * star (blockDiagConst k W)) a b
      = CStarMatrix.ofMatrix W * M a b * star (CStarMatrix.ofMatrix W) := by
  classical
  simp only [CStarMatrix.mul_apply, blockDiagConst_apply, star_blockDiagConst_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Entrywise evaluation commutes with finite sums of `CStarMatrix` values. -/
private lemma cstar_sum_apply {ι m nn A : Type*} [AddCommMonoid A] (s : Finset ι)
    (G : ι → CStarMatrix m nn A) (a : m) (b : nn) :
    (∑ i ∈ s, G i) a b = ∑ i ∈ s, G i a b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, CStarMatrix.add_apply, ih]

/-- A linear self-map of `M_D(ℂ)`, reinterpreted as a linear self-map of the
C⋆-algebra `CStarMatrix (Fin D) (Fin D) ℂ` (the two types are definitionally
equal). -/
def cstarMap (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    CStarMatrix (Fin D) (Fin D) ℂ →ₗ[ℂ] CStarMatrix (Fin D) (Fin D) ℂ := E

@[simp] lemma cstarMap_apply
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : CStarMatrix (Fin D) (Fin D) ℂ) : cstarMap E X = E X := rfl

/-- For a Kraus family `K`, the entrywise image of a block matrix `M` under
`E(X) = ∑ᵢ Kᵢ X Kᵢ†` is the sum of conjugations by the block-diagonal Kraus
matrices. -/
private lemma map_eq_sum_conjugate
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    {r : ℕ} {K : Fin r → Matrix (Fin D) (Fin D) ℂ}
    (hK : ∀ X, E X = ∑ i, K i * X * (K i)ᴴ) (k : ℕ)
    (M : CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin D) (Fin D) ℂ)) :
    M.map (cstarMap E)
      = ∑ i, blockDiagConst k (K i) * M * star (blockDiagConst k (K i)) := by
  have hmap : M.map (cstarMap E)
      = M.map fun X =>
        ∑ i, CStarMatrix.ofMatrix (K i) * X * star (CStarMatrix.ofMatrix (K i)) := by
    apply CStarMatrix.ext
    intro a b
    rw [CStarMatrix.map_apply, CStarMatrix.map_apply, cstarMap_apply, hK]
    rfl
  rw [hmap]
  apply CStarMatrix.ext
  intro a b
  rw [CStarMatrix.map_apply, cstar_sum_apply]
  simp only [conjugate_blockDiagConst_apply]

/-- **Kraus complete positivity, entrywise form.** If `E` is completely positive
(admits a Kraus representation), then applying `E` entrywise to a positive block
matrix over `M_D(ℂ)` yields a positive block matrix.  This is the defining
property of a Mathlib `CompletelyPositiveMap`. -/
theorem map_cstarMatrix_nonneg
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} (hE : IsCPMap E)
    (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin D) (Fin D) ℂ))
    (hM : 0 ≤ M) : 0 ≤ M.map (cstarMap E) := by
  obtain ⟨r, K, hK⟩ := hE
  rw [map_eq_sum_conjugate hK k M]
  exact Finset.sum_nonneg fun i _ =>
    star_right_conjugate_nonneg hM (blockDiagConst k (K i))

/-- **Bridge to Mathlib's `CompletelyPositiveMap`.** A TNLean completely positive
map (`IsCPMap`, defined through a Kraus representation) is a Mathlib completely
positive map on `CStarMatrix (Fin D) (Fin D) ℂ`. -/
def toCompletelyPositiveMap
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} (hE : IsCPMap E) :
    CStarMatrix (Fin D) (Fin D) ℂ →CP CStarMatrix (Fin D) (Fin D) ℂ where
  toLinearMap := cstarMap E
  map_cstarMatrix_nonneg' k M hM := hE.map_cstarMatrix_nonneg k M hM

end IsCPMap
