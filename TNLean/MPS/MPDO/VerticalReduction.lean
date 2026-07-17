/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosureDecomposition
import TNLean.MPS.MPDO.HorizontalBNT

/-!
# Reducing sectors of the vertically viewed tensor

This file carries the invariant-projection argument of arXiv:1606.00608,
Proposition 4.13, lines 1873--1887, into the general canonical-form
decomposition at lines 200--225 and 253--255.

For a tensor in horizontal canonical form that generates matrix product
density operators, every one-sided invariant orthogonal projection of the
vertically viewed tensor is reducing. The general decomposition under this
closure condition then gives complete pairwise orthogonal physical sectors,
their exact corner tensors, and both intertwining identities. No spectral
normalization or grouping into a basis of normal tensors is asserted here.

## Main results

* `MPOTensor.IsHorizontalCF.hasInvariantProjectorClosure_verticalTensor`:
  every one-sided invariant orthogonal projection of the vertically viewed
  tensor is reducing.
* `MPOTensor.IsHorizontalCF.exists_irreducible_verticalBlockDecomp_with_isometry`:
  the physical space splits into complete orthogonal irreducible reducing
  sectors for the vertically viewed tensor.
* `MPOTensor.IsHorizontalCF.exists_complete_verticalReducingProjectors`:
  the range projections of these sectors are complete, pairwise orthogonal,
  and commute with every vertical letter.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Every invariant orthogonal projection of the vertically viewed tensor is
reducing for an MPO tensor in horizontal canonical form that generates matrix
product density operators.

This is the conclusion of the invariant-projection argument in
arXiv:1606.00608, Proposition 4.13, lines 1873--1887. The left-invariance
identity is translated to the one-site MPO actions, the horizontal Lemma L
reduction gives right invariance, and the result is translated back to the
vertically viewed tensor. -/
theorem IsHorizontalCF.hasInvariantProjectorClosure_verticalTensor
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    MPSTensor.HasInvariantProjectorClosure (verticalTensor M) := by
  intro P hP hInv v
  have hLeft : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P := by
    funext i j
    ext a b
    let w := finProdFinEquiv (a, b)
    have hw : verticalTensor (M.ketLeftMul P) w =
        verticalTensor ((M.ketLeftMul P).braRightMul P) w := by
      rw [verticalTensor_ketLeftMul, verticalTensor_braRightMul,
        verticalTensor_ketLeftMul]
      exact hInv w
    have hij := congrFun (congrFun hw i) j
    simpa [w, verticalTensor_finProdFinEquiv] using hij
  have hRight :=
    hHorizontal.braRight_eq_ketLeftBraRight_of_invariant M hM hP.1 hLeft
  rw [← verticalTensor_braRightMul, hRight, verticalTensor_braRightMul,
    verticalTensor_ketLeftMul]

/-- Complete orthogonal decomposition of the vertically viewed tensor into
irreducible reducing corners.

For a horizontally canonical MPO tensor generating matrix product density
operators, there are isometries `V k` with pairwise orthogonal ranges summing
to the physical identity. Every vertical letter intertwines each `V k` with
the corresponding irreducible corner, and the adjoint intertwining and exact
compression formula hold as well. The unit-weight direct sum of these corners
has the same positive-length matrix product vector family as the vertically
viewed tensor.

This specializes the canonical-form construction of arXiv:1606.00608,
lines 200--225 and 253--255, after the invariant-projection argument of
Proposition 4.13, lines 1873--1887. -/
theorem IsHorizontalCF.exists_irreducible_verticalBlockDecomp_with_isometry
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∑ k : Fin r, V k * (V k)ᴴ = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * blocks k v) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = blocks k v * (V k)ᴴ) ∧
      (∀ k v, blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      (∀ k, MPSTensor.IsIrreducibleTensor (blocks k)) ∧
      MPSTensor.SameMPV₂Pos (verticalTensor M)
        (MPSTensor.toTensorFromBlocks
          (d := D * D) (μ := fun _ : Fin r => (1 : ℂ)) blocks) := by
  obtain ⟨r, dim, blocks, V, hdim, hIso, hSum, hOrth, hIntertwine,
      hIntertwineStar, hCompress, hIrred, hSame⟩ :=
    MPSTensor.exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure
      (verticalTensor M)
      (hHorizontal.hasInvariantProjectorClosure_verticalTensor M hM)
  exact ⟨r, dim, blocks, V, hdim, hIso, hSum, hOrth, hIntertwine,
    hIntertwineStar, hCompress, hIrred, hSame.toSameMPV₂Pos⟩

/-- The ranges of the vertical corner isometries form complete pairwise
orthogonal reducing projections.

This is the precursor of the grouped sector projections used in
arXiv:1606.00608, Proposition 4.13, line 1898. At this stage the corners are
irreducible, but possible zero corners have not been removed and the remaining
corners have not been spectrally normalized or grouped into a basis of normal
tensors. -/
theorem IsHorizontalCF.exists_complete_verticalReducingProjectors
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (P : Fin r → Matrix (Fin d) (Fin d) ℂ),
      (∀ k, IsOrthogonalProjection (P k)) ∧
      (∑ k, P k = 1) ∧
      (∀ k l, k ≠ l → P k * P l = 0) ∧
      ∀ k v, verticalTensor M v * P k = P k * verticalTensor M v := by
  obtain ⟨r, _dim, blocks, V, _hpos, hiso, hsum, horth, hint, hintStar,
    _hcorner, _hirr, _hMPV⟩ :=
    hHorizontal.exists_irreducible_verticalBlockDecomp_with_isometry M hM
  let P : Fin r → Matrix (Fin d) (Fin d) ℂ := fun k => V k * (V k)ᴴ
  refine ⟨r, P, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · change (V k * (V k)ᴴ)ᴴ = V k * (V k)ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    · change (V k * (V k)ᴴ) * (V k * (V k)ᴴ) = V k * (V k)ᴴ
      calc
        (V k * (V k)ᴴ) * (V k * (V k)ᴴ)
            = V k * ((V k)ᴴ * V k) * (V k)ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = V k * (V k)ᴴ := by rw [hiso k, Matrix.mul_one]
  · exact hsum
  · intro k l hkl
    change (V k * (V k)ᴴ) * (V l * (V l)ᴴ) = 0
    calc
      (V k * (V k)ᴴ) * (V l * (V l)ᴴ)
          = V k * ((V k)ᴴ * V l) * (V l)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [horth k l hkl, Matrix.mul_zero, Matrix.zero_mul]
  · intro k v
    change verticalTensor M v * (V k * (V k)ᴴ) =
      (V k * (V k)ᴴ) * verticalTensor M v
    calc
      verticalTensor M v * (V k * (V k)ᴴ)
          = (verticalTensor M v * V k) * (V k)ᴴ :=
            (Matrix.mul_assoc _ _ _).symm
      _ = (V k * blocks k v) * (V k)ᴴ := by rw [hint k v]
      _ = V k * (blocks k v * (V k)ᴴ) := Matrix.mul_assoc _ _ _
      _ = V k * ((V k)ᴴ * verticalTensor M v) := by rw [hintStar k v]
      _ = (V k * (V k)ᴴ) * verticalTensor M v :=
        (Matrix.mul_assoc _ _ _).symm

end MPOTensor
