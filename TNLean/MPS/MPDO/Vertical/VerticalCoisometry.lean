/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSum
import TNLean.MPS.CanonicalForm.VerticalForm.VerticalCF
import QICLean.Algebra.Unitary.IsometricFrameEmbedding

/-!
# Coisometries from orthogonal vertical sectors

For a finite family of isometries with mutually orthogonal ranges, this file
forms the block-row coisometry whose rows are their adjoints.  If a tensor
intertwines each isometry with a sector tensor, conjugation by this coisometry
is the direct sum of the sector tensors.  A literal sum over the sector
corners gives the reverse reconstruction identity.

These matrix identities isolate the finite-dimensional construction needed for
the coisometry and direct-sum conclusion of arXiv:1606.00608,
Proposition 4.13, lines 1863--1870.  The reverse identity proved here is the
conditional consequence of an assumed literal sum over the sector corners.

## Main definitions

* `Matrix.sigmaBlockRow`: the block row formed from the adjoints of a family
  of rectangular matrices.
* `MPOTensor.flattenGroupedSectorMap`: the same family reindexed by its finite
  copy label.

## Main results

* `Matrix.sigmaBlockRow_isCoisometry`: orthogonal isometries give a
  coisometry.
* `Matrix.sigmaBlockRow_conjugation`: sector intertwinings give a
  block-diagonal conjugation identity.
* `Matrix.sigmaBlockRow_reconstruction`: a sum of sector corners equals the
  reverse block-diagonal compression.
* `MPOTensor.isVerticalCF_of_grouped_orthogonal_sectors`: positive grouped
  orthogonal sectors with an exact reconstruction give vertical canonical form.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1863--1870
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Reindex a family of sector maps indexed by the dependent pair
$(\alpha,q)$ by the copy index used in the vertical direct sum. -/
def flattenGroupedSectorMap {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (W : (p : (α : Fin g) × Fin (mult α)) →
      Matrix (Fin d) (Fin (dim p.1)) ℂ) :
    (q : Fin (∑ α, mult α)) →
      Matrix (Fin d) (Fin (verticalCopyDim dim mult q)) ℂ :=
  fun q ↦ W (finSigmaFinEquiv.symm q)

/-- Orthogonal grouped vertical sectors assemble to the vertical canonical form.

The sector label is the dependent pair $(\alpha,q)$, where $\alpha$ labels a
normal tensor and $q$ labels one diagonal entry of its positive multiplicity
matrix.  The two canonical finite-sum equivalences identify these labels and
their bond indices with the coordinates of the vertical direct sum.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
theorem isVerticalCF_of_grouped_orthogonal_sectors
    (M : MPOTensor d D) {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (hMult : ∀ α, 0 < mult α)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (hω : ∀ α q, (0 : ℂ) < ω α q)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hBNT : MPSTensor.IsBNT (verticalTensor M) g dim A)
    (W : (p : (α : Fin g) × Fin (mult α)) →
      Matrix (Fin d) (Fin (dim p.1)) ℂ)
    (hiso : ∀ p, (W p)ᴴ * W p = 1)
    (horth : ∀ p q, p ≠ q → (W p)ᴴ * W q = 0)
    (hinter : ∀ p v, verticalTensor M v * W p =
      W p * ((ω p.1 p.2) • A p.1 v))
    (hreconstruct : ∀ v, verticalTensor M v =
      ∑ q : Fin (∑ α, mult α),
        flattenGroupedSectorMap dim mult W q *
          ((verticalCopyWeights mult ω q) • verticalCopyBlocks dim mult A q v) *
          (flattenGroupedSectorMap dim mult W q)ᴴ) :
    IsVerticalCF M := by
  classical
  let Wflat : (q : Fin (∑ α, mult α)) →
      Matrix (Fin d) (Fin (verticalCopyDim dim mult q)) ℂ :=
    flattenGroupedSectorMap dim mult W
  let B : (q : Fin (∑ α, mult α)) →
      MPSTensor (D * D) (verticalCopyDim dim mult q) :=
    fun q v ↦ verticalCopyWeights mult ω q • verticalCopyBlocks dim mult A q v
  let rowEquiv : ((q : Fin (∑ α, mult α)) ×
      Fin (verticalCopyDim dim mult q)) ≃
      Fin (∑ q : Fin (∑ α, mult α), verticalCopyDim dim mult q) :=
    finSigmaFinEquiv
  let U : Matrix
      (Fin (∑ q : Fin (∑ α, mult α), verticalCopyDim dim mult q)) (Fin d) ℂ :=
    Matrix.reindex rowEquiv (Equiv.refl _) (Matrix.sigmaBlockRow Wflat)
  have hisoFlat : ∀ q, (Wflat q)ᴴ * Wflat q = 1 := by
    intro q
    exact hiso (finSigmaFinEquiv.symm q)
  have horthFlat : ∀ q l, q ≠ l → (Wflat q)ᴴ * Wflat l = 0 := by
    intro q l hql
    exact horth (finSigmaFinEquiv.symm q) (finSigmaFinEquiv.symm l)
      (finSigmaFinEquiv.symm.injective.ne hql)
  have hinterFlat : ∀ q v, verticalTensor M v * Wflat q = Wflat q * B q v := by
    intro q v
    exact hinter (finSigmaFinEquiv.symm q) v
  have hreconstructFlat : ∀ v, verticalTensor M v =
      ∑ q, Wflat q * B q v * (Wflat q)ᴴ := by
    intro v
    exact hreconstruct v
  refine ⟨g, dim, mult, ω, A, U, hMult, hω, ?_, hBNT, ?_, ?_⟩
  · dsimp only [U]
    rw [Matrix.conjTranspose_reindex,
      show Matrix.reindex rowEquiv (Equiv.refl (Fin d))
          (Matrix.sigmaBlockRow Wflat) =
          Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
            (Matrix.sigmaBlockRow Wflat) by rfl,
      show Matrix.reindex (Equiv.refl (Fin d)) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ =
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
            (Matrix.sigmaBlockRow Wflat)ᴴ by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) rowEquiv,
      Matrix.sigmaBlockRow_isCoisometry Wflat hisoFlat horthFlat,
      Matrix.reindexLinearEquiv_one]
  · intro v
    have hsigma := Matrix.sigmaBlockRow_conjugation
      (verticalTensor M) B Wflat hisoFlat horthFlat hinterFlat v
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex,
      show Matrix.reindex rowEquiv (Equiv.refl (Fin d))
          (Matrix.sigmaBlockRow Wflat) =
          Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
            (Matrix.sigmaBlockRow Wflat) by rfl,
      show verticalTensor M v =
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
            (verticalTensor M v) by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) (Equiv.refl _),
      show Matrix.reindex (Equiv.refl (Fin d)) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ =
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
            (Matrix.sigmaBlockRow Wflat)ᴴ by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) rowEquiv,
      hsigma]
    rfl
  · intro v
    have hsigma := Matrix.sigmaBlockRow_reconstruction
      (verticalTensor M) B Wflat hreconstructFlat v
    rw [hsigma]
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex]
    change (Matrix.sigmaBlockRow Wflat)ᴴ * Matrix.blockDiagonal' (fun q ↦ B q v) *
        Matrix.sigmaBlockRow Wflat =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ *
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv rowEquiv
          (Matrix.blockDiagonal' (fun q ↦ B q v)) *
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
          (Matrix.sigmaBlockRow Wflat)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) rowEquiv rowEquiv,
      Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) rowEquiv (Equiv.refl _)]
    rfl

end MPOTensor
