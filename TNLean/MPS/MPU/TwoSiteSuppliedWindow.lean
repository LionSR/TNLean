/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteFiniteHeisenberg

/-!
# Arbitrary finite buffers for a directly supplied two-site tensor

For a tensor on two physical half-sites with supplied standard-form
gates, separate a prefix, a three-cell window and a suffix in the actual
periodic matrix. The complete input/output coordinate equivalences are
bijective. The existing buffered three-block trace identity therefore
gives a full-matrix intertwiner, and actual periodic unitarity gives
conjugation by the same four-half-site output observable.

The tensor is supplied directly. No unblocked tensor, simple block,
preimage under blocking, or extra blocking hypothesis is required.

**Scope restriction (supplied standard form):** The gates and their
standard-form identities are supplied. Their construction from a bare
MPU and the global automorphism comparison are separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

Source: CPSV17, arXiv:1703.09188, StandardForm and SF, lines 603–622,
and the finite conjugation underlying eq:appendix-1, lines 2300–2306.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

private abbrev SuppliedInputExterior (d p s : ℕ) :=
  (Fin p → Fin (d * d)) × ((Fin (d * d) × Fin (d * d)) × (Fin s → Fin (d * d)))

private abbrev SuppliedOutputExterior (d p s : ℕ) :=
  (Fin p → Fin (d * d)) × ((Fin d × Fin d) × (Fin s → Fin (d * d)))

/-- Complete input coordinates of a directly supplied tensor with an
arbitrary prefix and suffix. The existing complete three-cell-plus-tail
coordinates are reused; no restricted coefficient slice is chosen.
Source: CPSV17 StandardForm, lines 603–622. -/
def twoSiteSuppliedInputEquiv (d p s : ℕ) :
    (SuppliedInputExterior d p s × (Fin d × Fin d)) ≃
      (Fin (p + (3 + s)) → Fin (d * d)) :=
  (Equiv.prodAssoc _ _ _).trans <|
    ((Equiv.refl (Fin p → Fin (d * d))).prodCongr
      (twoSiteHeisenbergInputEquiv d s)).trans (Fin.appendEquiv p (3 + s))

/-- Complete output coordinates separate the same arbitrary buffers and
exterior half-sites from the actual four-half-site output observable.
Source: CPSV17 StandardForm, lines 603–622. -/
def twoSiteSuppliedOutputEquiv (d p s : ℕ) :
    (SuppliedOutputExterior d p s × ((Fin d × Fin d) × (Fin d × Fin d))) ≃
      (Fin (p + (3 + s)) → Fin (d * d)) :=
  (Equiv.prodAssoc _ _ _).trans <|
    ((Equiv.refl (Fin p → Fin (d * d))).prodCongr
      (twoSiteHeisenbergOutputEquiv d s)).trans (Fin.appendEquiv p (3 + s))

/-- The actual full periodic matrix in complete supplied-window
coordinates. Both buffers remain part of the finite operator.
Source: CPSV17 StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
noncomputable def twoSiteSuppliedHeisenbergMatrix {d D : ℕ}
    (W : MPOTensor (d * d) D) (p s : ℕ) :
    Matrix (SuppliedOutputExterior d p s × ((Fin d × Fin d) × (Fin d × Fin d)))
      (SuppliedInputExterior d p s × (Fin d × Fin d)) ℂ :=
  Matrix.reindex (twoSiteSuppliedOutputEquiv d p s).symm
    (twoSiteSuppliedInputEquiv d p s).symm (mpo W (p + (3 + s)))

private theorem twoSiteSuppliedHeisenbergMatrix_apply {d D ℓ r p s : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (e : SuppliedOutputExterior d p s) (f : SuppliedInputExterior d p s)
    (x : (Fin d × Fin d) × (Fin d × Fin d)) (j : Fin d × Fin d) :
    twoSiteSuppliedHeisenbergMatrix W p s (e, x) (f, j) =
      twoSiteBufferedTrace S (List.ofFn e.1) (List.ofFn f.1)
        (List.ofFn e.2.2) (List.ofFn f.2.2)
        e.2.1.1 e.2.1.2 f.2.1.1 f.2.1.2 x j := by
  change mpo W (p + (3 + s))
    (Fin.append e.1 (Fin.append
      ![finProdFinEquiv (e.2.1.1, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
        finProdFinEquiv (x.2.2, e.2.1.2)] e.2.2))
    (Fin.append f.1 (Fin.append ![f.2.1.1, finProdFinEquiv j, f.2.1.2] f.2.2)) = _
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_fin_append, twoSiteBufferedTrace,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- The actual finite periodic matrix intertwines the central one-cell
input observable with the four-half-site output, with arbitrary supplied
prefix and suffix lengths. No locality or output equality is assumed.
Source: CPSV17 StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem twoSiteSuppliedHeisenbergMatrix_intertwiner {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (p s : ℕ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (twoSiteSuppliedHeisenbergMatrix W p s)
        (Matrix.rightKroneckerEmbed A) =
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
        (Matrix.rightKroneckerEmbed (twoLinkOutputObservable u v A))
        (twoSiteSuppliedHeisenbergMatrix W p s) := by
  classical
  ext row col
  rcases row with ⟨e, x⟩
  rcases col with ⟨f, j⟩
  have h := congrArg (fun M => M x j)
    (twoSite_threeBlock_buffered_intertwiner S
      (List.ofFn e.1) (List.ofFn f.1) (List.ofFn e.2.2) (List.ofFn f.2.2)
      (by simp) e.2.1.1 e.2.1.2 f.2.1.1 f.2.1.2 A)
  simp only [Matrix.mul_apply] at h
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.rightKroneckerEmbed_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, twoSiteSuppliedHeisenbergMatrix_apply S] using h

/-- Complete coordinate relabelling preserves the actual periodic
unitarity derived from the supplied standard form, for every prefix
and suffix including zero. Source: CPSV17 StandardForm, lines 603–622. -/
theorem twoSiteSuppliedHeisenbergMatrix_isUnitaryBetween {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (p s : ℕ) :
    (twoSiteSuppliedHeisenbergMatrix W p s).IsUnitaryBetween := by
  have : NeZero (p + (3 + s)) := ⟨by omega⟩
  have h := (Matrix.isUnitaryBetween_iff_mem_unitaryGroup (mpo W (p + (3 + s)))).mpr
    (TwoSiteStandardFormData.mpo_mem_unitaryGroup W u v S)
  exact h.reindex _ (twoSiteSuppliedOutputEquiv d p s).symm
    (twoSiteSuppliedInputEquiv d p s).symm

/-- Actual finite Heisenberg conjugation with a directly supplied
standard form and arbitrary complete-cell buffers. The tensor need not
be an iterated block of another tensor.
Source: CPSV17 StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem twoSiteSuppliedHeisenbergMatrix_conjugation {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (p s : ℕ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
        (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (twoSiteSuppliedHeisenbergMatrix W p s)
          (Matrix.rightKroneckerEmbed A)) (twoSiteSuppliedHeisenbergMatrix W p s)ᴴ =
      Matrix.rightKroneckerEmbed (m := SuppliedOutputExterior d p s)
        (twoLinkOutputObservable u v A) := by
  rw [twoSiteSuppliedHeisenbergMatrix_intertwiner S p s A, Matrix.mul_assoc,
    (twoSiteSuppliedHeisenbergMatrix_isUnitaryBetween S p s).2, Matrix.mul_one]

/-- The same conjugation identity in the original finite-chain
configuration coordinates, for arbitrary complete-cell prefix and
suffix lengths of a directly supplied tensor.
Source: CPSV17 StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem mpo_suppliedWindow_conjugation {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (p s : ℕ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    mpo W (p + (3 + s)) *
        Matrix.reindex (twoSiteSuppliedInputEquiv d p s)
          (twoSiteSuppliedInputEquiv d p s)
          (Matrix.rightKroneckerEmbed (m := SuppliedInputExterior d p s) A) *
        (mpo W (p + (3 + s)))ᴴ =
      Matrix.reindex (twoSiteSuppliedOutputEquiv d p s)
        (twoSiteSuppliedOutputEquiv d p s)
        (Matrix.rightKroneckerEmbed (m := SuppliedOutputExterior d p s)
          (twoLinkOutputObservable u v A)) := by
  let ei := twoSiteSuppliedInputEquiv d p s
  let eo := twoSiteSuppliedOutputEquiv d p s
  let M := twoSiteSuppliedHeisenbergMatrix W p s
  have hM : Matrix.reindex eo ei M = mpo W (p + (3 + s)) := by
    ext row col
    simp [M, eo, ei, twoSiteSuppliedHeisenbergMatrix, Matrix.reindex_apply]
  have hMH : Matrix.reindex ei eo Mᴴ = (mpo W (p + (3 + s)))ᴴ := by
    rw [← Matrix.conjTranspose_reindex, hM]
  have h := congrArg (Matrix.reindexLinearEquiv ℂ ℂ eo eo)
    (twoSiteSuppliedHeisenbergMatrix_conjugation S p s A)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ eo ei eo,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ eo ei ei] at h
  simp only [Matrix.coe_reindexLinearEquiv] at h
  rw [hM, hMH] at h
  exact h

end MPOTensor
