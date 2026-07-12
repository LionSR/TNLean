/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.HayashiSectorComparison

/-!
# Physical-sector factorizations of simple MPO tensors

This file isolates the algebraic content of the physical-sector decomposition
used in Appendix C.2 of arXiv:1606.00608.  After an isometry on the physical
space, every physical slice of the MPO tensor is a direct sum of Kronecker
products
\[
  U\,\kappa_{\beta,\alpha}\,U^*=
    \bigoplus_k (l_k)_\beta\otimes(r_k)_\alpha.
\]
The datum below records exactly this factorization.  In particular, it does
not contain a quantum-Markov decomposition, positivity of the neighboring
operators, or the trace factorization used later in Proposition C.7.

The two contractions needed in the fixed-point calculation are then intrinsic
to this datum.  The neighboring operator contracts the common virtual index
between a right tensor and a left tensor.  The boundary operator contracts an
arbitrary virtual matrix against the two outer tensors.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equation `AppUkU=rl`, lines 1381--1388, and equation `etarl`,
  lines 1441--1445
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- A source-minimal physical-sector factorization of an MPO tensor.

The physical space is decomposed as
$\bigoplus_k B_k^L\otimes B_k^R$.  The matrices `leftTensor k beta` and
`rightTensor k alpha` are the factors $(l_k)_\beta$ and $(r_k)_\alpha$ in
the transformed physical slice.  The only compatibility imposed on these
data is the displayed direct-sum factorization from the source.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388; the explicit slice factorization is derived at lines 1435--1448. -/
structure PhysicalSectorFactorization (K : MPOTensor d D) where
  /-- Number of physical sectors. -/
  sectorCount : ℕ
  /-- Dimension of the left factor in each physical sector. -/
  leftDim : Fin sectorCount → ℕ
  /-- Dimension of the right factor in each physical sector. -/
  rightDim : Fin sectorCount → ℕ
  /-- Identification of the physical space with the direct sum of its sectors. -/
  sectorEquiv : Fin d ≃ Σ k : Fin sectorCount, Fin (leftDim k) × Fin (rightDim k)
  /-- The physical-space isometry in equation `AppUkU=rl`. -/
  physicalIsometry : Matrix (Fin d) (Fin d) ℂ
  /-- The physical transformation is an isometry. -/
  physicalIsometry_isometry : physicalIsometryᴴ * physicalIsometry = 1
  /-- The left tensor $(l_k)_\beta$ in sector `k`. -/
  leftTensor : (k : Fin sectorCount) → Fin D →
    Matrix (Fin (leftDim k)) (Fin (leftDim k)) ℂ
  /-- The right tensor $(r_k)_\alpha$ in sector `k`. -/
  rightTensor : (k : Fin sectorCount) → Fin D →
    Matrix (Fin (rightDim k)) (Fin (rightDim k)) ℂ
  /-- Every transformed physical slice is the direct sum of its sector factors. -/
  factorization : ∀ beta alpha : Fin D,
    Matrix.reindex sectorEquiv sectorEquiv
        (physicalIsometry * physicalSlice K beta alpha * physicalIsometryᴴ) =
      Matrix.blockDiagonal' fun k ↦
        Matrix.kroneckerMap (· * ·) (leftTensor k beta) (rightTensor k alpha)

namespace PhysicalSectorFactorization

variable {K : MPOTensor d D}

/-- The physical index type within sector `k`. -/
abbrev SectorIndex (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) :=
  Fin (F.leftDim k) × Fin (F.rightDim k)

/-- The index space supporting the neighboring operator between sectors `k`
and `h`. -/
abbrev NeighborIndex (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :=
  Fin (F.rightDim k) × Fin (F.leftDim h)

/-- The index space supporting the two outer tensors in sectors `k` and `h`. -/
abbrev BoundaryIndex (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :=
  Fin (F.leftDim k) × Fin (F.rightDim h)

/-- A transformed physical slice, expressed in physical-sector coordinates. -/
def transformedPhysicalSlice (F : PhysicalSectorFactorization K)
    (beta alpha : Fin D) :
    Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (Σ k : Fin F.sectorCount, SectorIndex F k) ℂ :=
  Matrix.reindex F.sectorEquiv F.sectorEquiv
    (F.physicalIsometry * physicalSlice K beta alpha * F.physicalIsometryᴴ)

/-- The transformed physical slice is the direct sum of its left-right sector
factors. -/
theorem transformedPhysicalSlice_eq (F : PhysicalSectorFactorization K)
    (beta alpha : Fin D) :
    F.transformedPhysicalSlice beta alpha =
      Matrix.blockDiagonal' fun k ↦
        Matrix.kroneckerMap (· * ·) (F.leftTensor k beta) (F.rightTensor k alpha) :=
  F.factorization beta alpha

/-- The canonical finite encoding of the dependent sum of physical sectors.

This converts the direct-sum coordinates of equation `AppUkU=rl` into the
`Fin`-indexed physical space used by an MPO tensor.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def sectorFinEquiv (F : PhysicalSectorFactorization K) :
    Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)) ≃
      (Σ k : Fin F.sectorCount, SectorIndex F k) :=
  (Fintype.equivFin _).symm

/-- The MPO tensor obtained by expressing the physical legs in sector
coordinates.  Its physical matrix at fixed virtual indices is precisely
`transformedPhysicalSlice`, with the dependent sector sum encoded by
`sectorFinEquiv`.

Thus this tensor is the direct `Fin`-indexed form of
$U\,\mathcal K\,U^*=\bigoplus_k l_k\otimes r_k$ and can be inserted into the
ordinary physical-closure operations without additional coordinate changes.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388; the explicit physical-slice form appears at lines 1435--1448. -/
noncomputable def sectorCoordinateTensor (F : PhysicalSectorFactorization K) :
    MPOTensor (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)) D :=
  fun i j ↦ Matrix.of fun beta alpha ↦
    F.transformedPhysicalSlice beta alpha (F.sectorFinEquiv i) (F.sectorFinEquiv j)

/-- An entry of the sector-coordinate tensor is the corresponding entry of
the transformed physical slice.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
@[simp] theorem sectorCoordinateTensor_apply (F : PhysicalSectorFactorization K)
    (i j : Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)))
    (beta alpha : Fin D) :
    F.sectorCoordinateTensor i j beta alpha =
      F.transformedPhysicalSlice beta alpha (F.sectorFinEquiv i) (F.sectorFinEquiv j) :=
  rfl

/-- Within one physical sector, an entry of the sector-coordinate tensor is
the product of the corresponding left- and right-tensor entries.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388; the explicit physical-slice form appears at lines 1435--1448. -/
@[simp] theorem sectorCoordinateTensor_apply_same
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount)
    (x y : SectorIndex F k) (beta alpha : Fin D) :
    F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨k, x⟩) (F.sectorFinEquiv.symm ⟨k, y⟩) beta alpha =
      F.leftTensor k beta x.1 y.1 * F.rightTensor k alpha x.2 y.2 := by
  rw [sectorCoordinateTensor_apply]
  simp only [Equiv.apply_symm_apply]
  rw [F.transformedPhysicalSlice_eq, Matrix.blockDiagonal'_apply_eq]
  rfl

/-- Entries of the sector-coordinate tensor between distinct physical sectors
vanish.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388; the direct-sum form is used at lines 1435--1448. -/
@[simp] theorem sectorCoordinateTensor_apply_ne
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount} (hkh : k ≠ h)
    (x : SectorIndex F k) (y : SectorIndex F h) (beta alpha : Fin D) :
    F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨k, x⟩) (F.sectorFinEquiv.symm ⟨h, y⟩) beta alpha = 0 := by
  rw [sectorCoordinateTensor_apply]
  simp only [Equiv.apply_symm_apply]
  rw [F.transformedPhysicalSlice_eq, Matrix.blockDiagonal'_apply_ne _ _ _ hkh]

/-- An entry within one sector is the product of the corresponding entries of
the left and right tensors. -/
@[simp] theorem transformedPhysicalSlice_apply_same
    (F : PhysicalSectorFactorization K) (beta alpha : Fin D)
    (k : Fin F.sectorCount) (x y : SectorIndex F k) :
    F.transformedPhysicalSlice beta alpha ⟨k, x⟩ ⟨k, y⟩ =
      F.leftTensor k beta x.1 y.1 * F.rightTensor k alpha x.2 y.2 := by
  rw [F.transformedPhysicalSlice_eq, Matrix.blockDiagonal'_apply_eq]
  rfl

/-- Entries between distinct physical sectors vanish. -/
@[simp] theorem transformedPhysicalSlice_apply_ne
    (F : PhysicalSectorFactorization K) (beta alpha : Fin D)
    {k h : Fin F.sectorCount} (hkh : k ≠ h)
    (x : SectorIndex F k) (y : SectorIndex F h) :
    F.transformedPhysicalSlice beta alpha ⟨k, x⟩ ⟨h, y⟩ = 0 := by
  rw [F.transformedPhysicalSlice_eq, Matrix.blockDiagonal'_apply_ne _ _ _ hkh]

/-- The neighboring operator $\eta_{k,h}=r_k l_h$, obtained by contracting
the common virtual index:
\[
  (\eta_{k,h})_{(x_R,x_L),(y_R,y_L)}=
  \sum_a (r_k)_a(x_R,y_R)(l_h)_a(x_L,y_L).
\]

No positivity or normalization is asserted.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
noncomputable def neighboringOperator (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :
    Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ :=
  Matrix.of fun x y ↦
    ∑ a : Fin D,
      F.rightTensor k a x.1 y.1 * F.leftTensor h a x.2 y.2

/-- Entries of the neighboring operator are virtual-index contractions of the
right and left sector tensors. -/
@[simp] theorem neighboringOperator_apply (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (x y : NeighborIndex F k h) :
    F.neighboringOperator k h x y =
      ∑ a : Fin D,
        F.rightTensor k a x.1 y.1 * F.leftTensor h a x.2 y.2 :=
  rfl

/-- The outer boundary operator associated with a virtual matrix `X`:
\[
  B_{k,h}(X)=\sum_{a,b}X_{b,a}\,(l_k)_a\otimes(r_h)_b.
\]

This is the boundary factor left after contracting the interior virtual
indices in products of the factorized tensor.  It uses only the factorization
in equation `AppUkU=rl`.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388, and the contraction argument at lines 1441--1450. -/
noncomputable def boundaryOperator (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ :=
  Matrix.of fun x y ↦
    ∑ a : Fin D, ∑ b : Fin D,
      X b a * F.leftTensor k a x.1 y.1 * F.rightTensor h b x.2 y.2

/-- Entries of the boundary operator are the contraction of `X` against the
two outer sector tensors. -/
@[simp] theorem boundaryOperator_apply (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ)
    (x y : BoundaryIndex F k h) :
    F.boundaryOperator k h X x y =
      ∑ a : Fin D, ∑ b : Fin D,
        X b a * F.leftTensor k a x.1 y.1 * F.rightTensor h b x.2 y.2 :=
  rfl

@[simp] theorem boundaryOperator_zero (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :
    F.boundaryOperator k h 0 = 0 := by
  ext x y
  simp

@[simp] theorem boundaryOperator_add (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (X Y : Matrix (Fin D) (Fin D) ℂ) :
    F.boundaryOperator k h (X + Y) =
      F.boundaryOperator k h X + F.boundaryOperator k h Y := by
  ext x y
  simp [add_mul, Finset.sum_add_distrib]

@[simp] theorem boundaryOperator_smul (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (c : ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    F.boundaryOperator k h (c • X) = c • F.boundaryOperator k h X := by
  ext x y
  simp [Finset.mul_sum, mul_assoc]

end PhysicalSectorFactorization

end MPOTensor
