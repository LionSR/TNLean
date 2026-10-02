/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.Algebra.PermutationMatrixUnitary

/-!
# Blocking copies of the left regular representation

The change of coordinates \((a,b)\mapsto(a,ab)\) identifies the simultaneous left action on
\(G\times G\) with the left action on the first coordinate alone. Its permutation matrix is
unitary and satisfies \(T^\dagger(L_g\otimes L_g)T=L_g\otimes I\).

More generally, \((a,(b_i)_i)\mapsto(a,(ab_i)_i)\) concentrates a simultaneous left action on
any finite collection of coordinates into the first coordinate.

These are the virtual changes of coordinates used in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Section 6, immediately before the observation on preservation of \(G\)-isometry
(`Papers/1001.3807/paper_v3.tex`, lines 1830–1850).
-/

open scoped Matrix Kronecker

namespace Matrix

/-- The matrix of a product permutation is the Kronecker product of its factor matrices. -/
theorem permMatrixHom_prodCongr {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    permMatrixHom (R := ℂ) (Equiv.prodCongr σ τ) =
      permMatrixHom (R := ℂ) σ ⊗ₖ permMatrixHom (R := ℂ) τ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [permMatrixHom_apply, Equiv.Perm.permMatrix,
    Prod.ext_iff, Equiv.Perm.inv_def]
  split_ifs <;> simp_all

end Matrix

namespace RegularRepresentation

variable {G : Type*} [Group G]

/-- The coordinate permutation \((a,b)\mapsto(a,ab)\) of SCP10, Section 6. -/
def blockingEquiv : Equiv.Perm (G × G) where
  toFun x := (x.1, x.1 * x.2)
  invFun x := (x.1, x.1⁻¹ * x.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem blockingEquiv_apply (a b : G) : blockingEquiv (a, b) = (a, a * b) := rfl

@[simp]
theorem blockingEquiv_symm_apply (a b : G) :
    blockingEquiv.symm (a, b) = (a, a⁻¹ * b) := rfl

/-- In relative coordinates, the simultaneous left action affects only the first factor.
This is the permutation form of the intertwining identity in SCP10, Section 6. -/
theorem blockingEquiv_conjugates (g : G) :
    blockingEquiv⁻¹ * MulAction.toPermHom G (G × G) g * blockingEquiv =
      Equiv.prodCongr (MulAction.toPermHom G G g) (Equiv.refl G) := by
  ext x <;> simp [blockingEquiv, Equiv.Perm.mul_apply, MulAction.toPermHom,
    MulAction.toPerm, mul_assoc]

/-- The relative-coordinate permutation \((a,(b_i)_i)\mapsto(a,(ab_i)_i)\).
This gives the many-bond form of the coordinate change in SCP10, Section 6. -/
def blockingFamilyEquiv (ι : Type*) : Equiv.Perm (G × (ι → G)) where
  toFun x := (x.1, fun i => x.1 * x.2 i)
  invFun x := (x.1, fun i => x.1⁻¹ * x.2 i)
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem blockingFamilyEquiv_apply {ι : Type*} (a : G) (b : ι → G) :
    blockingFamilyEquiv ι (a, b) = (a, fun i => a * b i) := rfl

@[simp]
theorem blockingFamilyEquiv_symm_apply {ι : Type*} (a : G) (b : ι → G) :
    (blockingFamilyEquiv ι).symm (a, b) = (a, fun i => a⁻¹ * b i) := rfl

/-- Simultaneous left multiplication is left multiplication of the distinguished coordinate
in relative coordinates. -/
theorem blockingFamilyEquiv_smul {ι : Type*} (g a : G) (b : ι → G) :
    blockingFamilyEquiv ι (g * a, b) = g • blockingFamilyEquiv ι (a, b) := by
  ext i <;> simp [blockingFamilyEquiv, mul_assoc]

/-- A simultaneous left action on a distinguished coordinate and an arbitrary family becomes
left action on the distinguished coordinate alone. This generalizes SCP10, Section 6. -/
theorem blockingFamilyEquiv_conjugates (ι : Type*) (g : G) :
    (blockingFamilyEquiv ι)⁻¹ * MulAction.toPermHom G (G × (ι → G)) g *
        blockingFamilyEquiv ι =
      Equiv.prodCongr (MulAction.toPermHom G G g) (Equiv.refl (ι → G)) := by
  ext x i <;> simp [blockingFamilyEquiv, Equiv.Perm.mul_apply, MulAction.toPermHom,
    MulAction.toPerm, mul_assoc]

variable [Fintype G] [DecidableEq G]

/-- The unitary \(T|a,b\rangle=|a,ab\rangle\) of SCP10, Section 6. -/
def blockingMatrix : Matrix (G × G) (G × G) ℂ :=
  Matrix.permMatrixHom (R := ℂ) blockingEquiv

/-- The basis permutation implementing blocking is unitary. -/
theorem blockingMatrix_mem_unitaryGroup :
    blockingMatrix (G := G) ∈ Matrix.unitaryGroup (G × G) ℂ :=
  (blockingEquiv⁻¹).permMatrix_mem_unitaryGroup

/-- The two-bond identity \(T^\dagger(L_g\otimes L_g)T=L_g\otimes I\)
of SCP10, Section 6, with \(L_g|a\rangle=|ga\rangle\). -/
theorem blockingMatrix_conjugates (g : G) :
    (blockingMatrix (G := G)).conjTranspose *
        (Matrix.permMatrixHom (R := ℂ) (MulAction.toPermHom G G g) ⊗ₖ
          Matrix.permMatrixHom (R := ℂ) (MulAction.toPermHom G G g)) * blockingMatrix =
      Matrix.permMatrixHom (R := ℂ) (MulAction.toPermHom G G g) ⊗ₖ (1 : Matrix G G ℂ) := by
  have hdiag : MulAction.toPermHom G (G × G) g =
      Equiv.prodCongr (MulAction.toPermHom G G g) (MulAction.toPermHom G G g) := by
    ext x <;> rfl
  have h := congrArg (Matrix.permMatrixHom (R := ℂ)) (blockingEquiv_conjugates g)
  simp only [map_mul, hdiag, Matrix.permMatrixHom_prodCongr] at h
  simpa [blockingMatrix, Matrix.permMatrixHom_apply, Equiv.Perm.inv_def] using h

/-- The unitary coordinate change for a distinguished regular bond and a finite family of bonds. -/
def blockingFamilyMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix (G × (ι → G)) (G × (ι → G)) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (blockingFamilyEquiv ι)

/-- The many-bond change of relative coordinates is unitary. -/
theorem blockingFamilyMatrix_mem_unitaryGroup (ι : Type*) [Fintype ι] [DecidableEq ι] :
    blockingFamilyMatrix (G := G) ι ∈ Matrix.unitaryGroup (G × (ι → G)) ℂ :=
  ((blockingFamilyEquiv ι)⁻¹).permMatrix_mem_unitaryGroup

/-- Simultaneous left action on finitely many regular bonds is unitarily equivalent to one
regular bond and unchanged relative coordinates, as used in SCP10, Section 6. -/
theorem blockingFamilyMatrix_conjugates (ι : Type*) [Fintype ι] [DecidableEq ι] (g : G) :
    (blockingFamilyMatrix (G := G) ι).conjTranspose *
        Matrix.permMatrixHom (R := ℂ) (MulAction.toPermHom G (G × (ι → G)) g) *
        blockingFamilyMatrix ι =
      Matrix.permMatrixHom (R := ℂ) (MulAction.toPermHom G G g) ⊗ₖ
        (1 : Matrix (ι → G) (ι → G) ℂ) := by
  have h := congrArg (Matrix.permMatrixHom (R := ℂ)) (blockingFamilyEquiv_conjugates ι g)
  simp only [map_mul, Matrix.permMatrixHom_prodCongr] at h
  simpa [blockingFamilyMatrix, Matrix.permMatrixHom_apply, Equiv.Perm.inv_def] using h


end RegularRepresentation
