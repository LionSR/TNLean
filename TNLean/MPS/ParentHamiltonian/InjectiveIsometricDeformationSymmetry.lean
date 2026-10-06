/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Vec
import QICLean.Algebra.MatrixReindexUnitary
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.ParentHamiltonian.IsometricDeformationCovariance
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.Symmetry.EntanglementSpectrum
import TNLean.Tactic.MatrixReciprocalSmul

/-!
# Symmetry of the isometric deformation for an injective canonical tensor

This module derives a unitary virtual action from exact on-site symmetry of an
injective tensor, and transfers it to the constructed polar deformation. Both
canonical orientations are treated: the unital normalization \(E_A(I)=I\),
and the trace-preserving normalization \(\sum_i A_i^\dagger A_i=I\).
No faithful fixed point is imposed as an additional hypothesis.

For the coordinates \(P_{i,(a,b)}=A_i(a,b)\), the trace-preserving orientation
is exactly the source condition
\(\operatorname{tr}_{\mathrm{left}}(P^\dagger P)=I\).
The unital orientation instead means \(\sum_i A_iA_i^\dagger=I\);
the two canonical orientations are dual.

Source: arXiv:1010.3732, `paper_v3.tex`, lines 645--676.
**Scope restriction (already-blocked single canonical block):** The tensor is
one-site injective, exactly symmetric as a family of vectors, and in one of the
stated canonical orientations. The multi-block virtual permutation and the
passage from arbitrary normal tensors to a symmetry-
compatible blocked canonical form are not asserted here. See
`docs/paper-gaps/spc11_isometric_symmetry_unitary_virtual.tex`.
-/

open scoped Matrix BigOperators MatrixOrder ComplexOrder Kronecker

namespace MPSTensor

variable {G : Type*} [Monoid G] {d D : ℕ}

/-- Exact on-site symmetry of an injective unital-normalized tensor admits
unitary virtual conjugations. Source: arXiv:1010.3732, lines 652--660.
The faithful adjoint fixed point needed to normalize the gauge is derived. -/
theorem exists_unitary_virtual_of_isOnSiteSymmetric [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ,
      V ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ∀ i, twistedTensor A U g i = V * A i * Vᴴ := by
  classical
  let setup := twistedTPGaugeSetup A hA 1 (by simp) hNorm
  have hB : setup.B = A := by
    rw [setup.hB_def]
    funext i
    simp [twistedMixedCompanion, Matrix.one_apply]
  obtain ⟨X, hX⟩ := gaugeEquiv_twistedTensor_of_injective A hA U hSymm g
  obtain ⟨V, hVV, hVV', -, c, hc, hXV⟩ :=
    exists_unitary_gauge_of_symmetry hA hNorm setup.hσ_pd
      (by simpa only [hB] using setup.hσ_fixB)
      (by simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp (hU g))
      one_ne_zero (fun i => by simpa only [one_smul, twistedTensor] using hX i)
  have hInv : (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) = c⁻¹ • Vᴴ := by
    apply Units.inv_eq_of_mul_eq_one_left
    simp (disch := exact hc) only [hXV, matrix_reciprocal_smul, hVV']
  refine ⟨V, Matrix.mem_unitaryGroup_iff.mpr (by
    simpa only [Matrix.star_eq_conjTranspose] using hVV), ?_⟩
  simpa (disch := exact hc) only [hXV, hInv, matrix_reciprocal_smul] using hX

private def singletonEntryEquiv (D : ℕ) :
    BlockEntryIndex (fun _ : Fin 1 => D) ≃ Fin D × Fin D where
  toFun := fun p => p.2
  invFun := fun p => ⟨0, p⟩
  left_inv := fun _ => Sigma.ext (Subsingleton.elim _ _) HEq.rfl
  right_inv := fun _ => rfl

private noncomputable def singletonVirtualAction (V : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (BlockEntryIndex (fun _ : Fin 1 => D))
      (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ :=
  Matrix.reindex (singletonEntryEquiv D).symm (singletonEntryEquiv D).symm (Vᵀ ⊗ₖ Vᴴ)

private theorem singletonVirtualAction_mem_unitaryGroup
    (V : Matrix (Fin D) (Fin D) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    singletonVirtualAction V ∈ Matrix.unitaryGroup
      (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ :=
  Matrix.reindex_mem_unitaryGroup _ _ (Matrix.kronecker_mem_unitary
    (Matrix.transpose_mem_unitaryGroup_iff.mpr hV) (Unitary.star_mem hV))

private theorem blockPhysicalMatrix_singleton_covariance
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ)
    (hCov : ∀ i, rotatePhysical u A i = V * A i * Vᴴ) :
    u * blockPhysicalMatrix (fun _ : Fin 1 => A) =
      blockPhysicalMatrix (fun _ : Fin 1 => A) * singletonVirtualAction V := by
  ext i p
  have hvec := congrFun (Matrix.vec_vecMul_kronecker Vᴴ (A i)ᵀ Vᵀ) p.2
  simp only [← Matrix.transpose_mul, Matrix.vec,
    Matrix.transpose_apply] at hvec
  have hlocal : rotatePhysical u A i p.2.1 p.2.2 =
      ((A i)ᵀ.vec ᵥ* (Vᵀ ⊗ₖ Vᴴ)) p.2 :=
    (congrFun (congrFun (hCov i) p.2.1) p.2.2).trans
      (by simpa only [Matrix.mul_assoc] using hvec.symm)
  simpa [Matrix.mul_apply, blockPhysicalMatrix, singletonVirtualAction,
    Matrix.reindex_apply, singletonEntryEquiv, Matrix.vecMul, dotProduct,
    Fintype.sum_sigma, Fintype.sum_prod_type, rotatePhysical, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using hlocal

/-- A unital-normalized injective tensor with exact on-site symmetry has
unitary covariance on its joint physical map. Source: arXiv:1010.3732,
lines 652--660, in the already-blocked single-block case. -/
theorem exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ X : Matrix (BlockEntryIndex (fun _ : Fin 1 => D))
        (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ ∧
      U g * blockPhysicalMatrix (fun _ : Fin 1 => A) =
        blockPhysicalMatrix (fun _ : Fin 1 => A) * X := by
  exact (exists_unitary_virtual_of_isOnSiteSymmetric A hA hNorm U hU hSymm g).elim
    fun V hV => ⟨singletonVirtualAction V,
      singletonVirtualAction_mem_unitaryGroup V hV.1,
      blockPhysicalMatrix_singleton_covariance A (U g) V hV.2⟩

/-- The positive factor of the constructed polar deformation commutes with
an exact on-site symmetry of an injective unital-normalized tensor.
Source: arXiv:1010.3732, lines 660--676. -/
theorem commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    Commute (U g) (leftPolarPhysicalFactor (fun _ : Fin 1 => A)) := by
  exact (exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric
    A hA hNorm U hU hSymm g).elim fun X hX =>
      commute_leftPolarPhysicalFactor_of_unitary_covariance
        (fun _ : Fin 1 => A) (U g) X (hU g) hX.1 hX.2

/-- A virtual unitary derived from exact on-site symmetry intertwines the
entire constructed single-block isometric deformation. Source:
arXiv:1010.3732, lines 672--676. The same virtual unitary works at every
parameter; no adjoint fixed point is supplied as a hypothesis. -/
theorem exists_isometricDeformationBlocks_unitary_covariance_of_isOnSiteSymmetric
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ X : Matrix (BlockEntryIndex (fun _ : Fin 1 => D))
        (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ ∧
      ∀ γ : unitInterval,
        U g * blockPhysicalMatrix (isometricDeformationBlocks (fun _ : Fin 1 => A) γ) =
          blockPhysicalMatrix (isometricDeformationBlocks (fun _ : Fin 1 => A) γ) * X := by
  exact (exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric
    A hA hNorm U hU hSymm g).elim fun X hX => ⟨X, hX.1,
      fun γ => blockPhysicalMatrix_isometricDeformationBlocks_covariance
        (fun _ : Fin 1 => A) (U g) X (hU g) hX.1 hX.2 γ⟩

/-- In the trace-preserving canonical orientation printed in SPC11, exact
on-site symmetry admits a unitary virtual conjugation. Source:
arXiv:1010.3732, lines 652--660. No faithful fixed point is supplied. -/
theorem exists_unitary_virtual_of_isOnSiteSymmetric_of_isTP [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ,
      V ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ∀ i, twistedTensor A U g i = V * A i * Vᴴ := by
  obtain ⟨X, hX⟩ := gaugeEquiv_twistedTensor_of_injective A hA U hSymm g
  have hIrr : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
      (Kraus.injective_implies_irreducibleCP A hA)
  have hu : U g * (U g)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hU g)
  obtain ⟨V, -, hV⟩ :=
    exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible X 1 one_ne_zero
      (fun i => by simpa only [one_smul, rotatePhysical, twistedTensor] using hX i) hTP
      (isLeftCanonical_rotatePhysical A (U g) hu hTP) hIrr
      (isIrreducibleTensor_rotatePhysical A (U g) hu hIrr)
  exact ⟨V, V.property, by
    simpa only [one_smul, rotatePhysical, twistedTensor] using hV⟩

/-- Trace-preserving exact-vector symmetry gives a unitary on the joint
physical map. Source: arXiv:1010.3732, lines 652--660; this uses the
partial-trace normalization printed at line 653. -/
theorem exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_of_isTP
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ X : Matrix (BlockEntryIndex (fun _ : Fin 1 => D))
        (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ ∧
      U g * blockPhysicalMatrix (fun _ : Fin 1 => A) =
        blockPhysicalMatrix (fun _ : Fin 1 => A) * X := by
  exact (exists_unitary_virtual_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g).elim
    fun V hV => ⟨singletonVirtualAction V,
      singletonVirtualAction_mem_unitaryGroup V hV.1,
      blockPhysicalMatrix_singleton_covariance A (U g) V hV.2⟩

/-- The positive polar factor commutes with an exact physical symmetry
in the source's trace-preserving canonical orientation. Source:
arXiv:1010.3732, lines 652--676. -/
theorem commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_of_isTP [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    Commute (U g) (leftPolarPhysicalFactor (fun _ : Fin 1 => A)) := by
  exact (exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_of_isTP
    A hA hTP U hU hSymm g).elim fun X hX =>
      commute_leftPolarPhysicalFactor_of_unitary_covariance
        (fun _ : Fin 1 => A) (U g) X (hU g) hX.1 hX.2

/-- In the source's trace-preserving canonical orientation, the virtual
unitary derived from exact state symmetry intertwines the entire constructed
isometric deformation. Source: arXiv:1010.3732, lines 652--676. -/
theorem exists_isometricDeformationBlocks_unitary_covariance_of_isOnSiteSymmetric_of_isTP
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ X : Matrix (BlockEntryIndex (fun _ : Fin 1 => D))
        (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex (fun _ : Fin 1 => D)) ℂ ∧
      ∀ γ : unitInterval,
        U g * blockPhysicalMatrix (isometricDeformationBlocks (fun _ : Fin 1 => A) γ) =
          blockPhysicalMatrix (isometricDeformationBlocks (fun _ : Fin 1 => A) γ) * X := by
  exact (exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_of_isTP
    A hA hTP U hU hSymm g).elim fun X hX => ⟨X, hX.1,
      fun γ => blockPhysicalMatrix_isometricDeformationBlocks_covariance
        (fun _ : Fin 1 => A) (U g) X (hU g) hX.1 hX.2 γ⟩

end MPSTensor
