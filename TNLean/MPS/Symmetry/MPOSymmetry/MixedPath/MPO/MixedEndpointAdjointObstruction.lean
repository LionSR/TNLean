/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Boundary.NormalAdjointBoundary
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.MPO.MixedEndpointMPO
import TNLean.MPS.Symmetry.GappedPath.PolarDeformation

/-!
# Unitary endpoints need not give an adjoint-closed mixed boundary range

The endpoint involution is diagonal and unitary. Its virtual implementation
is a non-Hermitian involution. The two-site mixed boundary range remembers
that virtual implementation through the cross sectors.

This refutes inheritance from endpoint adjoint closure for the square-alphabet
mixed construction. The accompanying written calculation identifies a positive
polar tensor and explains the arbitrary-alphabet version; see
`docs/paper-gaps/glm23_mixed_endpoint_adjoint.tex`.

Source context: arXiv:2203.12563v3, Section 5, lines 1600–1631. This example
concerns the proposed adjoint-closure implication, not the existence of a
symmetric path after a different choice of virtual coordinates.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor.MPOSymmetry.MixedEndpointAdjointObstruction

/-- A non-Hermitian virtual involution, similar to `diag(1,-1)`. -/
def virtualInvolution : Matrix (Fin 2) (Fin 2) ℂ := !![3, -4; 2, -3]

/-- The unitary physical involution on the four endpoint letters. -/
def physicalInvolution : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, -1, 1]

/-- The positive coefficient matrix of the first endpoint tensor. -/
def endpointCoefficients : Matrix (Fin 4) (Fin 4) ℂ :=
  !![2, -2, 1, -1; -2, 4, -1, 2; 1, -1, 1, -1; -1, 2, -1, 2]

/-- The injective endpoint with a nonunitary virtual implementation. -/
def endpoint : MPSTensor 4 2 :=
  fun i j k => endpointCoefficients i (finProdFinEquiv (j, k))

/-- The one-dimensional second endpoint tensor. -/
def scalarEndpoint : MPSTensor 1 1 := fun _ => 1

/-- The bond-one MPO for the physical endpoint involution. -/
def endpointMPO : MPOTensor 4 1 := fun (i, j) _ _ => physicalInvolution i j

/-- The scalar second endpoint MPO. -/
def scalarMPO : MPOTensor 1 1 := fun (_, _) _ _ => 1

/-- The mixed MPO with one-dimensional action multiplicity and the virtual
involution used as both analysis and synthesis at the first endpoint. -/
noncomputable def mixedMPO : MPOTensor 9 2 :=
  mixedEndpointMPO (D₀ := 2) (D₁ := 1) endpointMPO scalarMPO
    (fun _ : Fin 1 => virtualInvolution) (fun _ => 1)
    (fun _ => virtualInvolution) (fun _ => 1)

/-- Both applications of the virtual involution cancel exactly. -/
theorem virtualInvolution_mul_self : virtualInvolution * virtualInvolution = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [virtualInvolution, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The displayed endpoint letters span the full two-by-two matrix algebra. -/
theorem endpoint_isInjective : Kraus.IsInjective endpoint := by
  let R : Matrix (Fin 4) (Fin 4) ℂ :=
    !![2, 1, -2, -1; 1, 1, -1, -1; -2, -1, 4, 2; -1, -1, 2, 2]
  apply isInjective_of_leftInverse_physicalMatrix endpoint
    (R.submatrix finProdFinEquiv id)
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [R, physicalMatrix, endpoint, endpointCoefficients, Matrix.mul_apply,
      Fin.sum_univ_succ, finProdFinEquiv, Matrix.one_apply, Prod.ext_iff]

/-- The unitary physical endpoint symmetry has an exact action decomposition
with the non-Hermitian virtual involution. -/
theorem endpoint_action :
    IsBiorthogonalDecomposition (MPOTensor.actTensor endpointMPO endpoint)
      (fun _ : Fin 1 => endpoint) (fun _ => virtualInvolution)
      (fun _ => virtualInvolution) where
  retract := fun _ => virtualInvolution_mul_self
  orthogonal := fun a b h => (h (Subsingleton.elim a b)).elim
  letter := by
    intro i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [MPOTensor.actTensor, endpointMPO, physicalInvolution, endpoint,
        endpointCoefficients, virtualInvolution, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.diagonal_apply, finProdFinEquiv, Matrix.vecMul, dotProduct]

/-- The scalar endpoint is injective. -/
theorem scalarEndpoint_isInjective : Kraus.IsInjective scalarEndpoint := by
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  have h : Matrix.single i j (1 : ℂ) = scalarEndpoint 0 := by
    ext a b
    fin_cases i; fin_cases j; fin_cases a; fin_cases b
    norm_num [scalarEndpoint, Matrix.single_apply]
  rw [h]
  exact Submodule.subset_span ⟨0, rfl⟩

/-- The scalar endpoint has the identity action decomposition. -/
theorem scalarEndpoint_action :
    IsBiorthogonalDecomposition (MPOTensor.actTensor scalarMPO scalarEndpoint)
      (fun _ : Fin 1 => scalarEndpoint) (fun _ => 1) (fun _ => 1) where
  retract := fun _ => Matrix.one_mul _
  orthogonal := fun a b h => (h (Subsingleton.elim a b)).elim
  letter := by
    intro i
    ext j k
    fin_cases i; fin_cases j; fin_cases k
    norm_num [MPOTensor.actTensor, scalarMPO, scalarEndpoint, Matrix.mul_apply,
        Fin.sum_univ_succ, finProdFinEquiv]

/-- The endpoint coefficient matrix is positive semidefinite, with an explicit
integer Gram factor. Its invertibility is witnessed in `endpoint_isInjective`. -/
theorem endpointCoefficients_posSemidef : endpointCoefficients.PosSemidef := by
  let R : Matrix (Fin 4) (Fin 4) ℂ :=
    !![1, -1, 0, 0; 0, 1, 0, 0; 1, -1, 1, -1; 0, 1, 0, 1]
  have hR : Rᴴ * R = endpointCoefficients := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R, endpointCoefficients, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.conjTranspose_apply]
  rw [← hR]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- The first endpoint physical operator is unitary. -/
theorem physicalInvolution_unitary : physicalInvolutionᴴ * physicalInvolution = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [physicalInvolution, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply]

/-- The first endpoint tensor is fixed by the physical adjoint. -/
theorem physicalAdjointTensor_endpointMPO :
    MPOTensor.physicalAdjointTensor endpointMPO = endpointMPO := by
  ext ⟨i, j⟩ α β
  fin_cases i <;> fin_cases j <;>
    norm_num [MPOTensor.physicalAdjointTensor, endpointMPO, physicalInvolution,
      Matrix.diagonal_apply]

/-- The scalar endpoint tensor is fixed by the physical adjoint. -/
theorem physicalAdjointTensor_scalarMPO :
    MPOTensor.physicalAdjointTensor scalarMPO = scalarMPO := by
  ext ⟨i, j⟩ α β
  simp [MPOTensor.physicalAdjointTensor, scalarMPO]

/-- The first endpoint has an adjoint-closed boundary range at every length. -/
theorem endpoint_adjoint_closed (X : Matrix (Fin 1) (Fin 1) ℂ) (N : ℕ) :
    ∃ Y, (MPOTensor.mpoWithBoundary endpointMPO X N)ᴴ =
      MPOTensor.mpoWithBoundary endpointMPO Y N := by
  refine ⟨X.map (starRingEnd ℂ), ?_⟩
  rw [MPOTensor.conjTranspose_mpoWithBoundary, physicalAdjointTensor_endpointMPO]

/-- The second endpoint has an adjoint-closed boundary range at every length. -/
theorem scalar_adjoint_closed (X : Matrix (Fin 1) (Fin 1) ℂ) (N : ℕ) :
    ∃ Y, (MPOTensor.mpoWithBoundary scalarMPO X N)ᴴ =
      MPOTensor.mpoWithBoundary scalarMPO Y N := by
  refine ⟨X.map (starRingEnd ℂ), ?_⟩
  rw [MPOTensor.conjTranspose_mpoWithBoundary, physicalAdjointTensor_scalarMPO]

/-- The mixed MPO itself is one-site injective after combining its physical
indices; failure of adjoint closure is not caused by redundant MPO bonds. -/
theorem mixedMPO_isInjective : Kraus.IsInjective mixedMPO.toMPSTensor := by
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  let r : Fin 9 := if i = 0 then (if j = 0 then 0 else 2)
    else (if j = 0 then 6 else 8)
  let c : ℂ := if i = j then 1 else 1 / 3
  have h : Matrix.single i j (1 : ℂ) =
      c • mixedMPO.toMPSTensor (finProdFinEquiv (r, r)) := by
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [r, c, MPOTensor.toMPSTensor, mixedMPO, mixedEndpointMPO,
        mixedEndpointMPOLetter, mixedEndpointPhysicalEquiv, endpointMPO, scalarMPO,
        physicalInvolution, virtualInvolution, Matrix.diagonal_apply,
        Matrix.single_apply, Fin.sum_univ_succ, finSumFinEquiv, finProdFinEquiv,
        Fin.addCases, Fin.divNat, Fin.modNat, Matrix.one_apply]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨finProdFinEquiv (r, r), rfl⟩)

private theorem mixed_boundary_entries (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    MPOTensor.mpoWithBoundary mixedMPO Y 2 ![0, 2] ![0, 2] = 3 * Y 1 0 ∧
    MPOTensor.mpoWithBoundary mixedMPO Y 2 ![0, 2] ![0, 5] = 2 * Y 1 0 ∧
    MPOTensor.mpoWithBoundary mixedMPO Y 2 ![0, 5] ![0, 2] = -4 * Y 1 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  norm_num [MPOTensor.mpoWithBoundary, List.ofFn_succ, MPOTensor.evalWord,
    mixedMPO, mixedEndpointMPO, mixedEndpointMPOLetter, mixedEndpointPhysicalEquiv,
    endpointMPO, scalarMPO, physicalInvolution, virtualInvolution,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply,
    finSumFinEquiv, finProdFinEquiv, Fin.addCases, Fin.divNat, Fin.modNat, Matrix.one_apply]
  <;> ring

/-- Despite adjoint-closed, unitary endpoint symmetries, the mixed two-site
boundary range is not adjoint-closed. Its corner entries force incompatible
values for the same coefficient of any proposed adjoint boundary. -/
theorem not_mixed_adjoint_closed :
    ¬ (∀ X : Matrix (Fin 2) (Fin 2) ℂ, ∃ Y,
      (MPOTensor.mpoWithBoundary mixedMPO X 2)ᴴ =
        MPOTensor.mpoWithBoundary mixedMPO Y 2) := by
  intro h
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  obtain ⟨Y, hY⟩ := h X
  have hd := congrArg (fun M => M ![0, 2] ![0, 2]) hY
  have ho := congrArg (fun M => M ![0, 2] ![0, 5]) hY
  simp only [Matrix.conjTranspose_apply, (mixed_boundary_entries X).1,
    (mixed_boundary_entries Y).1] at hd
  simp only [Matrix.conjTranspose_apply, (mixed_boundary_entries X).2.2,
    (mixed_boundary_entries Y).2.1] at ho
  norm_num [X] at hd ho
  have hd' := congrArg Complex.re hd
  have ho' := congrArg Complex.re ho
  simp at hd' ho'
  linarith

end MPSTensor.MPOSymmetry.MixedEndpointAdjointObstruction
