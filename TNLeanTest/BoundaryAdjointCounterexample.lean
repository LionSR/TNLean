/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryAdjointCounterexample
import TNLean.MPS.ParentHamiltonian.MatrixRepresentation
import TNLean.MPS.ParentHamiltonian.NonzeroInteraction

/-!
# An injective algebraically closed boundary family without adjoint closure

These regressions use the concrete bond-one tensor with physical matrix
\(P=\begin{pmatrix}1&1\\0&0\end{pmatrix}\), rather than assuming any of the
conclusions. Both tensors are normal, all positive-length boundary products and
state actions close, but the one-site adjoint is outside the boundary range.
The actual canonical one-site parent of the compatible state is
\(\operatorname{diag}(0,1)\), and it does not commute with \(P\).

The example concerns the insufficiency of algebraic boundary closedness for
physical adjoint closedness. It makes no claim against the weak-Hopf or
physical star-representation assumptions of GLM23.
-/

set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPOTensor MPOTensor.BoundaryAdjointCounterexample

namespace BoundaryAdjointCounterexampleTest

private abbrev zeroConfig : Fin 1 → Fin 2 := fun _ ↦ 0
private abbrev oneConfig : Fin 1 → Fin 2 := fun _ ↦ 1

private theorem config_cases (σ : Fin 1 → Fin 2) :
    σ = zeroConfig ∨ σ = oneConfig := by
  have h : (fun _ : Fin 1 ↦ σ 0) = σ := by
    funext i
    congr 1
    exact Subsingleton.elim _ _
  generalize hi : σ 0 = i at h
  fin_cases i
  · exact Or.inl h.symm
  · exact Or.inr h.symm

private theorem sum_config_one (f : (Fin 1 → Fin 2) → ℂ) :
    ∑ σ, f σ = f zeroConfig + f oneConfig := by
  have h (i : Fin 2) : (uniqueElim i : Fin 1 → Fin 2) = fun _ ↦ i := by
    funext j
    exact uniqueElim_const i j
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  simp only [Fin.sum_univ_two, Equiv.funUnique_symm_apply, h]

private theorem zeroConfig_mem_groundSpace :
    Pi.single zeroConfig (1 : ℂ) ∈ MPSTensor.groundSpace state 1 := by
  classical
  refine ⟨1, ?_⟩
  rw [← MPSTensor.mpvWithBoundary_eq_groundSpaceMap]
  funext σ
  rw [state_boundary_one_apply]
  rcases config_cases σ with rfl | rfl <;>
    simp [zeroConfig, oneConfig, funext_iff]

/-- The actual canonical parent matrix is \(\operatorname{diag}(0,1)\), in
one-site configuration coordinates. This follows from its Hermitian projection
properties, its zero mode and the existing nonzero-interaction bound. -/
theorem parentInteraction_matrix_apply (σ τ : Fin 1 → Fin 2) :
    LinearMap.toMatrix' (MPSTensor.parentInteraction state 1) σ τ =
      if σ 0 = 1 ∧ τ 0 = 1 then 1 else 0 := by
  classical
  let H := LinearMap.toMatrix' (MPSTensor.parentInteraction state 1)
  have hstar := MPSTensor.parentInteraction_toMatrix'_isStarProjection state 1
  have hHerm : H.IsHermitian := hstar.isSelfAdjoint.isHermitian
  have hkill := MPSTensor.parentInteraction_apply_mem_groundSpace state 1
    (Pi.single zeroConfig 1) zeroConfig_mem_groundSpace
  have hcol (ρ : Fin 1 → Fin 2) : H ρ zeroConfig = 0 := by
    simpa only [H, LinearMap.toMatrix'_apply, Pi.zero_apply] using congrFun hkill ρ
  have hrow (ρ : Fin 1 → Fin 2) : H zeroConfig ρ = 0 := by
    simpa only [hcol, star_zero] using (hHerm.apply zeroConfig ρ).symm
  have hne : H oneConfig oneConfig ≠ 0 := by
    intro hzero
    apply MPSTensor.parentInteraction_ne_zero state 1 (by norm_num)
    apply LinearMap.toMatrix'.injective
    rw [map_zero]
    change H = 0
    ext ρ υ
    rcases config_cases ρ with rfl | rfl <;>
      rcases config_cases υ with rfl | rfl <;> simp [hcol, hrow, hzero]
  have hidem : H * H = H := hstar.isIdempotentElem.eq
  have hsq : (H oneConfig oneConfig) ^ 2 = H oneConfig oneConfig := by
    have h := congrArg (fun M ↦ M oneConfig oneConfig) hidem
    simpa [Matrix.mul_apply, sum_config_one, hcol, hrow, pow_two] using h
  have hdiag : H oneConfig oneConfig = 1 :=
    (eq_zero_or_one_of_sq_eq_self hsq).resolve_left hne
  change H σ τ = _
  rcases config_cases σ with rfl | rfl <;>
    rcases config_cases τ with rfl | rfl <;>
      simp [hcol, hrow, hdiag, zeroConfig, oneConfig]

/-- The canonical parent fails to commute with the identity-boundary MPO,
even though this boundary commutes with every virtual letter. -/
theorem not_parentInteraction_commute :
    ¬ Commute (LinearMap.toMatrix' (MPSTensor.parentInteraction state 1))
      (mpoWithBoundary tensor 1 1) := by
  intro h
  have hentry := congrArg (fun M ↦ M zeroConfig oneConfig) h.eq
  simp only [Matrix.mul_apply, sum_config_one, parentInteraction_matrix_apply,
    boundary_one_apply] at hentry
  norm_num [zeroConfig, oneConfig] at hentry

-- Each premise in this counterexample is proved from its concrete letters.
example : Kraus.IsInjective tensor.toMPSTensor ∧ Kraus.IsInjective state ∧
    Kraus.IsNormal tensor.toMPSTensor ∧ Kraus.IsNormal state ∧
    IsBoundaryClosed tensor ∧ IsBoundaryCompatible tensor state ∧
    ¬ (∀ X : Matrix (Fin 1) (Fin 1) ℂ, ∃ Y : Matrix (Fin 1) (Fin 1) ℂ,
      (mpoWithBoundary tensor X 1)ᴴ = mpoWithBoundary tensor Y 1) :=
  ⟨tensor_isInjective, state_isInjective, tensor_isNormal, state_isNormal,
    tensor_isBoundaryClosed, tensor_isBoundaryCompatible, not_boundaryAdjointClosed⟩

-- The failure already occurs for a translation-invariant admissible boundary.
example : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ commutingBoundaryAlgebra tensor ∧
    ¬ Commute (LinearMap.toMatrix' (MPSTensor.parentInteraction state 1))
      (mpoWithBoundary tensor 1 1) :=
  ⟨mem_commutingBoundaryAlgebra 1, not_parentInteraction_commute⟩

end BoundaryAdjointCounterexampleTest

/-- info: 'MPOTensor.BoundaryAdjointCounterexample.tensor_isBoundaryClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.BoundaryAdjointCounterexample.tensor_isBoundaryClosed

/-- info: 'MPOTensor.BoundaryAdjointCounterexample.tensor_isBoundaryCompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.BoundaryAdjointCounterexample.tensor_isBoundaryCompatible

/-- info: 'MPOTensor.BoundaryAdjointCounterexample.not_boundaryAdjointClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.BoundaryAdjointCounterexample.not_boundaryAdjointClosed

/-- info: 'BoundaryAdjointCounterexampleTest.not_parentInteraction_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundaryAdjointCounterexampleTest.not_parentInteraction_commute
