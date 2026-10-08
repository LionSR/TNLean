/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryClosedness

/-!
# Algebraic boundary closedness does not imply adjoint closedness

The bond-one tensor with physical matrix \(P=\begin{pmatrix}1&1\\0&0\end{pmatrix}\)
is one-site injective and satisfies the exact local identity \(P^2=P\). Its
arbitrary-boundary operators are therefore closed under products with a single
output boundary for every positive length. It is likewise compatible with the
bond-one state \(|0\rangle\), which is also one-site injective.

Nevertheless, already at length one every boundary operator has zero lower
row, whereas \(P^\dagger\) has a nonzero lower-left entry. Thus even injectivity,
algebraic closedness and compatibility together do not give physical adjoint
closedness.

This is a newly derived counterexample to that implication. It is not a
counterexample to the weak-Hopf or physical star-representation assumptions in
Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3. It explains why deriving
adjoint closure from the algebraic condition `algcond` alone is insufficient.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.BoundaryAdjointCounterexample

/-- Bond-one tensor whose physical matrix is the nonorthogonal idempotent
\(P=\begin{pmatrix}1&1\\0&0\end{pmatrix}\). -/
def tensor : MPOTensor 2 1 := fun i _ ↦ if i = 0 then 1 else 0

/-- The bond-one product state \(|0\rangle\). -/
def state : MPSTensor 2 1 := fun i ↦ if i = 0 then 1 else 0

private theorem isInjective_of_letter_eq_one {d : ℕ} (A : MPSTensor d 1)
    (i : Fin d) (hi : A i = 1) : Kraus.IsInjective A := by
  rw [Kraus.IsInjective]
  apply top_unique
  intro X _
  have hOne : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Submodule.span ℂ (Set.range A) := Submodule.subset_span ⟨i, hi⟩
  have hX : X = X 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext a b
    fin_cases a
    fin_cases b
    simp
  rw [hX]
  exact Submodule.smul_mem _ _ hOne

/-- The flattened operator tensor is already injective without blocking. -/
theorem tensor_isInjective : Kraus.IsInjective tensor.toMPSTensor :=
  isInjective_of_letter_eq_one _ (0 : Fin (2 * 2)) (by rfl)

/-- The state tensor is already injective without blocking. -/
theorem state_isInjective : Kraus.IsInjective state :=
  isInjective_of_letter_eq_one _ 0 (by simp [state])

/-- In particular, the operator tensor is normal. -/
theorem tensor_isNormal : Kraus.IsNormal tensor.toMPSTensor :=
  tensor_isInjective.isNormal

/-- In particular, the state tensor is normal. -/
theorem state_isNormal : Kraus.IsNormal state := state_isInjective.isNormal

/-- The exact local fusion equation is the idempotence of the physical matrix. -/
theorem mulTensor_tensor : mulTensor tensor tensor = tensor := by
  funext i j
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [mulTensor, tensor, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply]

/-- The exact local action equation is \(P|0\rangle=|0\rangle\). -/
theorem actTensor_state : actTensor tensor state = state := by
  funext i
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [actTensor, tensor, state, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply]

/-- Product closedness holds for arbitrary boundaries with one output boundary
working simultaneously at every positive length. -/
theorem tensor_isBoundaryClosed : IsBoundaryClosed tensor := by
  apply isBoundaryClosed_of_biorthogonalDecomposition tensor
    (fun _ : Unit ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ : Unit ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ))
  refine ⟨fun _ ↦ by simp, fun c b h ↦ (h (Subsingleton.elim c b)).elim, ?_⟩
  intro i
  rw [mulTensor_tensor]
  simp

/-- Compatibility likewise uses one output state boundary at all positive
lengths, rather than separate fixed-length invariance assumptions. -/
theorem tensor_isBoundaryCompatible : IsBoundaryCompatible tensor state := by
  apply isBoundaryCompatible_of_biorthogonalDecomposition tensor state
    (fun _ : Unit ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ : Unit ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ))
  refine ⟨fun _ ↦ by simp, fun c b h ↦ (h (Subsingleton.elim c b)).elim, ?_⟩
  intro i
  rw [actTensor_state]
  simp

/-- Every bond-one boundary commutes with all tensor letters. -/
theorem mem_commutingBoundaryAlgebra (X : Matrix (Fin 1) (Fin 1) ℂ) :
    X ∈ MPOTensor.commutingBoundaryAlgebra tensor := by
  rw [mem_commutingBoundaryAlgebra_iff]
  intro i j
  by_cases hi : i = 0 <;> simp [tensor, hi]

/-- At one site the arbitrary boundary gives the scalar multiple \(X_{00}P\). -/
theorem boundary_one_apply (X : Matrix (Fin 1) (Fin 1) ℂ)
    (σ τ : Fin 1 → Fin 2) :
    mpoWithBoundary tensor X 1 σ τ = if σ 0 = 0 then X 0 0 else 0 := by
  by_cases hσ : σ 0 = 0 <;>
    simp [mpoWithBoundary, List.ofFn_succ, tensor, hσ, Matrix.trace]

/-- The one-site state boundary produces \(X_{00}|0\rangle\). -/
theorem state_boundary_one_apply (X : Matrix (Fin 1) (Fin 1) ℂ)
    (σ : Fin 1 → Fin 2) :
    MPSTensor.mpvWithBoundary state X σ = if σ 0 = 0 then X 0 0 else 0 := by
  by_cases hσ : σ 0 = 0 <;>
    simp [MPSTensor.mpvWithBoundary, List.ofFn_succ, state, hσ, Matrix.trace]

/-- The adjoint of the identity-boundary operator is outside the full boundary
range: its lower-left entry is one, while every boundary operator's is zero. -/
theorem adjoint_not_mem_boundaryRange :
    (mpoWithBoundary tensor 1 1)ᴴ ∉
      Set.range (fun X : Matrix (Fin 1) (Fin 1) ℂ ↦ mpoWithBoundary tensor X 1) := by
  rintro ⟨Y, hY⟩
  have h := congrArg (fun M ↦ M (fun _ ↦ (1 : Fin 2)) (fun _ ↦ (0 : Fin 2))) hY
  change mpoWithBoundary tensor Y 1 (fun _ ↦ 1) (fun _ ↦ 0) =
    star (mpoWithBoundary tensor 1 1 (fun _ ↦ 0) (fun _ ↦ 1)) at h
  simp only [boundary_one_apply] at h
  norm_num at h

/-- Algebraic closedness, even with normality and a compatible injective state,
does not supply the adjoint-closure hypothesis for the whole boundary range. -/
theorem not_boundaryAdjointClosed :
    ¬ ∀ X : Matrix (Fin 1) (Fin 1) ℂ, ∃ Y : Matrix (Fin 1) (Fin 1) ℂ,
      (mpoWithBoundary tensor X 1)ᴴ = mpoWithBoundary tensor Y 1 := by
  intro h
  obtain ⟨Y, hY⟩ := h 1
  exact adjoint_not_mem_boundaryRange ⟨Y, hY.symm⟩

end MPOTensor.BoundaryAdjointCounterexample
