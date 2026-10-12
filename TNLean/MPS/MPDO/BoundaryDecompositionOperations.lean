/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryTransport
import TNLean.MPS.MPDO.ActionTensorReduction

/-!
# Composition and action of exact boundary decompositions

Exact biorthogonal decompositions compose along finite two-stage paths,
remain exact under a rectangular change of ambient support coordinates,
and pass through either factor of an MPO action tensor.

These operations construct the two actual fusion/action trees used for
multiplicity L-symbols. They assume no change-of-basis matrix or coherence
equation.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`, lines 491--552.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.IsBiorthogonalDecomposition

/-- Substitution of exact block decompositions produces the exact
decomposition indexed by two-stage paths. Source: GLM23 `rawrels`. -/
theorem comp
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {d DB : ℕ} {D : ι → ℕ} {E : ∀ i, κ i → ℕ}
    {B : MPSTensor d DB} {A : ∀ i, MPSTensor d (D i)}
    {V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ}
    {W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ}
    (h : IsBiorthogonalDecomposition B A V W)
    (C : ∀ i j, MPSTensor d (E i j))
    (V' : ∀ i j, Matrix (Fin (E i j)) (Fin (D i)) ℂ)
    (W' : ∀ i j, Matrix (Fin (D i)) (Fin (E i j)) ℂ)
    (h' : ∀ i, IsBiorthogonalDecomposition (A i) (C i) (V' i) (W' i)) :
    IsBiorthogonalDecomposition B (fun q : (i : ι) × κ i ↦ C q.1 q.2)
      (fun q ↦ V' q.1 q.2 * V q.1) (fun q ↦ W q.1 * W' q.1 q.2) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    change (V' i j * V i) * (W i * W' i j) = 1
    calc
      _ = V' i j * (V i * W i) * W' i j := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.retract, Matrix.mul_one, (h' i).retract]
  · rintro ⟨i, j⟩ ⟨k, l⟩ hne
    change (V' i j * V i) * (W k * W' k l) = 0
    calc
      _ = V' i j * (V i * W k) * W' k l := by simp only [Matrix.mul_assoc]
      _ = 0 := by
        by_cases hik : i = k
        · subst k
          have hjl : j ≠ l := by
            intro hjl
            subst l
            exact hne rfl
          rw [h.retract, Matrix.mul_one, (h' i).orthogonal j l hjl]
        · rw [h.orthogonal i k hik, Matrix.mul_zero, Matrix.zero_mul]
  · intro a
    rw [h.letter, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(h' i).letter, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by simp only [Matrix.mul_assoc]

/-- Embedding the ambient tensor through a rectangular retract transports
all exact decomposition maps. This includes invertible bond reassociation.
Source: GLM23 `rawrels`, the common incoming bond coordinates. -/
theorem sandwich
    {ι : Type*} [Fintype ι] {d DB DE : ℕ} {D : ι → ℕ}
    {B : MPSTensor d DB} {A : ∀ i, MPSTensor d (D i)}
    {V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ}
    {W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ}
    (h : IsBiorthogonalDecomposition B A V W)
    (P : Matrix (Fin DE) (Fin DB) ℂ) (Q : Matrix (Fin DB) (Fin DE) ℂ)
    (hQP : Q * P = 1) :
    IsBiorthogonalDecomposition (fun a ↦ P * B a * Q) A
      (fun i ↦ V i * Q) (fun i ↦ P * W i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    calc
      (V i * Q) * (P * W i) = V i * (Q * P) * W i := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, h.retract]
  · intro i j hij
    calc
      (V i * Q) * (P * W j) = V i * (Q * P) * W j := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQP, Matrix.mul_one, h.orthogonal i j hij]
  · intro a
    rw [h.letter, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [Matrix.mul_assoc]

/-- Exact decomposition of the state factor passes through a fixed MPO
action with identity strands on the operator bond. Source: GLM23 `rawrels`. -/
theorem actTensor_idKron
    {ι : Type*} [Fintype ι] {d DB DT : ℕ} {D : ι → ℕ}
    {B : MPSTensor d DB} {A : ∀ i, MPSTensor d (D i)}
    {V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ}
    {W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ}
    (h : IsBiorthogonalDecomposition B A V W) (T : MPOTensor d DT) :
    IsBiorthogonalDecomposition (MPOTensor.actTensor T B)
      (fun i ↦ MPOTensor.actTensor T (A i))
      (fun i ↦ MPOTensor.idKron DT (V i)) (fun i ↦ MPOTensor.idKron DT (W i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [MPOTensor.idKron_mul, h.retract, MPOTensor.idKron_one]
  · intro i j hij
    rw [MPOTensor.idKron_mul, h.orthogonal i j hij]
    simp [MPOTensor.idKron]
  · intro a
    simp only [MPOTensor.actTensor_apply, MPOTensor.idKron, Matrix.submatrix_mul_equiv]
    simp_rw [Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
    ext x y
    simp only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [h.letter j, Matrix.sum_apply, Finset.mul_sum]

/-- Exact decomposition of the operator factor passes through its action
on a fixed state, with identity strands on the state bond.
Source: GLM23 `rawrels`, the fusion-then-action tree. -/
theorem actTensor_kronId
    {ι : Type*} [Fintype ι] {d DT DB : ℕ} {D : ι → ℕ}
    {T : MPOTensor d DT} {S : ∀ i, MPOTensor d (D i)}
    {V : ∀ i, Matrix (Fin (D i)) (Fin DT) ℂ}
    {W : ∀ i, Matrix (Fin DT) (Fin (D i)) ℂ}
    (h : IsBiorthogonalDecomposition T.toMPSTensor
      (fun i ↦ (S i).toMPSTensor) V W) (B : MPSTensor d DB) :
    IsBiorthogonalDecomposition (MPOTensor.actTensor T B)
      (fun i ↦ MPOTensor.actTensor (S i) B)
      (fun i ↦ MPOTensor.kronId (V i) DB) (fun i ↦ MPOTensor.kronId (W i) DB) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [MPOTensor.kronId_mul, h.retract, MPOTensor.kronId_one]
  · intro i j hij
    rw [MPOTensor.kronId_mul, h.orthogonal i j hij]
    simp [MPOTensor.kronId]
  · intro a
    have hletter (j : Fin d) : T a j = ∑ i, W i * S i a j * V i := by
      simpa [MPOTensor.toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
        MPSTensor.finProdFinEquiv_modNat] using h.letter (finProdFinEquiv (a, j))
    simp only [MPOTensor.actTensor_apply, MPOTensor.kronId, Matrix.submatrix_mul_equiv]
    simp_rw [Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
    ext x y
    simp only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hletter j, Matrix.sum_apply, Finset.sum_mul]

end MPSTensor.IsBiorthogonalDecomposition
