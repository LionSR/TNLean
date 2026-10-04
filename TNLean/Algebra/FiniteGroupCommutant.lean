/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SignedPermutationSpan
import QICLean.Algebra.MatrixReindexUnitary
import QICLean.Algebra.ScalarCommutant
import QICLean.Algebra.StarSubalgebraBlockForm
import Mathlib.Algebra.Group.Commute.Hom

/-!
# Unital matrix C*-algebras as finite-group commutants

For every unital star-subalgebra of complex matrices, a finite group has a
unitary representation whose commutant is exactly that subalgebra. The unitary
block decomposition is derived internally. Independent signed permutation
groups act on the multiplicity factors; their spans are the full matrix
algebras on those factors. The block commutant calculation and the unitary
change of basis give the unital version of SCP10, Theorem 4.1
(arXiv:1001.3807, local source lines 852–885). The empty matrix index type is allowed.

**Local fix (unital subalgebras):** The source defines C*-algebras without
requiring the ambient identity (lines 561–563), so its printed Theorem 4.1
cannot hold literally: every commutant contains the identity. This module proves
the corrected unital version, whose block decomposition has no zero block.
The printed obstruction and the support-compression repair are documented in
`docs/paper-gaps/scp10_finite_group_commutant_unital.tex`.
-/

open scoped Matrix
noncomputable section
namespace TNLean

open scoped Kronecker

/-- Independent signed permutation groups act on the multiplicity factors.
Source: SCP10, Theorem 4.1, block construction in lines 864–885. -/
def blockSignedPermutationRepresentation {K : ℕ} (m d : Fin K → ℕ) :
    ((k : Fin K) → signedPermutationSubgroup (Fin (m k))) →*
      Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ where
  toFun g := Matrix.blockDiagonal' fun k =>
    signedPermutationRepresentation (Fin (m k)) (g k) ⊗ₖ (1 : Matrix (Fin (d k)) _ ℂ)
  map_one' := by
    simp only [Pi.one_apply, map_one, Matrix.one_kronecker_one]
    change Matrix.blockDiagonal' (1 : ∀ k, Matrix (Fin (m k) × Fin (d k)) _ ℂ) = 1
    exact Matrix.blockDiagonal'_one
  map_mul' g h := by
    simp only [Pi.mul_apply, map_mul]
    rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext k
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The independent-block representation is unitary.
Source: SCP10, Theorem 4.1, block construction in lines 864–885. -/
theorem blockSignedPermutationRepresentation_mem_unitaryGroup {K : ℕ}
    (m d : Fin K → ℕ) (g : (k : Fin K) → signedPermutationSubgroup (Fin (m k))) :
    blockSignedPermutationRepresentation m d g ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (Matrix.blockDiagonal' (fun k =>
    signedPermutationRepresentation (Fin (m k)) (g k) ⊗ₖ
      (1 : Matrix (Fin (d k)) _ ℂ))).conjTranspose *
      Matrix.blockDiagonal' (fun k =>
        signedPermutationRepresentation (Fin (m k)) (g k) ⊗ₖ (1 : Matrix (Fin (d k)) _ ℂ)) = 1
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul]
  have hg (k : Fin K) :
      (signedPermutationRepresentation (Fin (m k)) (g k)).conjTranspose *
        signedPermutationRepresentation (Fin (m k)) (g k) = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp
      (signedPermutationRepresentation_mem_unitaryGroup (Fin (m k)) (g k)))
  simp only [hg, Matrix.one_mul, Matrix.one_kronecker_one]
  exact Matrix.blockDiagonal'_one


private def blockMultiplicityMap {K : ℕ} (m d : Fin K → ℕ) :
    ((k : Fin K) → Matrix (Fin (m k)) (Fin (m k)) ℂ) →ₗ[ℂ]
      Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ where
  toFun C := Matrix.blockDiagonal' fun k => C k ⊗ₖ (1 : Matrix (Fin (d k)) _ ℂ)
  map_add' C D := by
    simp only [Pi.add_apply, Matrix.add_kronecker]
    exact Matrix.blockDiagonal'_add _ _
  map_smul' c C := by
    simp only [Pi.smul_apply, Matrix.smul_kronecker]
    exact Matrix.blockDiagonal'_smul (R := ℂ) c _

private theorem blockMultiplicityMap_mem_span {K : ℕ} (m d : Fin K → ℕ)
    (C : (k : Fin K) → Matrix (Fin (m k)) (Fin (m k)) ℂ) :
    blockMultiplicityMap m d C ∈
      Submodule.span ℂ (Set.range (blockSignedPermutationRepresentation m d)) := by
  classical
  let T := Submodule.span ℂ (Set.range (blockSignedPermutationRepresentation m d))
  have hunit (k : Fin K) (i j : Fin (m k)) :
      blockMultiplicityMap m d (Pi.single k (Matrix.single i j 1)) ∈ T := by
    obtain ⟨g, h, he⟩ := exists_signedPermutationRepresentation_sub_eq_single (Fin (m k)) i j
    let x := Function.update (1 : (k : Fin K) → signedPermutationSubgroup (Fin (m k))) k g
    let y := Function.update (1 : (k : Fin K) → signedPermutationSubgroup (Fin (m k))) k h
    have hf : (1 / 2 : ℂ) •
        ((fun l => signedPermutationRepresentation (Fin (m l)) (x l)) -
          (fun l => signedPermutationRepresentation (Fin (m l)) (y l))) =
        Pi.single k (Matrix.single i j 1) := by
      funext l
      by_cases hl : l = k
      · subst l
        simpa [x, y] using he
      · simp [x, y, hl]
    have hm := congrArg (blockMultiplicityMap m d) hf
    simp only [map_smul, map_sub] at hm
    rw [← hm]
    exact T.smul_mem _ (T.sub_mem (Submodule.subset_span ⟨x, rfl⟩)
      (Submodule.subset_span ⟨y, rfl⟩))
  have hall (k : Fin K) (B : Matrix (Fin (m k)) (Fin (m k)) ℂ) :
      blockMultiplicityMap m d (Pi.single k B) ∈ T := by
    let E := (blockMultiplicityMap m d).comp (LinearMap.single ℂ
      (fun k => Matrix (Fin (m k)) (Fin (m k)) ℂ) k)
    have htop : T.comap E = ⊤ := Submodule.eq_top_of_forall_single_mem _ (hunit k)
    have hB : B ∈ T.comap E := by rw [htop]; trivial
    exact hB
  have hc : C = ∑ k, Pi.single k (C k) := by
    symm
    funext l
    simpa only [Finset.sum_apply] using Fintype.sum_pi_single l C
  rw [hc, map_sum]
  exact T.sum_mem (fun k _ => hall k (C k))


private def blockTensorSwap {K : ℕ} (m d : Fin K → ℕ) :
    ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃
      ((k : Fin K) × (Fin (d k) × Fin (m k))) :=
  Equiv.sigmaCongrRight (fun _ => Equiv.prodComm _ _)

private theorem reindex_blockTensorSwap {K : ℕ} (m d : Fin K → ℕ)
    (C : (k : Fin K) → Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (B : (k : Fin K) → Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    Matrix.reindex (blockTensorSwap m d) (blockTensorSwap m d)
      (Matrix.blockDiagonal' fun k => C k ⊗ₖ B k) =
      Matrix.blockDiagonal' fun k => B k ⊗ₖ C k := by
  classical
  ext ⟨i, a, b⟩ ⟨j, c, e⟩
  change (Matrix.blockDiagonal' fun k => C k ⊗ₖ B k) ⟨i, (b, a)⟩ ⟨j, (e, c)⟩ =
    (Matrix.blockDiagonal' fun k => B k ⊗ₖ C k) ⟨i, (a, b)⟩ ⟨j, (c, e)⟩
  by_cases h : i = j
  · subst j
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply]
    exact mul_comm _ _
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,
      Matrix.blockDiagonal'_apply_ne _ _ _ h]

private theorem commutes_blockMultiplicityMap_iff {K : ℕ} (m d : Fin K → ℕ)
    (X : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ) :
    (∀ C, Commute X (blockMultiplicityMap m d C)) ↔
      ∃ B : (k : Fin K) → Matrix (Fin (d k)) (Fin (d k)) ℂ,
        X = Matrix.blockDiagonal' fun k => (1 : Matrix (Fin (m k)) _ ℂ) ⊗ₖ B k := by
  classical
  let e := blockTensorSwap m d
  let E := Matrix.reindexLinearEquiv ℂ ℂ e e
  have hmul (A B) : E A * E B = E (A * B) :=
    Matrix.reindexLinearEquiv_mul ℂ ℂ e e e A B
  have he (C) : E (blockMultiplicityMap m d C) =
      Matrix.blockDiagonal' fun k => (1 : Matrix (Fin (d k)) _ ℂ) ⊗ₖ C k :=
    reindex_blockTensorSwap m d C (fun _ => 1)
  have hcomm : (∀ C, Commute X (blockMultiplicityMap m d C)) ↔
      ∀ C : (k : Fin K) → Matrix (Fin (m k)) (Fin (m k)) ℂ,
        E X * Matrix.blockDiagonal' (fun k => (1 : Matrix (Fin (d k)) _ ℂ) ⊗ₖ C k) =
        Matrix.blockDiagonal' (fun k => (1 : Matrix (Fin (d k)) _ ℂ) ⊗ₖ C k) * E X := by
    simp only [← he, hmul, E.injective.eq_iff, Commute, SemiconjBy]
  rw [hcomm, Matrix.commutes_blockDiagonal'_one_kronecker_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, E.injective ?_⟩
    rw [hB]
    exact (reindex_blockTensorSwap m d (fun _ => 1) B).symm
  · rintro ⟨B, rfl⟩
    exact ⟨B, reindex_blockTensorSwap m d (fun _ => 1) B⟩


/-- The independent signed permutation groups have exactly the prescribed block commutant.
Source: SCP10, Theorem 4.1, Schur-commutant step in lines 876–885. -/
theorem commutes_blockSignedPermutationRepresentation_iff {K : ℕ} (m d : Fin K → ℕ)
    (X : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ) :
    (∀ g, Commute X (blockSignedPermutationRepresentation m d g)) ↔
      ∃ B : (k : Fin K) → Matrix (Fin (d k)) (Fin (d k)) ℂ,
        X = Matrix.blockDiagonal' fun k => (1 : Matrix (Fin (m k)) _ ℂ) ⊗ₖ B k := by
  rw [← commutes_blockMultiplicityMap_iff]
  constructor
  · intro h C
    apply Commute.span_right (fun Y hY => ?_) _ (blockMultiplicityMap_mem_span m d C)
    obtain ⟨g, rfl⟩ := hY
    exact h g
  · intro h g
    exact h (fun k => signedPermutationRepresentation (Fin (m k)) (g k))


private def unitaryConjugation {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ where
  toFun A := W * A * star W
  invFun A := star W * A * W
  left_inv A := by
    change star W * (W * A * star W) * W = A
    calc
      _ = (star W * W) * A * (star W * W) := by simp only [mul_assoc]
      _ = A := by rw [hW.1]; simp
  right_inv A := by
    change W * (star W * A * W) * star W = A
    calc
      _ = (W * star W) * A * (W * star W) := by simp only [mul_assoc]
      _ = A := by rw [hW.2]; simp
  map_mul' A B := by
    calc
      W * (A * B) * star W = W * A * (star W * W) * B * star W := by rw [hW.1]; simp [mul_assoc]
      _ = (W * A * star W) * (W * B * star W) := by simp only [mul_assoc]
  map_add' A B := by simp only [mul_add, add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hW.2]


/-- Every unital complex matrix star-subalgebra is the commutant of a unitary
representation of a finite group. No decomposition is assumed, and the empty
matrix index type is allowed. Source: SCP10, Theorem 4.1, lines 852–885. -/
theorem _root_.StarSubalgebra.exists_finite_unitary_group_commutant
    {n : Type*} [Fintype n] [DecidableEq n]
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (U : G →* Matrix n n ℂ),
      (∀ g, U g ∈ Matrix.unitaryGroup n ℂ) ∧
        ∀ A : Matrix n n ℂ, A ∈ S ↔ ∀ g, Commute A (U g) := by
  classical
  obtain ⟨K, d, m, e, W, hW, _hd, _hm, hS⟩ := S.exists_unitary_conj_blockDiagonal_iff
  let G := (k : Fin K) → signedPermutationSubgroup (Fin (m k))
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  let F := E.trans (unitaryConjugation W hW)
  let U : G →* Matrix n n ℂ :=
    { toFun := fun g => F (blockSignedPermutationRepresentation m d g)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun g h => by rw [map_mul, map_mul] }
  refine ⟨G, inferInstance, inferInstance, U, ?_, ?_⟩
  · intro g
    change W * Matrix.reindex e e (blockSignedPermutationRepresentation m d g) * star W ∈ _
    exact (Matrix.unitaryGroup n ℂ).mul_mem
      ((Matrix.unitaryGroup n ℂ).mul_mem hW
        (Matrix.reindex_mem_unitaryGroup e _
          (blockSignedPermutationRepresentation_mem_unitaryGroup m d g)))
      (Unitary.star_mem hW)
  · intro A
    have hcomm : (∀ g, Commute A (U g)) ↔
        ∀ g, Commute (F.symm A) (blockSignedPermutationRepresentation m d g) := by
      constructor
      · intro h g
        apply (commute_map_iff F.injective).mp
        have hg := h g
        change Commute A (F (blockSignedPermutationRepresentation m d g)) at hg
        simpa only [AlgEquiv.apply_symm_apply] using hg
      · intro h g
        change Commute A (F (blockSignedPermutationRepresentation m d g))
        simpa only [AlgEquiv.apply_symm_apply] using (h g).map F
    rw [hcomm, commutes_blockSignedPermutationRepresentation_iff]
    rw [hS A]
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B, ?_⟩
      change E.symm (star W * A * W) = _
      rw [hB]
      exact E.symm_apply_apply _
    · rintro ⟨B, hB⟩
      refine ⟨B, ?_⟩
      change E.symm (star W * A * W) = _ at hB
      change star W * A * W = E (Matrix.blockDiagonal' fun k =>
        (1 : Matrix (Fin (m k)) _ ℂ) ⊗ₖ B k)
      simpa only [AlgEquiv.apply_symm_apply] using congrArg E hB

end TNLean
