/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StarSubalgebraBlockForm

/-!
# Commuting overlapping operators

This file begins the matrix passage in the Bravyi--Vyalyi spatial decomposition for two
commuting overlapping Hermitian operators. It defines their natural embeddings on a
three-factor space and the middle-factor coefficient matrices obtained by fixing the outer
indices.

## Main results

* `Matrix.middleSlices_commute_of_overlappingLifts_commute` -- commutation of the two
  overlapping operators implies pairwise commutation of all their middle-factor coefficient
  matrices.
* `Matrix.exists_middle_spatial_decomposition_of_overlappingLifts_commute` -- one
  orthonormal decomposition of the middle space puts the coefficient families of the two
  overlapping operators on complementary tensor factors.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting Hamiltonians*,
  arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`) and its proof on pages 2--3.
-/

namespace Matrix

variable {a b c : Type*}
variable [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The natural embedding of an operator on the first two factors into the three-factor
space.

Source: Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`). -/
def leftOverlappingLift (X : Matrix (a × b) (a × b) ℂ) :
    Matrix ((a × b) × c) ((a × b) × c) ℂ :=
  fun p q ↦ X p.1 q.1 * (1 : Matrix c c ℂ) p.2 q.2

/-- The natural embedding of an operator on the last two factors into the three-factor
space.

Source: Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`). -/
def rightOverlappingLift (Y : Matrix (b × c) (b × c) ℂ) :
    Matrix ((a × b) × c) ((a × b) × c) ℂ :=
  fun p q ↦ (1 : Matrix a a ℂ) p.1.1 q.1.1 * Y (p.1.2, p.2) (q.1.2, q.2)

/-- The middle-factor coefficient matrix of an operator on the first two factors, with
the two first-factor indices fixed.

Source: Beigi, arXiv:1105.1019v2, proof of Lemma 2.1 (`lem:comm`). -/
def leftMiddleSlice (X : Matrix (a × b) (a × b) ℂ) (i i' : a) : Matrix b b ℂ :=
  fun j j' ↦ X (i, j) (i', j')

/-- The middle-factor coefficient matrix of an operator on the last two factors, with
the two last-factor indices fixed.

Source: Beigi, arXiv:1105.1019v2, proof of Lemma 2.1 (`lem:comm`). -/
def rightMiddleSlice (Y : Matrix (b × c) (b × c) ℂ) (k k' : c) : Matrix b b ℂ :=
  fun j j' ↦ Y (j, k) (j', k')

omit [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c] in
/-- Hermiticity exchanges the two outer indices of a middle-factor coefficient matrix.

Source: Beigi, arXiv:1105.1019v2, proof of Lemma 2.1 (`lem:comm`). -/
theorem star_rightMiddleSlice (Y : Matrix (b × c) (b × c) ℂ) (hY : Y.IsHermitian)
    (k k' : c) : star (rightMiddleSlice Y k k') = rightMiddleSlice Y k' k := by
  ext i j
  change star (Y (j, k) (i, k')) = Y (i, k') (j, k)
  exact hY.apply (i, k') (j, k)

omit [DecidableEq b] in
/-- If two operators on the first--middle and middle--last tensor factors commute after
their natural embeddings, then every middle-factor coefficient matrix of the first
operator commutes with every middle-factor coefficient matrix of the second operator.

This is the coefficientwise consequence of
`[X_{AB} \otimes \mathbf 1_C, \mathbf 1_A \otimes Y_{BC}] = 0` used before the
finite-dimensional star-algebra decomposition in S. Beigi, arXiv:1105.1019v2,
proof of Lemma 2.1 (`lem:comm`), pages 2--3. Hermiticity is not needed for this
coefficientwise implication. -/
theorem middleSlices_commute_of_overlappingLifts_commute
    (X : Matrix (a × b) (a × b) ℂ) (Y : Matrix (b × c) (b × c) ℂ)
    (hComm : leftOverlappingLift X * rightOverlappingLift Y =
      rightOverlappingLift Y * leftOverlappingLift X) (i i' : a) (k k' : c) :
    leftMiddleSlice X i i' * rightMiddleSlice Y k k' =
      rightMiddleSlice Y k k' * leftMiddleSlice X i i' := by
  ext j j'
  have h := congrFun (congrFun hComm ((i, j), k)) ((i', j'), k')
  simpa [leftOverlappingLift, rightOverlappingLift, leftMiddleSlice, rightMiddleSlice,
    Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type] using h

/-- **Middle-space spatial decomposition for commuting overlapping operators.** Suppose
operators `X` on the first--middle factors and `Y` on the middle--last factors commute after
their natural embeddings, and suppose `Y` is Hermitian. There is an orthonormal basis
`(e_{q,r,s})` of the middle space such that every coefficient matrix of `X` acts on the
`s` index, identically across `r`, and every coefficient matrix of `Y` acts on the
complementary `r` index, identically across `s`:
$$
 X_{ii'}e_{q,r,s}=\sum_{s'}(B^{ii'}_q)_{s's}e_{q,r,s'},\qquad
 Y_{kk'}e_{q,r,s}=\sum_{r'}(C^{kk'}_q)_{r'r}e_{q,r',s}.
$$
The dimensions of both factors in every summand are positive. Thus, up to the order of the
two tensor factors, the basis realizes
`H_B \cong \bigoplus_q H_{q,l}\otimes H_{q,r}` with complementary actions of the two
operator families.

This is the middle-space conclusion of the Bravyi--Vyalyi decomposition in S. Beigi,
arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`). The source assumes both `X` and `Y` Hermitian;
the proof below uses Hermiticity only for `Y`, because it applies the star-subalgebra
decomposition to the commutant of the coefficient matrices of `Y`. -/
theorem exists_middle_spatial_decomposition_of_overlappingLifts_commute
    (X : Matrix (a × b) (a × b) ℂ) (Y : Matrix (b × c) (b × c) ℂ)
    (hY : Y.IsHermitian)
    (hComm : leftOverlappingLift X * rightOverlappingLift Y =
      rightOverlappingLift Y * leftOverlappingLift X) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : OrthonormalBasis ((q : Fin K) × (Fin (m q) × Fin (d q))) ℂ
        (EuclideanSpace ℂ b)),
      (∀ q, 0 < d q) ∧ (∀ q, 0 < m q) ∧
        (∀ i i' : a, ∃ B : ∀ q, Matrix (Fin (d q)) (Fin (d q)) ℂ,
          ∀ (q : Fin K) (r : Fin (m q)) (s : Fin (d q)),
            Matrix.toEuclideanLin (leftMiddleSlice X i i') (e ⟨q, (r, s)⟩) =
              ∑ s', B q s' s • e ⟨q, (r, s')⟩) ∧
        ∀ k k' : c, ∃ C : ∀ q, Matrix (Fin (m q)) (Fin (m q)) ℂ,
          ∀ (q : Fin K) (r : Fin (m q)) (s : Fin (d q)),
            Matrix.toEuclideanLin (rightMiddleSlice Y k k') (e ⟨q, (r, s)⟩) =
              ∑ r', C q r' r • e ⟨q, (r', s)⟩ := by
  let S : StarSubalgebra ℂ (Matrix b b ℂ) :=
    StarSubalgebra.centralizer ℂ
      (Set.range fun p : c × c ↦ rightMiddleSlice Y p.1 p.2)
  obtain ⟨K, d, m, e, hd, hm, hS, hScomm⟩ :=
    S.exists_complementary_action_orthonormalBasis
  refine ⟨K, d, m, e, hd, hm, ?_, ?_⟩
  · intro i i'
    apply hS
    change leftMiddleSlice X i i' ∈ StarSubalgebra.centralizer ℂ
      (Set.range fun p : c × c ↦ rightMiddleSlice Y p.1 p.2)
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro g ⟨⟨k, k'⟩, rfl⟩
    dsimp
    constructor
    · exact (middleSlices_commute_of_overlappingLifts_commute X Y hComm i i' k k').symm
    · rw [star_rightMiddleSlice Y hY]
      exact (middleSlices_commute_of_overlappingLifts_commute X Y hComm i i' k' k).symm
  · intro k k'
    apply hScomm
    intro A hA
    change A ∈ StarSubalgebra.centralizer ℂ
      (Set.range fun p : c × c ↦ rightMiddleSlice Y p.1 p.2) at hA
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hA _ ⟨(k, k'), rfl⟩).1

end Matrix
