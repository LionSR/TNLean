/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OperatorBlock
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
* `Matrix.exists_unitary_blockActions_of_overlappingLifts_commute` -- the corresponding
  explicit unitary direct-sum representation, with Hermitian operators on the two
  complementary factors and the two block identities of Beigi's lemma.
* `Matrix.exists_unitary_blockSum_equalities_of_overlappingLifts_commute` -- the same
  identities solved for the original two overlapping operators.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting Hamiltonians*,
  J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`) and its proof on pages 2--3.
-/

open scoped InnerProductSpace Kronecker

namespace OrthonormalBasis

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem exists_unitary_conj_toMatrix {K : ℕ} {d m : Fin K → ℕ}
    (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ
      (EuclideanSpace ℂ n)) :
    ∃ (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n) (U : Matrix n n ℂ),
      U ∈ Matrix.unitaryGroup n ℂ ∧
        ∀ A : Matrix n n ℂ,
          star U * A * U = Matrix.reindex e e
            (LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A)) := by
  classical
  set s : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
    EuclideanSpace.basisFun n ℂ with hs
  set e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n :=
    b.toBasis.indexEquiv s.toBasis with he
  set b' : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b.reindex e with hb'
  refine ⟨e, s.toBasis.toMatrix ⇑b'.toBasis,
    s.toMatrix_orthonormalBasis_mem_unitary b', fun A ↦ ?_⟩
  have hstar : star (s.toBasis.toMatrix ⇑b'.toBasis) =
      b'.toBasis.toMatrix ⇑s.toBasis := by
    have h1 : star (s.toBasis.toMatrix ⇑b'.toBasis) *
        s.toBasis.toMatrix ⇑b'.toBasis = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (s.toMatrix_orthonormalBasis_mem_unitary b')
    have h2 : s.toBasis.toMatrix ⇑b'.toBasis *
        b'.toBasis.toMatrix ⇑s.toBasis = 1 :=
      Module.Basis.toMatrix_mul_toMatrix_flip _ _
    calc
      star (s.toBasis.toMatrix ⇑b'.toBasis) =
          star (s.toBasis.toMatrix ⇑b'.toBasis) *
            (s.toBasis.toMatrix ⇑b'.toBasis *
              b'.toBasis.toMatrix ⇑s.toBasis) := by rw [h2, mul_one]
      _ = star (s.toBasis.toMatrix ⇑b'.toBasis) *
            s.toBasis.toMatrix ⇑b'.toBasis *
              b'.toBasis.toMatrix ⇑s.toBasis := by rw [mul_assoc]
      _ = b'.toBasis.toMatrix ⇑s.toBasis := by rw [h1, one_mul]
  have hA' : LinearMap.toMatrix s.toBasis s.toBasis (Matrix.toEuclideanLin A) = A := by
    rw [hs, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hchange : b'.toBasis.toMatrix ⇑s.toBasis * A *
      s.toBasis.toMatrix ⇑b'.toBasis =
        LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) := by
    conv_lhs => rw [← hA']
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      b'.toBasis s.toBasis b'.toBasis s.toBasis (Matrix.toEuclideanLin A)
  have hreindex : LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) =
      Matrix.reindex e e
        (LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A)) := by
    ext x y
    simp [hb', Matrix.reindex_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
  calc
    star (s.toBasis.toMatrix ⇑b'.toBasis) * A *
        s.toBasis.toMatrix ⇑b'.toBasis =
      b'.toBasis.toMatrix ⇑s.toBasis * A *
        s.toBasis.toMatrix ⇑b'.toBasis := by rw [hstar]
    _ = LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) := hchange
    _ = Matrix.reindex e e
        (LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A)) := hreindex

end OrthonormalBasis

namespace Matrix

variable {a b c : Type*}
variable [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The natural embedding of an operator on the first two factors into the three-factor
space.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`). -/
def leftOverlappingLift (X : Matrix (a × b) (a × b) ℂ) :
    Matrix ((a × b) × c) ((a × b) × c) ℂ :=
  fun p q ↦ X p.1 q.1 * (1 : Matrix c c ℂ) p.2 q.2

/-- The natural embedding of an operator on the last two factors into the three-factor
space.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`). -/
def rightOverlappingLift (Y : Matrix (b × c) (b × c) ℂ) :
    Matrix ((a × b) × c) ((a × b) × c) ℂ :=
  fun p q ↦ (1 : Matrix a a ℂ) p.1.1 q.1.1 * Y (p.1.2, p.2) (q.1.2, q.2)

/-- The middle-factor coefficient matrix of an operator on the first two factors, with
the two first-factor indices fixed. It is the complex specialization of
`operatorBlock`.

Source: Beigi, J. Phys. A 45 (2012) 025306, proof of Lemma 2.1 (`lem:comm`). -/
abbrev leftMiddleSlice (X : Matrix (a × b) (a × b) ℂ) (i i' : a) : Matrix b b ℂ :=
  operatorBlock X i i'

/-- The middle-factor coefficient matrix of an operator on the last two factors, with
the two last-factor indices fixed.

Source: Beigi, J. Phys. A 45 (2012) 025306, proof of Lemma 2.1 (`lem:comm`). -/
def rightMiddleSlice (Y : Matrix (b × c) (b × c) ℂ) (k k' : c) : Matrix b b ℂ :=
  fun j j' ↦ Y (j, k) (j', k')

/-- The index equivalence which orders each middle-space summand as left factor followed by
right factor when adjoining the first outer space. It sends
`(q, ((i, s), r))` to `(i, e (q, (r, s)))`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), decomposition and first block
identity on pages 2--3. -/
def leftSpatialBlockEquiv {K : ℕ} {d m : Fin K → ℕ}
    (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b) :
    ((q : Fin K) × ((a × Fin (d q)) × Fin (m q))) ≃ (a × b) where
  toFun x := (x.2.1.1, e ⟨x.1, (x.2.2, x.2.1.2)⟩)
  invFun y :=
    let z := e.symm y.2
    ⟨z.1, ((y.1, z.2.2), z.2.1)⟩
  left_inv x := by
    obtain ⟨q, ⟨⟨i, s⟩, r⟩⟩ := x
    dsimp
    rw [e.symm_apply_apply]
  right_inv y := by
    obtain ⟨i, j⟩ := y
    dsimp
    rw [e.apply_symm_apply]

/-- The index equivalence which orders each middle-space summand as left factor followed by
right factor when adjoining the last outer space. It sends
`(q, (s, (r, k)))` to `(e (q, (r, s)), k)`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), decomposition and second block
identity on pages 2--3. -/
def rightSpatialBlockEquiv {K : ℕ} {d m : Fin K → ℕ}
    (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b) :
    ((q : Fin K) × (Fin (d q) × (Fin (m q) × c))) ≃ (b × c) where
  toFun x := (e ⟨x.1, (x.2.2.1, x.2.1)⟩, x.2.2.2)
  invFun y :=
    let z := e.symm y.1
    ⟨z.1, (z.2.2, (z.2.1, y.2))⟩
  left_inv x := by
    obtain ⟨q, ⟨s, r, k⟩⟩ := x
    dsimp
    rw [e.symm_apply_apply]
  right_inv y := by
    obtain ⟨j, k⟩ := y
    dsimp
    rw [e.apply_symm_apply]

omit [DecidableEq b] in
private theorem conj_left_tensor_apply (X : Matrix (a × b) (a × b) ℂ)
    (U : Matrix b b ℂ) (i i' : a) (j j' : b) :
    (star ((1 : Matrix a a ℂ) ⊗ₖ U) * X * ((1 : Matrix a a ℂ) ⊗ₖ U))
        (i, j) (i', j') =
      (star U * leftMiddleSlice X i i' * U) j j' := by
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, operatorBlock_apply]
  simp

omit [DecidableEq b] in
private theorem conj_right_tensor_apply (Y : Matrix (b × c) (b × c) ℂ)
    (U : Matrix b b ℂ) (j j' : b) (k k' : c) :
    (star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y * (U ⊗ₖ (1 : Matrix c c ℂ)))
        (j, k) (j', k') =
      (star U * rightMiddleSlice Y k k' * U) j j' := by
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, rightMiddleSlice]
  simp

omit [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c] in
/-- Hermiticity exchanges the two outer indices of a middle-factor coefficient matrix.

Source: Beigi, J. Phys. A 45 (2012) 025306, proof of Lemma 2.1 (`lem:comm`). -/
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
finite-dimensional star-algebra decomposition in S. Beigi, J. Phys. A 45 (2012) 025306,
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
  simpa [leftOverlappingLift, rightOverlappingLift, operatorBlock_apply,
    rightMiddleSlice, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type] using h

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
J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`). The source assumes both `X` and `Y` Hermitian;
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

private theorem toMatrix_eq_leftBlockDiagonal_of_action {K : ℕ} {d m : Fin K → ℕ}
    (e : OrthonormalBasis ((q : Fin K) × (Fin (m q) × Fin (d q))) ℂ
      (EuclideanSpace ℂ b)) (A : Matrix b b ℂ)
    (B : ∀ q, Matrix (Fin (d q)) (Fin (d q)) ℂ)
    (hA : ∀ (q : Fin K) (r : Fin (m q)) (s : Fin (d q)),
      Matrix.toEuclideanLin A (e ⟨q, (r, s)⟩) =
        ∑ s', B q s' s • e ⟨q, (r, s')⟩) :
    LinearMap.toMatrix e.toBasis e.toBasis (Matrix.toEuclideanLin A) =
      Matrix.blockDiagonal' fun q =>
        (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ) ⊗ₖ B q := by
  ext ⟨q', r', s'⟩ ⟨q, r, s⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    hA q r s, inner_sum]
  simp only [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
  rcases eq_or_ne q' q with rfl | hqq
  · rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Sigma.mk.inj_iff,
      heq_eq_eq, Prod.mk.injEq, true_and]
    rcases eq_or_ne r' r with rfl | hrr
    · simp [Finset.sum_ite_eq]
    · simp [hrr]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hqq]
    simp [hqq]

private theorem toMatrix_eq_rightBlockDiagonal_of_action {K : ℕ} {d m : Fin K → ℕ}
    (e : OrthonormalBasis ((q : Fin K) × (Fin (m q) × Fin (d q))) ℂ
      (EuclideanSpace ℂ b)) (A : Matrix b b ℂ)
    (C : ∀ q, Matrix (Fin (m q)) (Fin (m q)) ℂ)
    (hA : ∀ (q : Fin K) (r : Fin (m q)) (s : Fin (d q)),
      Matrix.toEuclideanLin A (e ⟨q, (r, s)⟩) =
        ∑ r', C q r' r • e ⟨q, (r', s)⟩) :
    LinearMap.toMatrix e.toBasis e.toBasis (Matrix.toEuclideanLin A) =
      Matrix.blockDiagonal' fun q =>
        C q ⊗ₖ (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) := by
  ext ⟨q', r', s'⟩ ⟨q, r, s⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    hA q r s, inner_sum]
  simp only [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
  rcases eq_or_ne q' q with rfl | hqq
  · rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Sigma.mk.inj_iff,
      heq_eq_eq, Prod.mk.injEq, true_and]
    rcases eq_or_ne s' s with rfl | hss
    · simp [Finset.sum_ite_eq]
    · simp [hss]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hqq]
    simp [hqq]

/-- **Explicit unitary Bravyi--Vyalyi block actions.** Let $X_{AB}$ and $Y_{BC}$ be
Hermitian operators whose natural three-factor lifts commute. There are positive dimensions
$d_q,m_q$, a unitary $U$ identifying
$$
  H_B \cong \bigoplus_q H_{q,l}\otimes H_{q,r},
$$
and Hermitian operators $R_q$ on $H_A\otimes H_{q,l}$ and $S_q$ on
$H_{q,r}\otimes H_C$ such that
$$
 (\mathbf 1_A\otimes U^*)X_{AB}(\mathbf 1_A\otimes U)
   = \bigoplus_q (R_q\otimes\mathbf 1_{q,r}),
 \qquad
 (U^*\otimes\mathbf 1_C)Y_{BC}(U\otimes\mathbf 1_C)
   = \bigoplus_q (\mathbf 1_{q,l}\otimes S_q).
$$
The two equivalences in the formal statement order the dependent direct-sum indices as
$A\otimes(H_{q,l}\otimes H_{q,r})$ and
$(H_{q,l}\otimes H_{q,r})\otimes C$, respectively.

This is the explicit coordinate form of the two block-action identities in S. Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. Its hypotheses agree with the
source: both overlapping operators are Hermitian and their natural lifts commute. -/
theorem exists_unitary_blockActions_of_overlappingLifts_commute
    (X : Matrix (a × b) (a × b) ℂ) (Y : Matrix (b × c) (b × c) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hComm : leftOverlappingLift X * rightOverlappingLift Y =
      rightOverlappingLift Y * leftOverlappingLift X) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b)
      (U : Matrix b b ℂ)
      (R : ∀ q, Matrix (a × Fin (d q)) (a × Fin (d q)) ℂ)
      (S : ∀ q, Matrix (Fin (m q) × c) (Fin (m q) × c) ℂ),
      U ∈ Matrix.unitaryGroup b ℂ ∧
        (∀ q, 0 < d q) ∧ (∀ q, 0 < m q) ∧
        (∀ q, (R q).IsHermitian) ∧ (∀ q, (S q).IsHermitian) ∧
        Matrix.reindex (leftSpatialBlockEquiv e).symm
            (leftSpatialBlockEquiv e).symm
            (star ((1 : Matrix a a ℂ) ⊗ₖ U) * X *
              ((1 : Matrix a a ℂ) ⊗ₖ U)) =
          (Matrix.blockDiagonal' fun q =>
            R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ)) ∧
        Matrix.reindex (rightSpatialBlockEquiv e).symm
            (rightSpatialBlockEquiv e).symm
            (star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y *
              (U ⊗ₖ (1 : Matrix c c ℂ))) =
          (Matrix.blockDiagonal' fun q =>
            (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q) := by
  classical
  obtain ⟨K, d, m, basis, hd, hm, hleft, hright⟩ :=
    exists_middle_spatial_decomposition_of_overlappingLifts_commute X Y hY hComm
  choose B hB using hleft
  choose C hC using hright
  obtain ⟨e, U, hU, hcoord⟩ := basis.exists_unitary_conj_toMatrix
  let R : ∀ q, Matrix (a × Fin (d q)) (a × Fin (d q)) ℂ :=
    fun q x y => B x.1 y.1 q x.2 y.2
  let S : ∀ q, Matrix (Fin (m q) × c) (Fin (m q) × c) ℂ :=
    fun q x y => C x.2 y.2 q x.1 y.1
  have hXblock : Matrix.reindex (leftSpatialBlockEquiv e).symm
          (leftSpatialBlockEquiv e).symm
          (star ((1 : Matrix a a ℂ) ⊗ₖ U) * X *
            ((1 : Matrix a a ℂ) ⊗ₖ U)) =
        Matrix.blockDiagonal' fun q =>
          R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ) := by
    ext ⟨q, ⟨⟨i, s⟩, r⟩⟩ ⟨q', ⟨⟨i', s'⟩, r'⟩⟩
    change (star ((1 : Matrix a a ℂ) ⊗ₖ U) * X *
        ((1 : Matrix a a ℂ) ⊗ₖ U))
          (i, e ⟨q, (r, s)⟩) (i', e ⟨q', (r', s')⟩) = _
    rw [conj_left_tensor_apply, hcoord,
      toMatrix_eq_leftBlockDiagonal_of_action basis _ (B i i') (hB i i')]
    simp only [Matrix.reindex_apply]
    rcases eq_or_ne q q' with rfl | hqq
    · simp [R, Matrix.blockDiagonal'_apply_eq,
        Matrix.kroneckerMap_apply, Matrix.one_apply]
    · simp [R, Matrix.blockDiagonal'_apply_ne _ _ _ hqq]
  have hYblock : Matrix.reindex (rightSpatialBlockEquiv e).symm
          (rightSpatialBlockEquiv e).symm
          (star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y *
            (U ⊗ₖ (1 : Matrix c c ℂ))) =
        Matrix.blockDiagonal' fun q =>
          (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q := by
    ext ⟨q, ⟨s, r, k⟩⟩ ⟨q', ⟨s', r', k'⟩⟩
    change (star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y *
        (U ⊗ₖ (1 : Matrix c c ℂ)))
          (e ⟨q, (r, s)⟩, k) (e ⟨q', (r', s')⟩, k') = _
    rw [conj_right_tensor_apply, hcoord,
      toMatrix_eq_rightBlockDiagonal_of_action basis _ (C k k') (hC k k')]
    simp only [Matrix.reindex_apply]
    rcases eq_or_ne q q' with rfl | hqq
    · simp [S, Matrix.blockDiagonal'_apply_eq,
        Matrix.kroneckerMap_apply, Matrix.one_apply]
    · simp [S, Matrix.blockDiagonal'_apply_ne _ _ _ hqq]
  refine ⟨K, d, m, e, U, R, S, hU, hd, hm, ?_, ?_, hXblock, hYblock⟩
  · intro q
    apply Matrix.IsHermitian.ext
    rintro ⟨i', s'⟩ ⟨i, s⟩
    let r : Fin (m q) := ⟨0, hm q⟩
    have hConj := Matrix.isHermitian_conjTranspose_mul_mul
      ((1 : Matrix a a ℂ) ⊗ₖ U) hX
    have hConj' : (star ((1 : Matrix a a ℂ) ⊗ₖ U) * X *
        ((1 : Matrix a a ℂ) ⊗ₖ U)).IsHermitian := by
      simpa only [Matrix.star_eq_conjTranspose] using hConj
    have hPulled := hConj'.reindex (leftSpatialBlockEquiv e).symm
    have hEntry := hPulled.apply ⟨q, ((i', s'), r)⟩ ⟨q, ((i, s), r)⟩
    rw [hXblock] at hEntry
    simpa [R,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply,
      Matrix.one_apply] using hEntry
  · intro q
    apply Matrix.IsHermitian.ext
    rintro ⟨r', k'⟩ ⟨r, k⟩
    let s : Fin (d q) := ⟨0, hd q⟩
    have hConj := Matrix.isHermitian_conjTranspose_mul_mul
      (U ⊗ₖ (1 : Matrix c c ℂ)) hY
    have hConj' : (star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y *
        (U ⊗ₖ (1 : Matrix c c ℂ))).IsHermitian := by
      simpa only [Matrix.star_eq_conjTranspose] using hConj
    have hPulled := hConj'.reindex (rightSpatialBlockEquiv e).symm
    have hEntry := hPulled.apply ⟨q, (s, (r', k'))⟩ ⟨q, (s, (r, k))⟩
    rw [hYblock] at hEntry
    simpa [S,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply,
      Matrix.one_apply] using hEntry

/-- **Beigi's block-sum equalities for the original overlapping operators.** Let
$X_{AB}$ and $Y_{BC}$ be Hermitian, and suppose that their natural three-factor lifts
commute. There are positive dimensions $d_q,m_q$, a unitary $U$ on the middle space,
and Hermitian operators $R_q$ on $H_A\otimes H_{q,l}$ and $S_q$ on
$H_{q,r}\otimes H_C$ such that
$$
 X_{AB}=(\mathbf 1_A\otimes U)
   \left(\bigoplus_q R_q\otimes\mathbf 1_{q,r}\right)
   (\mathbf 1_A\otimes U^*),
 \qquad
 Y_{BC}=(U\otimes\mathbf 1_C)
   \left(\bigoplus_q \mathbf 1_{q,l}\otimes S_q\right)
   (U^*\otimes\mathbf 1_C).
$$
The reindexings in the formal statement express the two dependent direct sums in the
original product coordinates. The block operators are Hermitian; no unitarity assertion
is made about them.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`),
especially the two displayed equalities in the lemma. -/
theorem exists_unitary_blockSum_equalities_of_overlappingLifts_commute
    (X : Matrix (a × b) (a × b) ℂ) (Y : Matrix (b × c) (b × c) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hComm : leftOverlappingLift X * rightOverlappingLift Y =
      rightOverlappingLift Y * leftOverlappingLift X) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b)
      (U : Matrix b b ℂ)
      (R : ∀ q, Matrix (a × Fin (d q)) (a × Fin (d q)) ℂ)
      (S : ∀ q, Matrix (Fin (m q) × c) (Fin (m q) × c) ℂ),
      U ∈ Matrix.unitaryGroup b ℂ ∧
        (∀ q, 0 < d q) ∧ (∀ q, 0 < m q) ∧
        (∀ q, (R q).IsHermitian) ∧ (∀ q, (S q).IsHermitian) ∧
        X = ((1 : Matrix a a ℂ) ⊗ₖ U) *
          Matrix.reindex (leftSpatialBlockEquiv e) (leftSpatialBlockEquiv e)
            (Matrix.blockDiagonal' fun q =>
              R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ)) *
          star ((1 : Matrix a a ℂ) ⊗ₖ U) ∧
        Y = (U ⊗ₖ (1 : Matrix c c ℂ)) *
          Matrix.reindex (rightSpatialBlockEquiv e) (rightSpatialBlockEquiv e)
            (Matrix.blockDiagonal' fun q =>
              (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q) *
          star (U ⊗ₖ (1 : Matrix c c ℂ)) := by
  classical
  obtain ⟨K, d, m, e, U, R, S, hU, hd, hm, hR, hS, hXblock, hYblock⟩ :=
    exists_unitary_blockActions_of_overlappingLifts_commute X Y hX hY hComm
  have hXcoord : star ((1 : Matrix a a ℂ) ⊗ₖ U) * X *
        ((1 : Matrix a a ℂ) ⊗ₖ U) =
      Matrix.reindex (leftSpatialBlockEquiv e) (leftSpatialBlockEquiv e)
        (Matrix.blockDiagonal' fun q =>
          R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ)) := by
    have h := congrArg
      (Matrix.reindex (leftSpatialBlockEquiv e) (leftSpatialBlockEquiv e)) hXblock
    simpa using h
  have hYcoord : star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y *
        (U ⊗ₖ (1 : Matrix c c ℂ)) =
      Matrix.reindex (rightSpatialBlockEquiv e) (rightSpatialBlockEquiv e)
        (Matrix.blockDiagonal' fun q =>
          (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q) := by
    have h := congrArg
      (Matrix.reindex (rightSpatialBlockEquiv e) (rightSpatialBlockEquiv e)) hYblock
    simpa using h
  have hUleft : ((1 : Matrix a a ℂ) ⊗ₖ U) ∈ Matrix.unitaryGroup (a × b) ℂ :=
    Matrix.kronecker_mem_unitary (one_mem _) hU
  have hUright : (U ⊗ₖ (1 : Matrix c c ℂ)) ∈ Matrix.unitaryGroup (b × c) ℂ :=
    Matrix.kronecker_mem_unitary hU (one_mem _)
  have hUleft_mul : ((1 : Matrix a a ℂ) ⊗ₖ U) *
      star ((1 : Matrix a a ℂ) ⊗ₖ U) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hUleft
  have hUright_mul : (U ⊗ₖ (1 : Matrix c c ℂ)) *
      star (U ⊗ₖ (1 : Matrix c c ℂ)) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hUright
  have hXeq : X = ((1 : Matrix a a ℂ) ⊗ₖ U) *
        Matrix.reindex (leftSpatialBlockEquiv e) (leftSpatialBlockEquiv e)
          (Matrix.blockDiagonal' fun q =>
            R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ)) *
        star ((1 : Matrix a a ℂ) ⊗ₖ U) := by
    rw [← hXcoord,
      ← mul_assoc ((1 : Matrix a a ℂ) ⊗ₖ U)
        (star ((1 : Matrix a a ℂ) ⊗ₖ U) * X)
        ((1 : Matrix a a ℂ) ⊗ₖ U),
      ← mul_assoc ((1 : Matrix a a ℂ) ⊗ₖ U)
        (star ((1 : Matrix a a ℂ) ⊗ₖ U)) X,
      hUleft_mul, one_mul, mul_assoc, hUleft_mul, mul_one]
  have hYeq : Y = (U ⊗ₖ (1 : Matrix c c ℂ)) *
        Matrix.reindex (rightSpatialBlockEquiv e) (rightSpatialBlockEquiv e)
          (Matrix.blockDiagonal' fun q =>
            (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q) *
        star (U ⊗ₖ (1 : Matrix c c ℂ)) := by
    rw [← hYcoord,
      ← mul_assoc (U ⊗ₖ (1 : Matrix c c ℂ))
        (star (U ⊗ₖ (1 : Matrix c c ℂ)) * Y)
        (U ⊗ₖ (1 : Matrix c c ℂ)),
      ← mul_assoc (U ⊗ₖ (1 : Matrix c c ℂ))
        (star (U ⊗ₖ (1 : Matrix c c ℂ))) Y,
      hUright_mul, one_mul, mul_assoc, hUright_mul, mul_one]
  exact ⟨K, d, m, e, U, R, S, hU, hd, hm, hR, hS, hXeq, hYeq⟩

end Matrix
