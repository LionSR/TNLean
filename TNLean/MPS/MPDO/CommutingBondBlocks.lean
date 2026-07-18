/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.MPDO.CommutingFormSpatialBridge

/-!
# Neighboring positive blocks of a commuting MPDO bond

A positive two-site bond whose adjacent translates commute admits a common on-site
direct-sum decomposition.  In the resulting coordinates, the bond is a direct sum over
neighboring sector labels, acts identically on the two outer factors, and is determined by
a positive operator on the two inner factors.

## Main definitions

* `MPOTensor.EtaLocalStructureData.CommutingBondBlockData` records the on-site unitary,
  sector dimensions, and neighboring positive operators.

## Main result

* `MPOTensor.EtaLocalStructureData.exists_commutingBondBlockData` constructs these data
  from an eta-local structure.

## References

* arXiv:1606.00608, Appendix C.2, equations `sigmaNK2` and `local`, lines 1581--1593
* S. Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`), pages 2--3
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The direct sum of the right and left on-site factors, in the coordinate order used
by the commuting-overlap decomposition.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1589;
Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`), pages 2--3. -/
abbrev CommutingBondSiteIndex (K : ℕ) (leftDim rightDim : Fin K → ℕ) :=
  (q : Fin K) × (Fin (rightDim q) × Fin (leftDim q))

/-- The tensor product of the right factor in sector `q` and the left factor in the
neighboring sector `h`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1589. -/
abbrev CommutingBondNeighborIndex (leftDim rightDim : Fin K → ℕ)
    (q h : Fin K) :=
  Fin (rightDim q) × Fin (leftDim h)

/-- Regroup two decomposed sites into their sector labels, two outer factors, and the
neighboring right-left factor.

Source: arXiv:1606.00608, Appendix C.2, equations `sigmaNK2` and `local`, lines
1581--1593. -/
def commutingBondTwoSiteRegroupEquiv (K : ℕ) (leftDim rightDim : Fin K → ℕ) :
    (CommutingBondSiteIndex K leftDim rightDim ×
      CommutingBondSiteIndex K leftDim rightDim) ≃
      Σ qh : Fin K × Fin K,
        Fin (leftDim qh.1) ×
          (CommutingBondNeighborIndex leftDim rightDim qh.1 qh.2 ×
            Fin (rightDim qh.2)) where
  toFun x :=
    ⟨(x.1.1, x.2.1),
      (x.1.2.2, ((x.1.2.1, x.2.2.2), x.2.2.1))⟩
  invFun x :=
    (⟨x.1.1, (x.2.2.1.1, x.2.1)⟩,
      ⟨x.1.2, (x.2.2.2, x.2.2.1.2)⟩)
  left_inv x := by
    obtain ⟨⟨q, r, s⟩, ⟨h, t, u⟩⟩ := x
    rfl
  right_inv x := by
    obtain ⟨⟨q, h⟩, s, ⟨r, u⟩, t⟩ := x
    rfl

/-- The two-site regrouping after the on-site sector coordinates have been identified with
the physical space.

Source: arXiv:1606.00608, Appendix C.2, equations `sigmaNK2` and `local`, lines
1581--1593. -/
def commutingBondPhysicalPairRegroupEquiv {K : ℕ}
    {leftDim rightDim : Fin K → ℕ}
    (e : CommutingBondSiteIndex K leftDim rightDim ≃ Fin d) :
    (Fin d × Fin d) ≃
      Σ qh : Fin K × Fin K,
        Fin (leftDim qh.1) ×
          (CommutingBondNeighborIndex leftDim rightDim qh.1 qh.2 ×
            Fin (rightDim qh.2)) :=
  (Equiv.prodCongr e e).symm.trans
    (commutingBondTwoSiteRegroupEquiv K leftDim rightDim)

/-- A positive two-site bond in neighboring-sector form.  On the summand labelled by
`(q, h)`, the transformed bond is
`1 ⊗ eta q h ⊗ 1`, where `eta q h` acts on the right factor of `q` and the left
factor of `h`.

Source: arXiv:1606.00608, Appendix C.2, equations `sigmaNK2` and `local`, lines
1581--1593; Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`), pages 2--3. -/
structure EtaLocalStructureData.CommutingBondBlockData
    {M : MPOTensor d D} (data : EtaLocalStructureData M) where
  /-- The number of on-site sectors.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  sectorCount : ℕ
  /-- The dimensions of the left on-site factors.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  leftDim : Fin sectorCount → ℕ
  /-- The dimensions of the right on-site factors.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  rightDim : Fin sectorCount → ℕ
  /-- The identification of the direct sum of sector factors with the physical space.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  siteEquiv : CommutingBondSiteIndex sectorCount leftDim rightDim ≃ Fin d
  /-- The on-site unitary which gives the sector decomposition.

  Source: arXiv:1606.00608, lines 1599--1605; Beigi, arXiv:1105.1019v2,
  Lemma 2.1 (`lem:comm`), pages 2--3. -/
  unitary : Matrix (Fin d) (Fin d) ℂ
  /-- The on-site change of coordinates is unitary.

  Source: Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`), pages 2--3. -/
  unitary_mem : unitary ∈ Matrix.unitaryGroup (Fin d) ℂ
  /-- Every left factor is nonzero.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  leftDim_pos : ∀ q, 0 < leftDim q
  /-- Every right factor is nonzero.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  rightDim_pos : ∀ q, 0 < rightDim q
  /-- The operator on the two neighboring inner factors.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  eta : ∀ q h, Matrix
    (CommutingBondNeighborIndex leftDim rightDim q h)
    (CommutingBondNeighborIndex leftDim rightDim q h) ℂ
  /-- Each neighboring operator is positive semidefinite.

  Source: arXiv:1606.00608, equation `sigmaNK2`, lines 1581--1589. -/
  eta_pos : ∀ q h, (eta q h).PosSemidef
  /-- In the sector coordinates, the bond is the direct sum of the neighboring operator
  tensored with the identity on both outer factors.

  Source: arXiv:1606.00608, equations `sigmaNK2` and `local`, lines 1581--1593. -/
  pairBond_block :
    Matrix.reindex
      (commutingBondPhysicalPairRegroupEquiv siteEquiv)
      (commutingBondPhysicalPairRegroupEquiv siteEquiv)
      (star (unitary ⊗ₖ unitary) * data.pairBond *
        (unitary ⊗ₖ unitary)) =
      Matrix.blockDiagonal' fun (qh : Fin sectorCount × Fin sectorCount) =>
        (1 : Matrix (Fin (leftDim qh.1)) (Fin (leftDim qh.1)) ℂ) ⊗ₖ
          (eta qh.1 qh.2 ⊗ₖ
            (1 : Matrix (Fin (rightDim qh.2))
              (Fin (rightDim qh.2)) ℂ))

private theorem double_conj_eq_conj_first
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix a a ℂ) (B : Matrix (a × a) (a × a) ℂ) :
    star (U ⊗ₖ U) * B * (U ⊗ₖ U) =
      star (U ⊗ₖ (1 : Matrix a a ℂ)) *
        (star ((1 : Matrix a a ℂ) ⊗ₖ U) * B *
          ((1 : Matrix a a ℂ) ⊗ₖ U)) *
        (U ⊗ₖ (1 : Matrix a a ℂ)) := by
  rw [show U ⊗ₖ U =
      ((1 : Matrix a a ℂ) ⊗ₖ U) *
        (U ⊗ₖ (1 : Matrix a a ℂ)) by
    rw [← Matrix.mul_kronecker_mul]
    simp]
  simp only [star_mul]
  simp only [Matrix.mul_assoc]

private theorem double_conj_eq_conj_second
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix a a ℂ) (B : Matrix (a × a) (a × a) ℂ) :
    star (U ⊗ₖ U) * B * (U ⊗ₖ U) =
      star ((1 : Matrix a a ℂ) ⊗ₖ U) *
        (star (U ⊗ₖ (1 : Matrix a a ℂ)) * B *
          (U ⊗ₖ (1 : Matrix a a ℂ))) *
        ((1 : Matrix a a ℂ) ⊗ₖ U) := by
  rw [show U ⊗ₖ U =
      (U ⊗ₖ (1 : Matrix a a ℂ)) *
        ((1 : Matrix a a ℂ) ⊗ₖ U) by
    rw [← Matrix.mul_kronecker_mul]
    simp]
  simp only [star_mul]
  simp only [Matrix.mul_assoc]

private theorem conjugate_first_apply
    {a c : Type*} [Fintype a]
    [Fintype c] [DecidableEq c]
    (U : Matrix a a ℂ) (B : Matrix (a × c) (a × c) ℂ)
    (i i' : a) (j j' : c) :
    (star (U ⊗ₖ (1 : Matrix c c ℂ)) * B *
        (U ⊗ₖ (1 : Matrix c c ℂ))) (i, j) (i', j') =
      (star U * Matrix.submatrix B (fun x ↦ (x, j)) (fun y ↦ (y, j')) * U) i i' := by
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.submatrix, Fintype.sum_prod_type]
  simp

private theorem conjugate_second_apply
    {a c : Type*} [Fintype a] [DecidableEq a]
    [Fintype c]
    (U : Matrix c c ℂ) (B : Matrix (a × c) (a × c) ℂ)
    (i i' : a) (j j' : c) :
    (star ((1 : Matrix a a ℂ) ⊗ₖ U) * B *
        ((1 : Matrix a a ℂ) ⊗ₖ U)) (i, j) (i', j') =
      (star U * Matrix.submatrix B (fun x ↦ (i, x)) (fun y ↦ (i', y)) * U) j j' := by
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.submatrix, Fintype.sum_prod_type]
  simp

private theorem doubleBlock_entry_same_second
    {b : Type*} [Fintype b] [DecidableEq b]
    {K : ℕ} {leftDim rightDim : Fin K → ℕ}
    (e : CommutingBondSiteIndex K leftDim rightDim ≃ b)
    (U : Matrix b b ℂ) (B : Matrix (b × b) (b × b) ℂ)
    (R : ∀ h, Matrix (b × Fin (leftDim h)) (b × Fin (leftDim h)) ℂ)
    (hleft :
      Matrix.reindex (Matrix.leftSpatialBlockEquiv e).symm
          (Matrix.leftSpatialBlockEquiv e).symm
          (star ((1 : Matrix b b ℂ) ⊗ₖ U) * B *
            ((1 : Matrix b b ℂ) ⊗ₖ U)) =
        Matrix.blockDiagonal' fun h =>
          R h ⊗ₖ (1 : Matrix (Fin (rightDim h)) (Fin (rightDim h)) ℂ))
    (x y : CommutingBondSiteIndex K leftDim rightDim)
    (h : Fin K) (t t' : Fin (rightDim h)) (u u' : Fin (leftDim h)) :
    Matrix.reindex (Equiv.prodCongr e e).symm (Equiv.prodCongr e e).symm
        (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
        (x, ⟨h, (t, u)⟩) (y, ⟨h, (t', u')⟩) =
      Matrix.reindex (Equiv.prodCongr e (Equiv.refl _)).symm
          (Equiv.prodCongr e (Equiv.refl _)).symm
          (star (U ⊗ₖ (1 : Matrix (Fin (leftDim h))
              (Fin (leftDim h)) ℂ)) * R h *
            (U ⊗ₖ (1 : Matrix (Fin (leftDim h))
              (Fin (leftDim h)) ℂ)))
          (x, u) (y, u') *
        (1 : Matrix (Fin (rightDim h)) (Fin (rightDim h)) ℂ) t t' := by
  change (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
      (e x, e ⟨h, (t, u)⟩) (e y, e ⟨h, (t', u')⟩) =
    (star (U ⊗ₖ (1 : Matrix (Fin (leftDim h))
        (Fin (leftDim h)) ℂ)) * R h *
      (U ⊗ₖ (1 : Matrix (Fin (leftDim h))
        (Fin (leftDim h)) ℂ)))
      (e x, u) (e y, u') *
        (1 : Matrix (Fin (rightDim h)) (Fin (rightDim h)) ℂ) t t'
  rw [double_conj_eq_conj_first]
  rw [conjugate_first_apply]
  rw [conjugate_first_apply]
  have hentry (a a' : b) :
      (star ((1 : Matrix b b ℂ) ⊗ₖ U) * B *
          ((1 : Matrix b b ℂ) ⊗ₖ U))
          (a, e ⟨h, (t, u)⟩) (a', e ⟨h, (t', u')⟩) =
        R h (a, u) (a', u') *
          (1 : Matrix (Fin (rightDim h)) (Fin (rightDim h)) ℂ) t t' := by
    have hx := congrFun (congrFun hleft
      ⟨h, ((a, u), t)⟩) ⟨h, ((a', u'), t')⟩
    simpa [Matrix.reindex_apply, Matrix.leftSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] using hx
  have hslice :
      Matrix.submatrix
          (star ((1 : Matrix b b ℂ) ⊗ₖ U) * B *
            ((1 : Matrix b b ℂ) ⊗ₖ U))
          (fun a ↦ (a, e ⟨h, (t, u)⟩))
          (fun a ↦ (a, e ⟨h, (t', u')⟩)) =
        ((1 : Matrix (Fin (rightDim h)) (Fin (rightDim h)) ℂ) t t') •
          Matrix.submatrix (R h) (fun a ↦ (a, u)) (fun a ↦ (a, u')) := by
    ext a a'
    simpa [Matrix.submatrix_apply, mul_comm] using hentry a a'
  rw [hslice]
  simp [mul_comm]

private theorem doubleBlock_entry_off_second
    {b : Type*} [Fintype b] [DecidableEq b]
    {K : ℕ} {leftDim rightDim : Fin K → ℕ}
    (e : CommutingBondSiteIndex K leftDim rightDim ≃ b)
    (U : Matrix b b ℂ) (B : Matrix (b × b) (b × b) ℂ)
    (R : ∀ h, Matrix (b × Fin (leftDim h)) (b × Fin (leftDim h)) ℂ)
    (hleft :
      Matrix.reindex (Matrix.leftSpatialBlockEquiv e).symm
          (Matrix.leftSpatialBlockEquiv e).symm
          (star ((1 : Matrix b b ℂ) ⊗ₖ U) * B *
            ((1 : Matrix b b ℂ) ⊗ₖ U)) =
        Matrix.blockDiagonal' fun h =>
          R h ⊗ₖ (1 : Matrix (Fin (rightDim h)) (Fin (rightDim h)) ℂ))
    (x y : CommutingBondSiteIndex K leftDim rightDim)
    (h h' : Fin K) (t : Fin (rightDim h)) (u : Fin (leftDim h))
    (t' : Fin (rightDim h')) (u' : Fin (leftDim h')) (hhh : h ≠ h') :
    Matrix.reindex (Equiv.prodCongr e e).symm (Equiv.prodCongr e e).symm
        (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
        (x, ⟨h, (t, u)⟩) (y, ⟨h', (t', u')⟩) = 0 := by
  change (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
      (e x, e ⟨h, (t, u)⟩) (e y, e ⟨h', (t', u')⟩) = 0
  rw [double_conj_eq_conj_first]
  rw [conjugate_first_apply]
  have hentry (a a' : b) :
      (star ((1 : Matrix b b ℂ) ⊗ₖ U) * B *
          ((1 : Matrix b b ℂ) ⊗ₖ U))
          (a, e ⟨h, (t, u)⟩) (a', e ⟨h', (t', u')⟩) = 0 := by
    have hx := congrFun (congrFun hleft
      ⟨h, ((a, u), t)⟩) ⟨h', ((a', u'), t')⟩
    simpa [Matrix.reindex_apply, Matrix.leftSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_ne _ _ _ hhh] using hx
  have hslice :
      Matrix.submatrix
          (star ((1 : Matrix b b ℂ) ⊗ₖ U) * B *
            ((1 : Matrix b b ℂ) ⊗ₖ U))
          (fun a ↦ (a, e ⟨h, (t, u)⟩))
          (fun a ↦ (a, e ⟨h', (t', u')⟩)) = 0 := by
    ext a a'
    simpa using hentry a a'
  rw [hslice]
  simp

private theorem doubleBlock_entry_same_first
    {b : Type*} [Fintype b] [DecidableEq b]
    {K : ℕ} {leftDim rightDim : Fin K → ℕ}
    (e : CommutingBondSiteIndex K leftDim rightDim ≃ b)
    (U : Matrix b b ℂ) (B : Matrix (b × b) (b × b) ℂ)
    (S : ∀ q, Matrix (Fin (rightDim q) × b) (Fin (rightDim q) × b) ℂ)
    (hright :
      Matrix.reindex (Matrix.rightSpatialBlockEquiv e).symm
          (Matrix.rightSpatialBlockEquiv e).symm
          (star (U ⊗ₖ (1 : Matrix b b ℂ)) * B *
            (U ⊗ₖ (1 : Matrix b b ℂ))) =
        Matrix.blockDiagonal' fun q ↦
          (1 : Matrix (Fin (leftDim q)) (Fin (leftDim q)) ℂ) ⊗ₖ S q)
    (q : Fin K) (r r' : Fin (rightDim q))
    (s s' : Fin (leftDim q))
    (x y : CommutingBondSiteIndex K leftDim rightDim) :
    Matrix.reindex (Equiv.prodCongr e e).symm (Equiv.prodCongr e e).symm
        (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
        (⟨q, (r, s)⟩, x) (⟨q, (r', s')⟩, y) =
      (1 : Matrix (Fin (leftDim q)) (Fin (leftDim q)) ℂ) s s' *
        Matrix.reindex (Equiv.prodCongr (Equiv.refl _) e).symm
          (Equiv.prodCongr (Equiv.refl _) e).symm
          (star ((1 : Matrix (Fin (rightDim q))
              (Fin (rightDim q)) ℂ) ⊗ₖ U) * S q *
            ((1 : Matrix (Fin (rightDim q))
              (Fin (rightDim q)) ℂ) ⊗ₖ U))
          (r, x) (r', y) := by
  change (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
      (e ⟨q, (r, s)⟩, e x) (e ⟨q, (r', s')⟩, e y) = _
  rw [double_conj_eq_conj_second]
  rw [conjugate_second_apply]
  change _ =
    (1 : Matrix (Fin (leftDim q)) (Fin (leftDim q)) ℂ) s s' *
      (star ((1 : Matrix (Fin (rightDim q)) (Fin (rightDim q)) ℂ) ⊗ₖ U) *
        S q * ((1 : Matrix (Fin (rightDim q)) (Fin (rightDim q)) ℂ) ⊗ₖ U))
        (r, e x) (r', e y)
  rw [conjugate_second_apply]
  have hentry (a a' : b) :
      (star (U ⊗ₖ (1 : Matrix b b ℂ)) * B *
          (U ⊗ₖ (1 : Matrix b b ℂ)))
          (e ⟨q, (r, s)⟩, a) (e ⟨q, (r', s')⟩, a') =
        (1 : Matrix (Fin (leftDim q)) (Fin (leftDim q)) ℂ) s s' *
          S q (r, a) (r', a') := by
    have hx := congrFun (congrFun hright
      ⟨q, (s, (r, a))⟩) ⟨q, (s', (r', a'))⟩
    simpa [Matrix.reindex_apply, Matrix.rightSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] using hx
  have hslice :
      Matrix.submatrix
          (star (U ⊗ₖ (1 : Matrix b b ℂ)) * B *
            (U ⊗ₖ (1 : Matrix b b ℂ)))
          (fun a ↦ (e ⟨q, (r, s)⟩, a))
          (fun a ↦ (e ⟨q, (r', s')⟩, a)) =
        ((1 : Matrix (Fin (leftDim q)) (Fin (leftDim q)) ℂ) s s') •
          Matrix.submatrix (S q) (fun a ↦ (r, a)) (fun a ↦ (r', a)) := by
    ext a a'
    simpa [Matrix.submatrix_apply] using hentry a a'
  rw [hslice]
  simp

private theorem doubleBlock_entry_off_first
    {b : Type*} [Fintype b] [DecidableEq b]
    {K : ℕ} {leftDim rightDim : Fin K → ℕ}
    (e : CommutingBondSiteIndex K leftDim rightDim ≃ b)
    (U : Matrix b b ℂ) (B : Matrix (b × b) (b × b) ℂ)
    (S : ∀ q, Matrix (Fin (rightDim q) × b) (Fin (rightDim q) × b) ℂ)
    (hright :
      Matrix.reindex (Matrix.rightSpatialBlockEquiv e).symm
          (Matrix.rightSpatialBlockEquiv e).symm
          (star (U ⊗ₖ (1 : Matrix b b ℂ)) * B *
            (U ⊗ₖ (1 : Matrix b b ℂ))) =
        Matrix.blockDiagonal' fun q ↦
          (1 : Matrix (Fin (leftDim q)) (Fin (leftDim q)) ℂ) ⊗ₖ S q)
    (q q' : Fin K) (r : Fin (rightDim q)) (s : Fin (leftDim q))
    (r' : Fin (rightDim q')) (s' : Fin (leftDim q'))
    (x y : CommutingBondSiteIndex K leftDim rightDim) (hqq : q ≠ q') :
    Matrix.reindex (Equiv.prodCongr e e).symm (Equiv.prodCongr e e).symm
        (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
        (⟨q, (r, s)⟩, x) (⟨q', (r', s')⟩, y) = 0 := by
  change (star (U ⊗ₖ U) * B * (U ⊗ₖ U))
      (e ⟨q, (r, s)⟩, e x) (e ⟨q', (r', s')⟩, e y) = 0
  rw [double_conj_eq_conj_second]
  rw [conjugate_second_apply]
  have hentry (a a' : b) :
      (star (U ⊗ₖ (1 : Matrix b b ℂ)) * B *
          (U ⊗ₖ (1 : Matrix b b ℂ)))
          (e ⟨q, (r, s)⟩, a) (e ⟨q', (r', s')⟩, a') = 0 := by
    have hx := congrFun (congrFun hright
      ⟨q, (s, (r, a))⟩) ⟨q', (s', (r', a'))⟩
    simpa [Matrix.reindex_apply, Matrix.rightSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_ne _ _ _ hqq] using hx
  have hslice :
      Matrix.submatrix
          (star (U ⊗ₖ (1 : Matrix b b ℂ)) * B *
            (U ⊗ₖ (1 : Matrix b b ℂ)))
          (fun a ↦ (e ⟨q, (r, s)⟩, a))
          (fun a ↦ (e ⟨q', (r', s')⟩, a)) = 0 := by
    ext a a'
    simpa using hentry a a'
  rw [hslice]
  simp

/-- The positive bond of an eta-local structure has the neighboring-sector form

`B = ⊕_(q,h) 1_(L,q) ⊗ eta_(q,h) ⊗ 1_(R,h)`

after a common on-site unitary change of coordinates.  The neighboring operators are
positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, equations `sigmaNK2` and `local`, lines
1581--1593, and the application of the commuting-overlap decomposition at lines
1599--1605; Beigi, arXiv:1105.1019v2, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem EtaLocalStructureData.exists_commutingBondBlockData
    {M : MPOTensor d D} (data : EtaLocalStructureData M) :
    Nonempty data.CommutingBondBlockData := by
  classical
  obtain ⟨K, leftDim, rightDim, e, U, R, S, hU, hleftDim,
      hrightDim, hR, hS, hleft, hright⟩ :=
    data.exists_unitary_blockActions_of_pairBond
  let left0 : ∀ q, Fin (leftDim q) := fun q => ⟨0, hleftDim q⟩
  let right0 : ∀ q, Fin (rightDim q) := fun q => ⟨0, hrightDim q⟩
  let pairEquiv := commutingBondPhysicalPairRegroupEquiv e
  let transformedBond := Matrix.reindex pairEquiv pairEquiv
    (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U))
  let eta : ∀ q h,
      Matrix (CommutingBondNeighborIndex leftDim rightDim q h)
        (CommutingBondNeighborIndex leftDim rightDim q h) ℂ :=
    fun q h x y => transformedBond
      ⟨(q, h), (left0 q, (x, right0 h))⟩
      ⟨(q, h), (left0 q, (y, right0 h))⟩
  refine ⟨⟨K, leftDim, rightDim, e, U, hU, hleftDim, hrightDim,
    eta, ?_, ?_⟩⟩
  · intro q h
    have hpair : data.pairBond.PosSemidef := by
      simpa [EtaLocalStructureData.pairBond, pairBondMatrix,
        Matrix.reindex_apply] using
        data.bondData.bond_pos.submatrix (finTwoArrowEquiv (Fin d)).symm
    have hdouble :
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)).PosSemidef := by
      simpa only [Matrix.star_eq_conjTranspose] using
        hpair.conjTranspose_mul_mul_same (U ⊗ₖ U)
    have htransformed : transformedBond.PosSemidef := by
      simpa [transformedBond, Matrix.reindex_apply] using
        hdouble.submatrix pairEquiv.symm
    let f : CommutingBondNeighborIndex leftDim rightDim q h →
        (Σ qh : Fin K × Fin K,
          Fin (leftDim qh.1) ×
            (CommutingBondNeighborIndex leftDim rightDim qh.1 qh.2 ×
              Fin (rightDim qh.2))) := fun x ↦
      ⟨(q, h), (left0 q, (x, right0 h))⟩
    have heta : eta q h = Matrix.submatrix transformedBond f f := by
      rfl
    rw [heta]
    exact htransformed.submatrix f
  · ext i j
    obtain ⟨⟨q, h⟩, s, ⟨⟨r, u⟩, t⟩⟩ := i
    obtain ⟨⟨q', h'⟩, s', ⟨⟨r', u'⟩, t'⟩⟩ := j
    change transformedBond
        ⟨(q, h), (s, ((r, u), t))⟩
        ⟨(q', h'), (s', ((r', u'), t'))⟩ = _
    rcases eq_or_ne q q' with rfl | hqq
    · rcases eq_or_ne h h' with rfl | hhh
      · rcases eq_or_ne s s' with rfl | hss
        · rcases eq_or_ne t t' with rfl | htt
          · simp only [Matrix.blockDiagonal'_apply_eq,
              Matrix.kroneckerMap_apply, Matrix.one_apply, if_pos,
              one_mul, mul_one]
            have hs := doubleBlock_entry_same_first e U data.pairBond S hright
              q r r' s s ⟨h, (t, u)⟩ ⟨h, (t, u')⟩
            have hs0 := doubleBlock_entry_same_first e U data.pairBond S hright
              q r r' (left0 q) (left0 q) ⟨h, (t, u)⟩ ⟨h, (t, u')⟩
            have ht := doubleBlock_entry_same_second e U data.pairBond R hleft
              ⟨q, (r, left0 q)⟩ ⟨q, (r', left0 q)⟩ h t t u u'
            have ht0 := doubleBlock_entry_same_second e U data.pairBond R hleft
              ⟨q, (r, left0 q)⟩ ⟨q, (r', left0 q)⟩ h
              (right0 h) (right0 h) u u'
            simp only [Matrix.one_apply, if_pos, one_mul, mul_one] at hs hs0 ht ht0
            exact hs.trans (hs0.symm.trans (ht.trans ht0.symm))
          · have hz := doubleBlock_entry_same_second e U data.pairBond R hleft
                ⟨q, (r, s)⟩ ⟨q, (r', s)⟩ h t t' u u'
            simp only [Matrix.one_apply, if_neg htt, mul_zero] at hz
            change Matrix.reindex (Equiv.prodCongr e e).symm
                (Equiv.prodCongr e e).symm
                (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U))
                (⟨q, (r, s)⟩, ⟨h, (t, u)⟩)
                (⟨q, (r', s)⟩, ⟨h, (t', u')⟩) = _
            simpa [Matrix.blockDiagonal'_apply_eq,
              Matrix.kroneckerMap_apply, Matrix.one_apply, htt] using hz
        · have hz := doubleBlock_entry_same_first e U data.pairBond S hright
              q r r' s s' ⟨h, (t, u)⟩ ⟨h, (t', u')⟩
          simp only [Matrix.one_apply, if_neg hss, zero_mul] at hz
          change Matrix.reindex (Equiv.prodCongr e e).symm
              (Equiv.prodCongr e e).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U))
              (⟨q, (r, s)⟩, ⟨h, (t, u)⟩)
              (⟨q, (r', s')⟩, ⟨h, (t', u')⟩) = _
          simpa [Matrix.blockDiagonal'_apply_eq,
            Matrix.kroneckerMap_apply, Matrix.one_apply, hss] using hz
      · have hz := doubleBlock_entry_off_second e U data.pairBond R hleft
            ⟨q, (r, s)⟩ ⟨q, (r', s')⟩ h h' t u t' u' hhh
        have hpair : (q, h) ≠ (q, h') := by
          intro heq
          exact hhh (congrArg (fun z : Fin K × Fin K ↦ z.2) heq)
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpair]
        change Matrix.reindex (Equiv.prodCongr e e).symm
            (Equiv.prodCongr e e).symm
            (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U))
            (⟨q, (r, s)⟩, ⟨h, (t, u)⟩)
            (⟨q, (r', s')⟩, ⟨h', (t', u')⟩) = 0
        exact hz
    · have hz := doubleBlock_entry_off_first e U data.pairBond S hright
          q q' r s r' s' ⟨h, (t, u)⟩ ⟨h', (t', u')⟩ hqq
      have hpair : (q, h) ≠ (q', h') := by
        intro heq
        exact hqq (congrArg (fun z : Fin K × Fin K ↦ z.1) heq)
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpair]
      change Matrix.reindex (Equiv.prodCongr e e).symm
          (Equiv.prodCongr e e).symm
          (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U))
          (⟨q, (r, s)⟩, ⟨h, (t, u)⟩)
          (⟨q', (r', s')⟩, ⟨h', (t', u')⟩) = 0
      exact hz

end MPOTensor
