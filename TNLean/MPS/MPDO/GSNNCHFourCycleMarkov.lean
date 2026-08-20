/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingOverlappingDecomp
import TNLean.Algebra.PositiveSemidefiniteNormalization
import TNLean.Entropy.MarkovChain
import TNLean.MPS.MPDO.CommutingOverlappingCoordinates
import TNLean.MPS.MPDO.CPSVExample412FourCycleEntropy
import TNLean.MPS.MPDO.GSNNCHSectorSum
import TNLean.MPS.MPDO.PhysicalSectorBondTransport
import TNLean.MPS.MPDO.PhysicalSupportBondTransport

/-!
# Four-cycle quantum Markov structure of a commuting Gibbs state

This file proves that a four-site Gibbs state of a nearest-neighbor commuting
Hamiltonian is a quantum Markov state after grouping the sites as
\(A=\{0\}\), \(B=\{1,3\}\), and \(C=\{2\}\).  The proof first separates the
four bonds into two positive overlapping factors and then applies the
Bravyi--Vyalyi spatial decomposition on the middle system.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.8,
  lines 829--850.
* S. Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1.
* Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246 (2004), 359--374.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

variable {a b c : Type*}
variable [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The direct-sum coordinates on three factors furnished by the spatial
decomposition of two commuting overlapping operators.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
private def overlappingSpatialBlockEquiv {K : ℕ} {d m : Fin K → ℕ}
    (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b) :
    (Σ q : Fin K, (a × Fin (d q)) × (Fin (m q) × c)) ≃ ((a × b) × c) where
  toFun x := ((x.2.1.1, e ⟨x.1, (x.2.2.1, x.2.1.2)⟩), x.2.2.2)
  invFun y :=
    let z := e.symm y.1.2
    ⟨z.1, ((y.1.1, z.2.2), (z.2.1, y.2))⟩
  left_inv x := by
    obtain ⟨q, ⟨⟨i, s⟩, ⟨r, k⟩⟩⟩ := x
    dsimp
    rw [e.symm_apply_apply]
  right_inv y := by
    obtain ⟨⟨i, j⟩, k⟩ := y
    dsimp
    rw [e.apply_symm_apply]

/-- The middle-space decomposition with the left factor written before the
right factor in every summand. -/
private def overlappingMiddleBlockEquiv {K : ℕ} {d m : Fin K → ℕ}
    (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b) :
    b ≃ Σ q : Fin K, Fin (d q) × Fin (m q) :=
  e.symm.trans (Equiv.sigmaCongrRight fun _ ↦ Equiv.prodComm _ _)

/-- Transporting a matrix from physical coordinates to raw spatial blocks and
then reassociating gives the same matrix as the HJPW middle decomposition. -/
private theorem reindex_abcEquiv_eq_reindex_sigmaAssoc_of_reindex_tripartite
    {dA dB dC K : ℕ} {d m : Fin K → ℕ}
    (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ Fin dB)
    (M : Matrix (Fin dA × (Fin dB × Fin dC))
      (Fin dA × (Fin dB × Fin dC)) ℂ)
    (B : Matrix (Σ q : Fin K,
        (Fin dA × Fin (d q)) × (Fin (m q) × Fin dC))
      (Σ q : Fin K,
        (Fin dA × Fin (d q)) × (Fin (m q) × Fin dC)) ℂ)
    (hM : Matrix.reindex
        (MarkovDilation.tripartiteBlockEquiv e).symm
        (MarkovDilation.tripartiteBlockEquiv e).symm M = B) :
    Matrix.reindex (HayashiMarkov.abcEquiv (overlappingMiddleBlockEquiv e))
        (HayashiMarkov.abcEquiv (overlappingMiddleBlockEquiv e)) M =
      Matrix.reindex (HayashiMarkov.sigmaAssoc d m)
        (HayashiMarkov.sigmaAssoc d m) B := by
  let T := MarkovDilation.tripartiteBlockEquiv
    (A := Fin dA) (C := Fin dC) e
  let H := HayashiMarkov.abcEquiv
    (dA := dA) (dB := dB) (dC := dC) (dL := d) (dR := m)
    (overlappingMiddleBlockEquiv e)
  let S := HayashiMarkov.sigmaAssoc
    (dA := dA) (dC := dC) d m
  have hCoord : T.trans H = S := by
    apply Equiv.ext
    rintro ⟨q, ⟨⟨i, s⟩, ⟨r, k⟩⟩⟩
    simp [T, H, S, HayashiMarkov.abcEquiv,
      overlappingMiddleBlockEquiv, HayashiMarkov.sigmaAssoc]
  ext x y
  have hx : T (S.symm x) = H.symm x := by
    apply H.injective
    rw [H.apply_symm_apply]
    have hz := congrFun (congrArg Equiv.toFun hCoord) (S.symm x)
    change H (T (S.symm x)) = S (S.symm x) at hz
    rw [S.apply_symm_apply] at hz
    exact hz
  have hy : T (S.symm y) = H.symm y := by
    apply H.injective
    rw [H.apply_symm_apply]
    have hz := congrFun (congrArg Equiv.toFun hCoord) (S.symm y)
    change H (T (S.symm y)) = S (S.symm y) at hz
    rw [S.apply_symm_apply] at hz
    exact hz
  have hxy := congrFun (congrFun hM (S.symm x)) (S.symm y)
  change M (H.symm x) (H.symm y) = B (S.symm x) (S.symm y)
  rw [← hx, ← hy]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, T]
    using hxy

omit [DecidableEq a] [DecidableEq b] in
/-- The natural lift on the first two factors preserves multiplication. -/
private theorem leftOverlappingLift_mul (X Y : Matrix (a × b) (a × b) ℂ) :
    leftOverlappingLift (c := c) (X * Y) =
      leftOverlappingLift X * leftOverlappingLift Y := by
  ext p q
  simp only [leftOverlappingLift, Matrix.mul_apply]
  conv_rhs => rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply]

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- Conjugate transpose commutes with the natural lift on the first two
factors. -/
private theorem leftOverlappingLift_star (X : Matrix (a × b) (a × b) ℂ) :
    leftOverlappingLift (c := c) (star X) = star (leftOverlappingLift X) := by
  ext p q
  rcases p with ⟨p, k⟩
  rcases q with ⟨q, k'⟩
  by_cases h : k = k'
  · subst k'
    simp [leftOverlappingLift]
  · simp [leftOverlappingLift, h, Ne.symm h]

omit [DecidableEq b] [DecidableEq c] in
/-- The natural lift on the last two factors preserves multiplication. -/
private theorem rightOverlappingLift_mul (X Y : Matrix (b × c) (b × c) ℂ) :
    rightOverlappingLift (a := a) (X * Y) =
      rightOverlappingLift X * rightOverlappingLift Y := by
  ext p q
  simp only [rightOverlappingLift, Matrix.mul_apply]
  conv_rhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  by_cases h : p.1.1 = q.1.1
  · simp [Matrix.one_apply, h, Fintype.sum_prod_type]
  · simp [Matrix.one_apply, h]

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] in
/-- Conjugate transpose commutes with the natural lift on the last two
factors. -/
private theorem rightOverlappingLift_star (X : Matrix (b × c) (b × c) ℂ) :
    rightOverlappingLift (a := a) (star X) = star (rightOverlappingLift X) := by
  ext p q
  rcases p with ⟨⟨i, j⟩, k⟩
  rcases q with ⟨⟨i', j'⟩, k'⟩
  by_cases h : i = i'
  · subst i'
    simp [rightOverlappingLift]
  · simp [rightOverlappingLift, h, Ne.symm h]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq b] in
/-- The right overlapping lift of a middle-system operator is its three-factor
Kronecker lift. -/
private theorem rightOverlappingLift_kronecker_one (U : Matrix b b ℂ) :
    rightOverlappingLift (a := a) (U ⊗ₖ (1 : Matrix c c ℂ)) =
      ((1 : Matrix a a ℂ) ⊗ₖ U) ⊗ₖ (1 : Matrix c c ℂ) := by
  ext p q
  simp [rightOverlappingLift]
  ring

omit [DecidableEq b] in
/-- Orthogonal middle supports force the product of two overlapping operators
to vanish. -/
private theorem overlappingLifts_mul_eq_zero_of_middle_mul_eq_zero
    (X : Matrix (a × b) (a × b) ℂ)
    (Y : Matrix (b × c) (b × c) ℂ)
    (P Q : Matrix b b ℂ)
    (hXP : X * ((1 : Matrix a a ℂ) ⊗ₖ P) = X)
    (hQY : (Q ⊗ₖ (1 : Matrix c c ℂ)) * Y = Y)
    (hPQ : P * Q = 0) :
    leftOverlappingLift X * rightOverlappingLift Y = 0 := by
  classical
  have hMiddle :
      leftOverlappingLift (c := c) ((1 : Matrix a a ℂ) ⊗ₖ P) *
          rightOverlappingLift (a := a)
            (Q ⊗ₖ (1 : Matrix c c ℂ)) = 0 := by
    rw [rightOverlappingLift_kronecker_one]
    change (((1 : Matrix a a ℂ) ⊗ₖ P) ⊗ₖ
        (1 : Matrix c c ℂ)) *
      (((1 : Matrix a a ℂ) ⊗ₖ Q) ⊗ₖ
        (1 : Matrix c c ℂ)) = 0
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPQ]
    simp
  calc
    leftOverlappingLift X * rightOverlappingLift Y =
        leftOverlappingLift (X * ((1 : Matrix a a ℂ) ⊗ₖ P)) *
          rightOverlappingLift
            ((Q ⊗ₖ (1 : Matrix c c ℂ)) * Y) := by rw [hXP, hQY]
    _ = (leftOverlappingLift X *
          leftOverlappingLift ((1 : Matrix a a ℂ) ⊗ₖ P)) *
        (rightOverlappingLift (Q ⊗ₖ (1 : Matrix c c ℂ)) *
          rightOverlappingLift Y) := by
      rw [← leftOverlappingLift_mul, ← rightOverlappingLift_mul]
    _ = leftOverlappingLift X *
        (leftOverlappingLift ((1 : Matrix a a ℂ) ⊗ₖ P) *
          rightOverlappingLift (Q ⊗ₖ (1 : Matrix c c ℂ))) *
        rightOverlappingLift Y := by simp only [mul_assoc]
    _ = 0 := by rw [hMiddle]; simp

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- The left overlapping lift preserves finite sums. -/
private theorem leftOverlappingLift_sum {I : Type*} [Fintype I]
    (X : I → Matrix (a × b) (a × b) ℂ) :
    leftOverlappingLift (c := c) (∑ i, X i) =
      ∑ i, leftOverlappingLift (c := c) (X i) := by
  ext p q
  simp only [leftOverlappingLift, Matrix.sum_apply]
  rw [Finset.sum_mul]

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- The left overlapping lift preserves scalar multiplication. -/
private theorem leftOverlappingLift_smul (z : ℂ)
    (X : Matrix (a × b) (a × b) ℂ) :
    leftOverlappingLift (c := c) (z • X) =
      z • leftOverlappingLift (c := c) X := by
  ext p q
  simp [leftOverlappingLift]
  ring

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] in
/-- The right overlapping lift preserves finite sums. -/
private theorem rightOverlappingLift_sum {I : Type*} [Fintype I]
    (X : I → Matrix (b × c) (b × c) ℂ) :
    rightOverlappingLift (a := a) (∑ i, X i) =
      ∑ i, rightOverlappingLift (a := a) (X i) := by
  ext p q
  simp only [rightOverlappingLift, Matrix.sum_apply]
  rw [Finset.mul_sum]

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] in
/-- The right overlapping lift preserves scalar multiplication. -/
private theorem rightOverlappingLift_smul (z : ℂ)
    (X : Matrix (b × c) (b × c) ℂ) :
    rightOverlappingLift (a := a) (z • X) =
      z • rightOverlappingLift (a := a) X := by
  ext p q
  simp [rightOverlappingLift]
  ring

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- Positivity of a left overlapping lift implies positivity of the local
operator whenever the complementary factor has a basis element. -/
private theorem posSemidef_of_leftOverlappingLift_posSemidef
    (X : Matrix (a × b) (a × b) ℂ) (k : c)
    (hX : (leftOverlappingLift (c := c) X).PosSemidef) : X.PosSemidef := by
  have hPrincipal := hX.submatrix (fun x : a × b ↦ (x, k))
  have hPrincipalEq :
      (leftOverlappingLift (c := c) X).submatrix
          (fun x : a × b ↦ (x, k)) (fun x : a × b ↦ (x, k)) = X := by
    ext p q
    change X p q * (1 : Matrix c c ℂ) k k = X p q
    simp
  rw [hPrincipalEq] at hPrincipal
  exact hPrincipal

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] in
/-- Positivity of a right overlapping lift implies positivity of the local
operator whenever the complementary factor has a basis element. -/
private theorem posSemidef_of_rightOverlappingLift_posSemidef
    (Y : Matrix (b × c) (b × c) ℂ) (i : a)
    (hY : (rightOverlappingLift (a := a) Y).PosSemidef) : Y.PosSemidef := by
  have hPrincipal := hY.submatrix (fun x : b × c ↦ ((i, x.1), x.2))
  have hPrincipalEq :
      (rightOverlappingLift (a := a) Y).submatrix
          (fun x : b × c ↦ ((i, x.1), x.2))
          (fun x : b × c ↦ ((i, x.1), x.2)) = Y := by
    ext p q
    change (1 : Matrix a a ℂ) i i * Y p q = Y p q
    simp
  rw [hPrincipalEq] at hPrincipal
  exact hPrincipal

/-- Reassociating the HJPW middle-system lift gives the left-associated
three-factor Kronecker product. -/
private theorem reindex_prodAssoc_symm_liftB
    {dA dB dC : ℕ} (U : Matrix (Fin dB) (Fin dB) ℂ) :
    Matrix.reindex (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
        (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
        (HayashiMarkov.liftB (dA := dA) (dC := dC) U) =
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
        (1 : Matrix (Fin dC) (Fin dC) ℂ) := by
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  simp [HayashiMarkov.liftB, Matrix.reindex_apply]
  ring

/-- Reassociating conjugation by the HJPW middle-system lift gives
conjugation by the corresponding left-associated Kronecker unitary. -/
private theorem reindex_prodAssoc_symm_liftB_conj
    {dA dB dC : ℕ} (U : Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix (Fin dA × (Fin dB × Fin dC))
      (Fin dA × (Fin dB × Fin dC)) ℂ) :
    Matrix.reindex (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
        (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
        (HayashiMarkov.liftB (dA := dA) (dC := dC) (star U) * ρ *
          (HayashiMarkov.liftB (dA := dA) (dC := dC) (star U))ᴴ) =
      star (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
          (1 : Matrix (Fin dC) (Fin dC) ℂ)) *
        Matrix.reindex (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
          (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm ρ *
        (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
          (1 : Matrix (Fin dC) (Fin dC) ℂ)) := by
  change (Matrix.reindexAlgEquiv ℂ ℂ
      (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm)
      (_ * ρ * _) = _
  rw [map_mul, map_mul]
  simp only [Matrix.coe_reindexAlgEquiv]
  rw [reindex_prodAssoc_symm_liftB]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose,
    HayashiMarkov.liftB]
  rw [show Matrix.reindex
      (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
      (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (U ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))) =
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
        (1 : Matrix (Fin dC) (Fin dC) ℂ) by
      exact reindex_prodAssoc_symm_liftB U]

/-- The spatial decomposition of two positive commuting overlapping operators
puts their product into a direct sum of positive tensor products.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1, combined with the
positive normalization used in HJPW, arXiv:quant-ph/0304007, Appendix A. -/
private theorem exists_unitary_positive_blockProduct_of_overlappingLifts_commute
    (X : Matrix (a × b) (a × b) ℂ) (Y : Matrix (b × c) (b × c) ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hComm : leftOverlappingLift X * rightOverlappingLift Y =
      rightOverlappingLift Y * leftOverlappingLift X) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ b)
      (U : Matrix b b ℂ)
      (R : ∀ q, Matrix (a × Fin (d q)) (a × Fin (d q)) ℂ)
      (S : ∀ q, Matrix (Fin (m q) × c) (Fin (m q) × c) ℂ),
      U ∈ Matrix.unitaryGroup b ℂ ∧
        (∀ q, 0 < d q) ∧ (∀ q, 0 < m q) ∧
        (∀ q, (R q).PosSemidef) ∧ (∀ q, (S q).PosSemidef) ∧
        Matrix.reindex (overlappingSpatialBlockEquiv e).symm
            (overlappingSpatialBlockEquiv e).symm
            (star (((1 : Matrix a a ℂ) ⊗ₖ U) ⊗ₖ (1 : Matrix c c ℂ)) *
              (leftOverlappingLift X * rightOverlappingLift Y) *
              (((1 : Matrix a a ℂ) ⊗ₖ U) ⊗ₖ (1 : Matrix c c ℂ))) =
          Matrix.blockDiagonal' fun q ↦ R q ⊗ₖ S q := by
  obtain ⟨K, d, m, e, U, R, S, hU, hd, hm, hRherm, hSherm, hR, hS⟩ :=
    exists_unitary_blockActions_of_overlappingLifts_commute X Y
      hX.isHermitian hY.isHermitian hComm
  have hRpos : ∀ q, (R q).PosSemidef := by
    intro q
    let W := (1 : Matrix a a ℂ) ⊗ₖ U
    have hConj : (star W * X * W).PosSemidef := by
      simpa only [Matrix.star_eq_conjTranspose] using
        hX.conjTranspose_mul_mul_same W
    have hBlock :
        (Matrix.blockDiagonal' fun q ↦
          R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ)).PosSemidef := by
      rw [← hR]
      simpa [W, Matrix.reindex_apply] using
        hConj.submatrix (leftSpatialBlockEquiv e)
    let r : Fin (m q) := ⟨0, hm q⟩
    have hPrincipal := hBlock.submatrix
      (fun x : a × Fin (d q) ↦ ⟨q, (x, r)⟩)
    have hPrincipalEq :
        (Matrix.blockDiagonal' fun q ↦
          R q ⊗ₖ (1 : Matrix (Fin (m q)) (Fin (m q)) ℂ)).submatrix
            (fun x : a × Fin (d q) ↦ ⟨q, (x, r)⟩)
            (fun x : a × Fin (d q) ↦ ⟨q, (x, r)⟩) = R q := by
      ext x y
      simp [Matrix.blockDiagonal'_apply_eq]
    rw [hPrincipalEq] at hPrincipal
    exact hPrincipal
  have hSpos : ∀ q, (S q).PosSemidef := by
    intro q
    let W := U ⊗ₖ (1 : Matrix c c ℂ)
    have hConj : (star W * Y * W).PosSemidef := by
      simpa only [Matrix.star_eq_conjTranspose] using
        hY.conjTranspose_mul_mul_same W
    have hBlock :
        (Matrix.blockDiagonal' fun q ↦
          (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q).PosSemidef := by
      rw [← hS]
      simpa [W, Matrix.reindex_apply] using
        hConj.submatrix (rightSpatialBlockEquiv e)
    let s : Fin (d q) := ⟨0, hd q⟩
    have hPrincipal := hBlock.submatrix
      (fun x : Fin (m q) × c ↦ ⟨q, (s, x)⟩)
    have hPrincipalEq :
        (Matrix.blockDiagonal' fun q ↦
          (1 : Matrix (Fin (d q)) (Fin (d q)) ℂ) ⊗ₖ S q).submatrix
            (fun x : Fin (m q) × c ↦ ⟨q, (s, x)⟩)
            (fun x : Fin (m q) × c ↦ ⟨q, (s, x)⟩) = S q := by
      ext x y
      simp [Matrix.blockDiagonal'_apply_eq]
    rw [hPrincipalEq] at hPrincipal
    exact hPrincipal
  refine ⟨K, d, m, e, U, R, S, hU, hd, hm, hRpos, hSpos, ?_⟩
  let V := ((1 : Matrix a a ℂ) ⊗ₖ U) ⊗ₖ (1 : Matrix c c ℂ)
  let E := overlappingSpatialBlockEquiv (a := a) (c := c) e
  have hLeftGlobal :
      Matrix.reindex E.symm E.symm
          (star V * leftOverlappingLift X * V) =
        Matrix.blockDiagonal' fun q ↦
          R q ⊗ₖ (1 : Matrix (Fin (m q) × c) (Fin (m q) × c) ℂ) := by
    change Matrix.reindex E.symm E.symm
        (star (leftOverlappingLift ((1 : Matrix a a ℂ) ⊗ₖ U)) *
          leftOverlappingLift X *
          leftOverlappingLift ((1 : Matrix a a ℂ) ⊗ₖ U)) = _
    rw [← leftOverlappingLift_star,
      ← leftOverlappingLift_mul, ← leftOverlappingLift_mul]
    ext x y
    rcases x with ⟨q, ⟨⟨i, s⟩, ⟨r, k⟩⟩⟩
    rcases y with ⟨q', ⟨⟨i', s'⟩, ⟨r', k'⟩⟩⟩
    by_cases hq : q = q'
    · subst q'
      have hEntry := congrFun (congrFun hR ⟨q, ((i, s), r)⟩)
        ⟨q, ((i', s'), r')⟩
      rw [Matrix.blockDiagonal'_apply_eq] at hEntry ⊢
      have hScaled := congrArg
        (fun z : ℂ ↦ z * (1 : Matrix c c ℂ) k k') hEntry
      by_cases hr : r = r' <;> by_cases hk : k = k'
      all_goals
        simp [E, overlappingSpatialBlockEquiv, leftSpatialBlockEquiv,
          leftOverlappingLift, Matrix.reindex_apply, Matrix.one_apply,
          hr, hk] at hScaled ⊢ <;> exact hScaled
    · have hEntry := congrFun (congrFun hR ⟨q, ((i, s), r)⟩)
        ⟨q', ((i', s'), r')⟩
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hq] at hEntry ⊢
      have hScaled := congrArg
        (fun z : ℂ ↦ z * (1 : Matrix c c ℂ) k k') hEntry
      simpa [E, overlappingSpatialBlockEquiv, leftSpatialBlockEquiv,
        leftOverlappingLift, Matrix.reindex_apply, Matrix.one_apply] using hScaled
  have hRightGlobal :
      Matrix.reindex E.symm E.symm
          (star V * rightOverlappingLift Y * V) =
        Matrix.blockDiagonal' fun q ↦
          (1 : Matrix (a × Fin (d q)) (a × Fin (d q)) ℂ) ⊗ₖ S q := by
    dsimp only [V]
    rw [← rightOverlappingLift_kronecker_one (a := a) (c := c) U]
    rw [← rightOverlappingLift_star,
      ← rightOverlappingLift_mul, ← rightOverlappingLift_mul]
    ext x y
    rcases x with ⟨q, ⟨⟨i, s⟩, ⟨r, k⟩⟩⟩
    rcases y with ⟨q', ⟨⟨i', s'⟩, ⟨r', k'⟩⟩⟩
    by_cases hq : q = q'
    · subst q'
      have hEntry := congrFun (congrFun hS ⟨q, (s, (r, k))⟩)
        ⟨q, (s', (r', k'))⟩
      rw [Matrix.blockDiagonal'_apply_eq] at hEntry ⊢
      have hScaled := congrArg
        (fun z : ℂ ↦ (1 : Matrix a a ℂ) i i' * z) hEntry
      by_cases hi : i = i' <;> by_cases hs : s = s'
      all_goals
        simp [E, overlappingSpatialBlockEquiv, rightSpatialBlockEquiv,
          rightOverlappingLift, Matrix.reindex_apply, Matrix.one_apply,
          hi, hs] at hScaled ⊢ <;> exact hScaled
    · have hEntry := congrFun (congrFun hS ⟨q, (s, (r, k))⟩)
        ⟨q', (s', (r', k'))⟩
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hq] at hEntry ⊢
      have hScaled := congrArg
        (fun z : ℂ ↦ (1 : Matrix a a ℂ) i i' * z) hEntry
      simpa [E, overlappingSpatialBlockEquiv, rightSpatialBlockEquiv,
        rightOverlappingLift, Matrix.reindex_apply, Matrix.one_apply] using hScaled
  have hV : V ∈ Matrix.unitaryGroup ((a × b) × c) ℂ := by
    exact Matrix.kronecker_mem_unitary
      (Matrix.kronecker_mem_unitary (one_mem _) hU) (one_mem _)
  have hVmul : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have hsplit :
      star V * (leftOverlappingLift X * rightOverlappingLift Y) * V =
        (star V * leftOverlappingLift X * V) *
          (star V * rightOverlappingLift Y * V) := by
    symm
    calc
      (star V * leftOverlappingLift X * V) *
          (star V * rightOverlappingLift Y * V) =
        (star V * leftOverlappingLift X) * (V * star V) *
          rightOverlappingLift Y * V := by simp only [mul_assoc]
      _ = star V * (leftOverlappingLift X * rightOverlappingLift Y) * V := by
        rw [hVmul]
        simp [mul_assoc]
  change Matrix.reindex E.symm E.symm
      (star V * (leftOverlappingLift X * rightOverlappingLift Y) * V) = _
  rw [hsplit]
  change (Matrix.reindexLinearEquiv ℂ ℂ E.symm E.symm)
      ((star V * leftOverlappingLift X * V) *
        (star V * rightOverlappingLift Y * V)) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ E.symm E.symm E.symm]
  change Matrix.reindex E.symm E.symm
        (star V * leftOverlappingLift X * V) *
      Matrix.reindex E.symm E.symm
        (star V * rightOverlappingLift Y * V) = _
  rw [hLeftGlobal, hRightGlobal, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext q
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- A positive direct sum of overlapping tensor factors, normalized to trace
one, gives the HJPW quantum Markov decomposition.

Source: Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246 (2004),
Theorem 6, equations (11), (14), and (15). -/
private theorem nonempty_quantumMarkovDecomposition_of_positive_blockProduct
    {dA dB dC K : ℕ} {d m : Fin K → ℕ}
    (ρ : Matrix (Fin dA × (Fin dB × Fin dC))
      (Fin dA × (Fin dB × Fin dC)) ℂ)
    (hρtrace : ρ.trace = 1)
    (e : ((q : Fin K) × (Fin (m q) × Fin (d q))) ≃ Fin dB)
    (U : Matrix (Fin dB) (Fin dB) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin dB) ℂ)
    (R : ∀ q, Matrix (Fin dA × Fin (d q)) (Fin dA × Fin (d q)) ℂ)
    (S : ∀ q, Matrix (Fin (m q) × Fin dC) (Fin (m q) × Fin dC) ℂ)
    (hd : ∀ q, 0 < d q) (hm : ∀ q, 0 < m q)
    (hR : ∀ q, (R q).PosSemidef) (hS : ∀ q, (S q).PosSemidef)
    (hBlock : Matrix.reindex (overlappingSpatialBlockEquiv e).symm
        (overlappingSpatialBlockEquiv e).symm
        (star (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
            (1 : Matrix (Fin dC) (Fin dC) ℂ)) *
          Matrix.reindex (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
            (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm ρ *
          (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
            (1 : Matrix (Fin dC) (Fin dC) ℂ))) =
      Matrix.blockDiagonal' fun q ↦ R q ⊗ₖ S q) :
    Nonempty (Entropy.QuantumMarkovDecomposition ρ) := by
  classical
  have hABC : Nonempty (Fin dA × (Fin dB × Fin dC)) :=
    Matrix.nonempty_of_trace_eq_one ρ hρtrace
  let a₀ : Fin dA := hABC.some.1
  let c₀ : Fin dC := hABC.some.2.2
  let p : Fin K → ℝ := fun q ↦ (R q).trace.re * (S q).trace.re
  let ρL : ∀ q, Matrix (Fin dA × Fin (d q)) (Fin dA × Fin (d q)) ℂ :=
    fun q ↦ Matrix.normalizePosSemidef (a₀, ⟨0, hd q⟩) (R q)
  let ρR : ∀ q, Matrix (Fin (m q) × Fin dC) (Fin (m q) × Fin dC) ℂ :=
    fun q ↦ Matrix.normalizePosSemidef (⟨0, hm q⟩, c₀) (S q)
  have hNormalized :
      Matrix.blockDiagonal' (fun q ↦ R q ⊗ₖ S q) =
        Matrix.blockDiagonal' (fun q ↦
          (p q : ℂ) • (ρL q ⊗ₖ ρR q)) := by
    apply congrArg Matrix.blockDiagonal'
    funext q
    simpa [p, ρL, ρR] using
      (Matrix.kronecker_eq_trace_re_mul_normalized
        (a₀, ⟨0, hd q⟩) (⟨0, hm q⟩, c₀) (hR q) (hS q))
  have hpSum : ∑ q, p q = 1 := by
    let V := ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) ⊗ₖ
      (1 : Matrix (Fin dC) (Fin dC) ℂ)
    have hV : V ∈ Matrix.unitaryGroup ((Fin dA × Fin dB) × Fin dC) ℂ :=
      Matrix.kronecker_mem_unitary
        (Matrix.kronecker_mem_unitary (one_mem _) hU) (one_mem _)
    have hVmul : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
    have htr := congrArg Matrix.trace (hBlock.trans hNormalized)
    change Matrix.trace (Matrix.reindex (overlappingSpatialBlockEquiv e).symm
        (overlappingSpatialBlockEquiv e).symm
        (star V * Matrix.reindex
          (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
          (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm ρ * V)) = _ at htr
    rw [Matrix.trace_reindex, Matrix.trace_mul_cycle, hVmul, Matrix.one_mul,
      Matrix.trace_reindex, hρtrace, Matrix.trace_blockDiagonal'] at htr
    have hLt (q : Fin K) : (ρL q).trace = 1 :=
      Matrix.normalizePosSemidef_trace _ (hR q)
    have hRt (q : Fin K) : (ρR q).trace = 1 :=
      Matrix.normalizePosSemidef_trace _ (hS q)
    simp_rw [Matrix.trace_smul, Matrix.trace_kronecker, hLt, hRt,
      mul_one] at htr
    have hpR := congrArg Complex.re htr.symm
    simpa using hpR
  have hstarU : star U ∈ Matrix.unitaryGroup (Fin dB) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  refine ⟨{
    m := K
    dL := d
    dR := m
    decompB := overlappingMiddleBlockEquiv e
    U_B := ⟨star U, hstarU⟩
    p := p
    hp_nonneg := ?_
    hp_sum := hpSum
    ρ_left := ρL
    ρ_right := ρR
    hρ_left_dm := ?_
    hρ_right_dm := ?_
    h_state := ?_ }⟩
  · intro q
    exact mul_nonneg
      (Complex.nonneg_iff.mp (hR q).trace_nonneg).1
      (Complex.nonneg_iff.mp (hS q).trace_nonneg).1
  · intro q
    exact ⟨Matrix.normalizePosSemidef_posSemidef _ (hR q),
      Matrix.normalizePosSemidef_trace _ (hR q)⟩
  · intro q
    exact ⟨Matrix.normalizePosSemidef_posSemidef _ (hS q),
      Matrix.normalizePosSemidef_trace _ (hS q)⟩
  · let Mconj :=
      HayashiMarkov.liftB (dA := dA) (dC := dC) (star U) * ρ *
        (HayashiMarkov.liftB (dA := dA) (dC := dC) (star U))ᴴ
    have hRaw : Matrix.reindex
        (MarkovDilation.tripartiteBlockEquiv e).symm
        (MarkovDilation.tripartiteBlockEquiv e).symm Mconj =
      Matrix.blockDiagonal' (fun q ↦ (p q : ℂ) • (ρL q ⊗ₖ ρR q)) := by
      rw [← hNormalized, ← hBlock]
      have hConj := reindex_prodAssoc_symm_liftB_conj U ρ
      ext x y
      have hxy := congrFun (congrFun hConj
        (overlappingSpatialBlockEquiv e x))
        (overlappingSpatialBlockEquiv e y)
      rcases x with ⟨q, ⟨⟨i, s⟩, ⟨r, k⟩⟩⟩
      rcases y with ⟨q', ⟨⟨i', s'⟩, ⟨r', k'⟩⟩⟩
      simpa [Mconj, Matrix.reindex_apply, Matrix.submatrix_apply,
        overlappingSpatialBlockEquiv] using hxy
    unfold HayashiMarkov.blockState
    exact reindex_abcEquiv_eq_reindex_sigmaAssoc_of_reindex_tripartite
      e Mconj _ hRaw

/-- A trace-one product of positive commuting operators on (A B) and
(B C) is a quantum Markov state with middle system (B).

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1, combined with
Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246 (2004), Theorem 6. -/
theorem exists_quantumMarkovDecomposition_of_positive_overlapping_product
    {dA dB dC : ℕ}
    (ρ : Matrix (Fin dA × (Fin dB × Fin dC))
      (Fin dA × (Fin dB × Fin dC)) ℂ)
    (hρtrace : ρ.trace = 1)
    (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Y : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hComm : leftOverlappingLift X * rightOverlappingLift Y =
      rightOverlappingLift Y * leftOverlappingLift X)
    (hFactor : Matrix.reindex
        (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm
        (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).symm ρ =
      leftOverlappingLift X * rightOverlappingLift Y) :
    Nonempty (Entropy.QuantumMarkovDecomposition ρ) := by
  obtain ⟨K, d, m, e, U, R, S, hU, hd, hm, hR, hS, hBlock⟩ :=
    exists_unitary_positive_blockProduct_of_overlappingLifts_commute
      X Y hX hY hComm
  apply nonempty_quantumMarkovDecomposition_of_positive_blockProduct
    ρ hρtrace e U hU R S hd hm hR hS
  simpa only [hFactor] using hBlock

end Matrix

namespace MPOTensor

/-- Decode the noncontiguous middle subsystem (B=\{1,3\}) from one basis
label. -/
private def fourCycleMiddlePair (d : ℕ) (b : Fin (d * d)) : Fin d × Fin d :=
  (finProdFinEquiv (m := d) (n := d)).symm b

/-- The four-site regrouping (A=\{0\}), (B=\{1,3\}), (C=\{2\}).

This is the coordinate boundary used to apply the Markov criterion to the
four-site instance derived from arXiv:1606.00608, Definition 4.8,
lines 829--850. -/
def fourCycleTripartiteEquiv (d : ℕ) :
    (Fin d × (Fin (d * d) × Fin d)) ≃ (Fin 4 → Fin d) where
  toFun x := ![x.1, (fourCycleMiddlePair d x.2.1).1,
    x.2.2, (fourCycleMiddlePair d x.2.1).2]
  invFun σ := (σ 0,
    finProdFinEquiv (m := d) (n := d) (σ 1, σ 3), σ 2)
  left_inv x := by
    obtain ⟨a, b, c⟩ := x
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact (finProdFinEquiv (m := d) (n := d)).apply_symm_apply b
    · rfl
  right_inv σ := by
    funext i
    fin_cases i <;> simp [fourCycleMiddlePair]

/-- The same four-site regrouping in the left-associated coordinates used by
overlapping lifts. -/
private def fourCycleOverlappingEquiv (d : ℕ) :
    ((Fin d × Fin (d * d)) × Fin d) ≃ (Fin 4 → Fin d) :=
  (Equiv.prodAssoc (Fin d) (Fin (d * d)) (Fin d)).trans
    (fourCycleTripartiteEquiv d)

/-- Regroup three consecutive sites ordered as (3,0,1) into the (A B)
factor of the four-cycle tripartition. -/
private def fourCycleABFactorEquiv (d : ℕ) :
    ((Fin d × Fin d) × Fin d) ≃ (Fin d × Fin (d * d)) where
  toFun x := (x.1.2,
    finProdFinEquiv (m := d) (n := d) (x.2, x.1.1))
  invFun x :=
    let b := fourCycleMiddlePair d x.2
    ((b.2, x.1), b.1)
  left_inv x := by
    obtain ⟨⟨i, j⟩, k⟩ := x
    simp [fourCycleMiddlePair]
  right_inv x := by
    obtain ⟨i, j⟩ := x
    apply Prod.ext
    · rfl
    · exact (finProdFinEquiv (m := d) (n := d)).apply_symm_apply j

/-- Regroup three consecutive sites ordered as (1,2,3) into the (B C)
factor of the four-cycle tripartition. -/
private def fourCycleBCFactorEquiv (d : ℕ) :
    ((Fin d × Fin d) × Fin d) ≃ (Fin (d * d) × Fin d) where
  toFun x :=
    (finProdFinEquiv (m := d) (n := d) (x.1.1, x.2), x.1.2)
  invFun x :=
    let b := fourCycleMiddlePair d x.1
    ((b.1, x.2), b.2)
  left_inv x := by
    obtain ⟨⟨i, j⟩, k⟩ := x
    simp [fourCycleMiddlePair]
  right_inv x := by
    obtain ⟨i, j⟩ := x
    apply Prod.ext
    · exact (finProdFinEquiv (m := d) (n := d)).apply_symm_apply i
    · rfl

/-- The three-site window (3,0,1) written in the (A B) coordinates of the
four-cycle tripartition. -/
private def fourCycleABWindowEquiv (d : ℕ) :
    (Fin d × Fin (d * d)) ≃ (Fin 3 → Fin d) :=
  (fourCycleABFactorEquiv d).symm.trans
    (threeSiteOverlappingEquiv (Fin d)).symm

/-- The three-site window (1,2,3) written in the (B C) coordinates of the
four-cycle tripartition. -/
private def fourCycleBCWindowEquiv (d : ℕ) :
    (Fin (d * d) × Fin d) ≃ (Fin 3 → Fin d) :=
  (fourCycleBCFactorEquiv d).symm.trans
    (threeSiteOverlappingEquiv (Fin d)).symm

/-- A three-site operator on sites (3,0,1) becomes an (A B)-operator tensored
with the identity on C in the four-cycle tripartition. -/
private theorem reindex_embedLocalOperator_three_eq_leftOverlappingLift
    (T : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) :
    Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm
        (embedLocalOperator (d := d) 3 4 (by decide) (3 : Fin 4) T) =
      Matrix.leftOverlappingLift
        (Matrix.reindex (fourCycleABWindowEquiv d).symm
          (fourCycleABWindowEquiv d).symm T) := by
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  have hAgree :
      AgreesOutsideWindow (d := d) 3 (by decide) (3 : Fin 4)
          (fourCycleOverlappingEquiv d ⟨⟨a, b⟩, c⟩)
          (fourCycleOverlappingEquiv d ⟨⟨a', b'⟩, c'⟩) ↔
        c' = c := by
    rw [agreesOutsideWindow_iff]
    constructor
    · intro h
      simpa [fourCycleOverlappingEquiv, fourCycleTripartiteEquiv] using
        h (2 : Fin 4) (by decide)
    · intro h k hk
      fin_cases k <;>
        simp [fourCycleOverlappingEquiv, fourCycleTripartiteEquiv] at hk ⊢
      exact h
  have hExtract (a : Fin d) (b : Fin (d * d)) (c : Fin d) :
      MPSTensor.extractWindow 3 (3 : Fin 4)
          (fourCycleOverlappingEquiv d ⟨⟨a, b⟩, c⟩) =
        fourCycleABWindowEquiv d (a, b) := by
    funext k
    fin_cases k <;>
      simp [MPSTensor.extractWindow, fourCycleOverlappingEquiv,
        fourCycleTripartiteEquiv, fourCycleABWindowEquiv,
        fourCycleABFactorEquiv, threeSiteOverlappingEquiv,
        fourCycleMiddlePair]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply, Matrix.leftOverlappingLift,
    Matrix.one_apply, Equiv.symm_symm]
  rw [hExtract, hExtract]
  by_cases h : c' = c
  · rw [ite_eq_left (hAgree.mpr h), ite_eq_left h.symm, mul_one]
  · rw [ite_eq_right (hAgree.not.mpr h),
      ite_eq_right (Ne.symm h), mul_zero]

/-- A three-site operator on sites (1,2,3) becomes a (B C)-operator tensored
with the identity on A in the four-cycle tripartition. -/
private theorem reindex_embedLocalOperator_three_eq_rightOverlappingLift
    (T : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) :
    Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm
        (embedLocalOperator (d := d) 3 4 (by decide) (1 : Fin 4) T) =
      Matrix.rightOverlappingLift
        (Matrix.reindex (fourCycleBCWindowEquiv d).symm
          (fourCycleBCWindowEquiv d).symm T) := by
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  have hAgree :
      AgreesOutsideWindow (d := d) 3 (by decide) (1 : Fin 4)
          (fourCycleOverlappingEquiv d ⟨⟨a, b⟩, c⟩)
          (fourCycleOverlappingEquiv d ⟨⟨a', b'⟩, c'⟩) ↔
        a' = a := by
    rw [agreesOutsideWindow_iff]
    constructor
    · intro h
      simpa [fourCycleOverlappingEquiv, fourCycleTripartiteEquiv] using
        h (0 : Fin 4) (by decide)
    · intro h k hk
      fin_cases k <;>
        simp [fourCycleOverlappingEquiv, fourCycleTripartiteEquiv] at hk ⊢
      exact h
  have hExtract (a : Fin d) (b : Fin (d * d)) (c : Fin d) :
      MPSTensor.extractWindow 3 (1 : Fin 4)
          (fourCycleOverlappingEquiv d ⟨⟨a, b⟩, c⟩) =
        fourCycleBCWindowEquiv d (b, c) := by
    funext k
    fin_cases k <;>
      simp [MPSTensor.extractWindow, fourCycleOverlappingEquiv,
        fourCycleTripartiteEquiv, fourCycleBCWindowEquiv,
        fourCycleBCFactorEquiv, threeSiteOverlappingEquiv,
        fourCycleMiddlePair]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply, Matrix.rightOverlappingLift,
    Matrix.one_apply, Equiv.symm_symm]
  rw [hExtract, hExtract]
  by_cases h : a' = a
  · rw [ite_eq_left (hAgree.mpr h), ite_eq_left h.symm, one_mul]
  · rw [ite_eq_right (hAgree.not.mpr h),
      ite_eq_right (Ne.symm h), zero_mul]

/-- Passing a two-site product to ordered-pair coordinates preserves matrix
multiplication. -/
private theorem pairBondMatrix_mul
    (B C : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    pairBondMatrix (B * C) = pairBondMatrix B * pairBondMatrix C := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (finTwoArrowEquiv (Fin d)))
      (B * C) = _
  exact map_mul _ B C

/-- In ordered-pair coordinates, the two-site sector projection is the
Kronecker square of the one-site projection. -/
private theorem pairBondMatrix_twoSiteSectorProjection
    (P : Matrix (Fin d) (Fin d) ℂ) :
    pairBondMatrix (twoSiteSectorProjection P) = P ⊗ₖ P := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [pairBondMatrix, twoSiteSectorProjection, Matrix.reindex_apply,
    finTwoArrowEquiv]

/-- A four-site chain operator regarded as a tripartite state with
(A={0}), (B={1,3}), and (C={2}).

This is the coordinate boundary used to apply the Markov criterion to the
four-site instance derived from arXiv:1606.00608, Definition 4.8,
lines 829--850. -/
noncomputable def fourCycleTripartiteState (rho : ChainOperator d 4) :
    Matrix (Fin d × (Fin (d * d) × Fin d))
      (Fin d × (Fin (d * d) × Fin d)) ℂ :=
  Matrix.reindex (fourCycleTripartiteEquiv d).symm
    (fourCycleTripartiteEquiv d).symm rho

namespace GSNNCHData

variable {d : ℕ}

/-- A sector bond in ordered-pair coordinates. -/
private noncomputable def pairBondFour (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  pairBondMatrix (data.bond x)

/-- A sector bond is absorbed on the right by its two-site sector projection.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem bond_mul_twoSiteSectorProjection (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    data.bond x * twoSiteSectorProjection (data.sectorProjection x) =
      data.bond x := by
  let Q := twoSiteSectorProjection (data.sectorProjection x)
  have hQ : Q * Q = Q :=
    twoSiteSectorProjection_mul_eq_of_mul_eq _ _ _
      (data.sectorProjection_isOrthogonal x).2
  have hB := data.bond_supported x
  change Q * data.bond x * Q = data.bond x at hB
  calc
    data.bond x * Q = (Q * data.bond x * Q) * Q :=
      congrArg (fun Z ↦ Z * Q) hB.symm
    _ = Q * data.bond x * (Q * Q) := by simp only [mul_assoc]
    _ = Q * data.bond x * Q := by rw [hQ]
    _ = data.bond x := hB

/-- A sector bond is absorbed on the left by its two-site sector projection.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem twoSiteSectorProjection_mul_bond (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    twoSiteSectorProjection (data.sectorProjection x) * data.bond x =
      data.bond x := by
  let Q := twoSiteSectorProjection (data.sectorProjection x)
  have hQ : Q * Q = Q :=
    twoSiteSectorProjection_mul_eq_of_mul_eq _ _ _
      (data.sectorProjection_isOrthogonal x).2
  have hB := data.bond_supported x
  change Q * data.bond x * Q = data.bond x at hB
  calc
    Q * data.bond x = Q * (Q * data.bond x * Q) :=
      congrArg (fun Z ↦ Q * Z) hB.symm
    _ = (Q * Q) * data.bond x * Q := by simp only [mul_assoc]
    _ = Q * data.bond x * Q := by rw [hQ]
    _ = data.bond x := hB

/-- In pair coordinates, a sector bond is absorbed on its right-hand site by
the one-site sector projection.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem pairBondFour_mul_rightSectorProjection (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    data.pairBondFour x *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ data.sectorProjection x) =
      data.pairBondFour x := by
  let P := data.sectorProjection x
  let B := data.pairBondFour x
  have hP : P * P = P := (data.sectorProjection_isOrthogonal x).2
  have hBQ : B * (P ⊗ₖ P) = B := by
    have h := congrArg pairBondMatrix
      (data.bond_mul_twoSiteSectorProjection x)
    simpa [B, P, pairBondFour, pairBondMatrix_mul,
      pairBondMatrix_twoSiteSectorProjection] using h
  have hQright :
      (P ⊗ₖ P) * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P) =
        P ⊗ₖ P := by
    rw [← Matrix.mul_kronecker_mul, hP]
    simp
  calc
    B * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P) =
        (B * (P ⊗ₖ P)) *
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P) :=
      (congrArg (fun Z ↦ Z * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P))
        hBQ).symm
    _ = B * ((P ⊗ₖ P) *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)) := by
      simp only [mul_assoc]
    _ = B * (P ⊗ₖ P) := by rw [hQright]
    _ = B := hBQ

/-- In pair coordinates, a sector bond is absorbed on its left-hand site by
the one-site sector projection.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem leftSectorProjection_mul_pairBondFour (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    (data.sectorProjection x ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * data.pairBondFour x =
      data.pairBondFour x := by
  let P := data.sectorProjection x
  let B := data.pairBondFour x
  have hP : P * P = P := (data.sectorProjection_isOrthogonal x).2
  have hQB : (P ⊗ₖ P) * B = B := by
    have h := congrArg pairBondMatrix
      (data.twoSiteSectorProjection_mul_bond x)
    simpa [B, P, pairBondFour, pairBondMatrix_mul,
      pairBondMatrix_twoSiteSectorProjection] using h
  have hleftQ :
      (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * (P ⊗ₖ P) =
        P ⊗ₖ P := by
    rw [← Matrix.mul_kronecker_mul, hP]
    simp
  calc
    (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * B =
        (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
          ((P ⊗ₖ P) * B) :=
      (congrArg
        (fun Z ↦ (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * Z) hQB).symm
    _ = ((P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * (P ⊗ₖ P)) *
        B := by simp only [mul_assoc]
    _ = (P ⊗ₖ P) * B := by rw [hleftQ]
    _ = B := hQB

/-- Adjacent bonds belonging to distinct orthogonal sectors have zero
overlapping product.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem overlappingLifts_pairBondFour_mul_eq_zero
    (data : GSNNCHData d 4) {x y : Fin data.sectorCount} (hxy : x ≠ y) :
    Matrix.leftOverlappingLift (data.pairBondFour x) *
        Matrix.rightOverlappingLift (data.pairBondFour y) = 0 := by
  exact Matrix.overlappingLifts_mul_eq_zero_of_middle_mul_eq_zero
    (data.pairBondFour x) (data.pairBondFour y)
    (data.sectorProjection x) (data.sectorProjection y)
    (data.pairBondFour_mul_rightSectorProjection x)
    (data.leftSectorProjection_mul_pairBondFour y)
    (data.sectorProjection_orthogonal hxy)

/-- On three consecutive sites, adjacent bonds from distinct sectors have
zero product.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem localAdjacentBonds_mul_eq_zero
    (data : GSNNCHData d 4) {x y : Fin data.sectorCount} (hxy : x ≠ y) :
    embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) (data.bond x) *
        embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) (data.bond y) =
      0 := by
  have h := data.overlappingLifts_pairBondFour_mul_eq_zero hxy
  change Matrix.leftOverlappingLift (pairBondMatrix (data.bond x)) *
    Matrix.rightOverlappingLift (pairBondMatrix (data.bond y)) = 0 at h
  rw [← reindex_embedLocalOperator_zero_eq_leftOverlappingLift,
    ← reindex_embedLocalOperator_one_eq_rightOverlappingLift] at h
  let E := Matrix.reindexAlgEquiv ℂ ℂ
    (threeSiteOverlappingEquiv (Fin d))
  apply E.injective
  rw [map_mul, map_zero]
  exact h

/-- On the four-cycle, the bond at site 0 in one sector annihilates the bond
at site 1 in every distinct sector.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem bondAt_zero_mul_one_eq_zero
    (data : GSNNCHData d 4) {x y : Fin data.sectorCount} (hxy : x ≠ y) :
    data.bondAt x 0 * data.bondAt y 1 = 0 := by
  have h := congrArg
    (embedLocalOperator (d := d) 3 4 (by decide) (0 : Fin 4))
    (data.localAdjacentBonds_mul_eq_zero hxy)
  have hzero : embedLocalOperator (d := d) 3 4 (by decide) (0 : Fin 4)
      (0 : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) = 0 := by
    ext σ τ
    simp [embedLocalOperator_apply]
  rw [hzero] at h
  simpa [GSNNCHData.bondAt, embedLocalOperator_mul,
    PhysicalSectorFactorization.embedLocalOperator_two_zero_nested,
    PhysicalSectorFactorization.embedLocalOperator_two_one_nested] using h

/-- Complementary adjacent-bond products from distinct sectors vanish.

Source: arXiv:1606.00608, Definition 4.8, lines 838--850. -/
private theorem complementaryAdjacentBondProducts_mul_eq_zero
    (data : GSNNCHData d 4) {x y : Fin data.sectorCount} (hxy : x ≠ y) :
    (data.bondAt x 3 * data.bondAt x 0) *
        (data.bondAt y 1 * data.bondAt y 2) = 0 := by
  rw [show (data.bondAt x 3 * data.bondAt x 0) *
      (data.bondAt y 1 * data.bondAt y 2) =
      data.bondAt x 3 * (data.bondAt x 0 * data.bondAt y 1) *
        data.bondAt y 2 by simp only [mul_assoc]]
  rw [data.bondAt_zero_mul_one_eq_zero hxy]
  simp

/-- For one sector, the complementary adjacent-bond products multiply to the
periodic four-bond product.

Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850. -/
private theorem complementaryAdjacentBondProducts_mul_eq_sectorProduct
    (data : GSNNCHData d 4) (x : Fin data.sectorCount) :
    (data.bondAt x 3 * data.bondAt x 0) *
        (data.bondAt x 1 * data.bondAt x 2) =
      data.sectorProduct x := by
  have h30 := data.bondAt_comm x (3 : Fin 4) (0 : Fin 4)
  have h31 := data.bondAt_comm x (3 : Fin 4) (1 : Fin 4)
  have h32 := data.bondAt_comm x (3 : Fin 4) (2 : Fin 4)
  calc
    (data.bondAt x 3 * data.bondAt x 0) *
        (data.bondAt x 1 * data.bondAt x 2) =
      data.bondAt x 0 *
        (data.bondAt x 3 * (data.bondAt x 1 * data.bondAt x 2)) := by
      rw [h30]
      simp only [mul_assoc]
    _ = data.bondAt x 0 *
        ((data.bondAt x 3 * data.bondAt x 1) * data.bondAt x 2) := by
      rw [mul_assoc]
    _ = data.bondAt x 0 *
        ((data.bondAt x 1 * data.bondAt x 3) * data.bondAt x 2) := by
      rw [h31]
    _ = data.bondAt x 0 *
        (data.bondAt x 1 * (data.bondAt x 3 * data.bondAt x 2)) := by
      rw [mul_assoc]
    _ = data.bondAt x 0 *
        (data.bondAt x 1 * (data.bondAt x 2 * data.bondAt x 3)) := by
      rw [h32]
    _ = data.sectorProduct x := by
      simp [sectorProduct]

/-- The product of two adjacent sector bonds on three consecutive sites. -/
private noncomputable def threeSiteBondProduct (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  Matrix.leftOverlappingLift (data.pairBondFour x) *
    Matrix.rightOverlappingLift (data.pairBondFour x)

/-- The two adjacent bonds assigned to the (A B) side of the four-cycle
tripartition. -/
private noncomputable def fourCycleABFactor (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    Matrix (Fin d × Fin (d * d)) (Fin d × Fin (d * d)) ℂ :=
  Matrix.reindex (fourCycleABFactorEquiv d) (fourCycleABFactorEquiv d)
    (data.threeSiteBondProduct x)

/-- The two adjacent bonds assigned to the (B C) side of the four-cycle
tripartition. -/
private noncomputable def fourCycleBCFactor (data : GSNNCHData d 4)
    (x : Fin data.sectorCount) :
    Matrix (Fin (d * d) × Fin d) (Fin (d * d) × Fin d) ℂ :=
  Matrix.reindex (fourCycleBCFactorEquiv d) (fourCycleBCFactorEquiv d)
    (data.threeSiteBondProduct x)

/-- The weighted (A B) operator obtained by summing the bonds on edges
(3,0) and (0,1) over the orthogonal sectors. -/
private noncomputable def fourCycleABOperator (data : GSNNCHData d 4) (c : ℝ) :
    Matrix (Fin d × Fin (d * d)) (Fin d × Fin (d * d)) ℂ :=
  (c : ℂ) • ∑ x : Fin data.sectorCount,
    (data.multiplicity x : ℂ) • data.fourCycleABFactor x

/-- The (B C) operator obtained by summing the bonds on edges (1,2) and
(2,3) over the orthogonal sectors. -/
private noncomputable def fourCycleBCOperator (data : GSNNCHData d 4) :
    Matrix (Fin (d * d) × Fin d) (Fin (d * d) × Fin d) ℂ :=
  ∑ x : Fin data.sectorCount, data.fourCycleBCFactor x

/-- The weighted four-site lift of the adjacent-bond product
$B_3^{(x)}B_0^{(x)}$ on the window $(3,0,1)$. -/
private noncomputable def globalABOperator (data : GSNNCHData d 4) (c : ℝ) :
    ChainOperator d 4 :=
  (c : ℂ) • ∑ x : Fin data.sectorCount,
    (data.multiplicity x : ℂ) •
      (data.bondAt x 3 * data.bondAt x 0)

/-- The four-site lift of the adjacent-bond product
$B_1^{(x)}B_2^{(x)}$ on the window $(1,2,3)$. -/
private noncomputable def globalBCOperator (data : GSNNCHData d 4) :
    ChainOperator d 4 :=
  ∑ x : Fin data.sectorCount,
    data.bondAt x 1 * data.bondAt x 2

/-- The (A B) factor is the adjacent-bond product on the physical window
(3,0,1), transported to the noncontiguous four-cycle coordinates. -/
private theorem fourCycleABFactor_eq_reindex_windowProduct
    (data : GSNNCHData d 4) (x : Fin data.sectorCount) :
    data.fourCycleABFactor x =
      Matrix.reindex (fourCycleABWindowEquiv d).symm
        (fourCycleABWindowEquiv d).symm
        (embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) (data.bond x) *
          embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) (data.bond x)) := by
  rw [fourCycleABFactor, threeSiteBondProduct, pairBondFour,
    ← reindex_embedLocalOperator_zero_eq_leftOverlappingLift,
    ← reindex_embedLocalOperator_one_eq_rightOverlappingLift]
  change (Matrix.reindex (fourCycleABFactorEquiv d)
      (fourCycleABFactorEquiv d))
      ((Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))) _ *
      (Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))) _) = _
  rw [Matrix.reindexLinearEquiv_mul]
  change ((Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
      (threeSiteOverlappingEquiv (Fin d))).trans
      (Matrix.reindex (fourCycleABFactorEquiv d)
        (fourCycleABFactorEquiv d))) _ = _
  rw [Matrix.reindex_trans]
  rfl

/-- The (B C) factor is the adjacent-bond product on the physical window
(1,2,3), transported to the noncontiguous four-cycle coordinates. -/
private theorem fourCycleBCFactor_eq_reindex_windowProduct
    (data : GSNNCHData d 4) (x : Fin data.sectorCount) :
    data.fourCycleBCFactor x =
      Matrix.reindex (fourCycleBCWindowEquiv d).symm
        (fourCycleBCWindowEquiv d).symm
        (embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) (data.bond x) *
          embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) (data.bond x)) := by
  rw [fourCycleBCFactor, threeSiteBondProduct, pairBondFour,
    ← reindex_embedLocalOperator_zero_eq_leftOverlappingLift,
    ← reindex_embedLocalOperator_one_eq_rightOverlappingLift]
  change (Matrix.reindex (fourCycleBCFactorEquiv d)
      (fourCycleBCFactorEquiv d))
      ((Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))) _ *
      (Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))) _) = _
  rw [Matrix.reindexLinearEquiv_mul]
  change ((Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
      (threeSiteOverlappingEquiv (Fin d))).trans
      (Matrix.reindex (fourCycleBCFactorEquiv d)
        (fourCycleBCFactorEquiv d))) _ = _
  rw [Matrix.reindex_trans]
  rfl

/-- In the four-cycle tripartition, the global bonds at sites 3 and 0 are
the natural lift of the (A B) factor. -/
private theorem reindex_bondAt_three_mul_zero_eq_leftOverlappingLift
    (data : GSNNCHData d 4) (x : Fin data.sectorCount) :
    Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm
        (data.bondAt x 3 * data.bondAt x 0) =
      Matrix.leftOverlappingLift (data.fourCycleABFactor x) := by
  rw [fourCycleABFactor_eq_reindex_windowProduct]
  rw [← reindex_embedLocalOperator_three_eq_leftOverlappingLift]
  rw [embedLocalOperator_mul]
  rw [PhysicalSectorFactorization.embedLocalOperator_two_zero_nested,
    PhysicalSectorFactorization.embedLocalOperator_two_one_nested]
  rfl

/-- In the four-cycle tripartition, the global bonds at sites 1 and 2 are
the natural lift of the (B C) factor. -/
private theorem reindex_bondAt_one_mul_two_eq_rightOverlappingLift
    (data : GSNNCHData d 4) (x : Fin data.sectorCount) :
    Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm
        (data.bondAt x 1 * data.bondAt x 2) =
      Matrix.rightOverlappingLift (data.fourCycleBCFactor x) := by
  rw [fourCycleBCFactor_eq_reindex_windowProduct]
  rw [← reindex_embedLocalOperator_three_eq_rightOverlappingLift]
  rw [embedLocalOperator_mul]
  rw [PhysicalSectorFactorization.embedLocalOperator_two_zero_nested,
    PhysicalSectorFactorization.embedLocalOperator_two_one_nested]
  rfl

/-- Regrouping the weighted (3,0),(0,1) bond sum gives the natural lift of
the (A B) operator. -/
private theorem reindex_globalABOperator_eq_leftOverlappingLift
    (data : GSNNCHData d 4) (c : ℝ) :
    Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm (data.globalABOperator c) =
      Matrix.leftOverlappingLift (data.fourCycleABOperator c) := by
  classical
  rw [globalABOperator, fourCycleABOperator]
  change (Matrix.reindexLinearEquiv ℂ ℂ
      (fourCycleOverlappingEquiv d).symm
      (fourCycleOverlappingEquiv d).symm)
        ((c : ℂ) • ∑ x : Fin data.sectorCount,
          (data.multiplicity x : ℂ) •
            (data.bondAt x 3 * data.bondAt x 0)) =
      Matrix.leftOverlappingLift
        ((c : ℂ) • ∑ x : Fin data.sectorCount,
          (data.multiplicity x : ℂ) • data.fourCycleABFactor x)
  rw [map_smul, Matrix.leftOverlappingLift_smul, map_sum,
    Matrix.leftOverlappingLift_sum]
  apply congrArg (fun M ↦ (c : ℂ) • M)
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_smul, Matrix.leftOverlappingLift_smul]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [data.reindex_bondAt_three_mul_zero_eq_leftOverlappingLift]

/-- Regrouping the (1,2),(2,3) bond sum gives the natural lift of the
(B C) operator. -/
private theorem reindex_globalBCOperator_eq_rightOverlappingLift
    (data : GSNNCHData d 4) :
    Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm data.globalBCOperator =
      Matrix.rightOverlappingLift data.fourCycleBCOperator := by
  classical
  rw [globalBCOperator, fourCycleBCOperator]
  change (Matrix.reindexLinearEquiv ℂ ℂ
      (fourCycleOverlappingEquiv d).symm
      (fourCycleOverlappingEquiv d).symm)
        (∑ x : Fin data.sectorCount,
          data.bondAt x 1 * data.bondAt x 2) =
      Matrix.rightOverlappingLift
        (∑ x : Fin data.sectorCount, data.fourCycleBCFactor x)
  rw [map_sum, Matrix.rightOverlappingLift_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact data.reindex_bondAt_one_mul_two_eq_rightOverlappingLift x

/-- The weighted four-site (A B) bond-pair sum is positive semidefinite for
a nonnegative normalization constant. -/
private theorem globalABOperator_posSemidef (data : GSNNCHData d 4) {c : ℝ}
    (hc : 0 ≤ c) : (data.globalABOperator c).PosSemidef := by
  classical
  unfold globalABOperator
  apply (Matrix.posSemidef_sum Finset.univ fun x _ ↦
    ((data.bondAt_posSemidef x 3).mul_of_commute
      (data.bondAt_posSemidef x 0) (data.bondAt_comm x 3 0)).smul
      (by exact_mod_cast Nat.zero_le (data.multiplicity x))).smul
  exact_mod_cast hc

/-- The four-site (B C) bond-pair sum is positive semidefinite. -/
private theorem globalBCOperator_posSemidef (data : GSNNCHData d 4) :
    data.globalBCOperator.PosSemidef := by
  classical
  unfold globalBCOperator
  refine Matrix.posSemidef_sum Finset.univ fun x _ ↦ ?_
  exact (data.bondAt_posSemidef x 1).mul_of_commute
    (data.bondAt_posSemidef x 2) (data.bondAt_comm x 1 2)

/-- Multiplying one sector's (A B) adjacent-bond product by the full (B C)
sum selects that sector and gives its periodic product. -/
private theorem abBondProduct_mul_globalBCOperator
    (data : GSNNCHData d 4) (x : Fin data.sectorCount) :
    (data.bondAt x 3 * data.bondAt x 0) * data.globalBCOperator =
      data.sectorProduct x := by
  classical
  rw [globalBCOperator, Matrix.mul_sum, Finset.sum_eq_single x]
  · exact data.complementaryAdjacentBondProducts_mul_eq_sectorProduct x
  · intro y hy hyx
    exact data.complementaryAdjacentBondProducts_mul_eq_zero (Ne.symm hyx)
  · simp

/-- The two positive complementary adjacent-bond sums multiply to the
normalized sector sum realized by the GSNNCH data.

Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850. -/
private theorem globalABOperator_mul_globalBCOperator
    (data : GSNNCHData d 4) {c : ℝ} {rho : ChainOperator d 4}
    (hreal : rho = (c : ℂ) • data.unnormalizedState) :
    data.globalABOperator c * data.globalBCOperator = rho := by
  classical
  rw [globalABOperator, Matrix.smul_mul, Finset.sum_mul]
  simp_rw [Matrix.smul_mul, data.abBondProduct_mul_globalBCOperator]
  exact hreal.symm

end GSNNCHData

/-- Regrouping a positive four-site operator as (A={0}), (B={1,3}),
(C={2}) preserves positivity. -/
theorem fourCycleTripartiteState_posSemidef {rho : ChainOperator d 4}
    (hrho : rho.PosSemidef) : (fourCycleTripartiteState rho).PosSemidef := by
  simpa only [fourCycleTripartiteState, Matrix.reindex_apply,
    Equiv.symm_symm] using
    hrho.submatrix (fourCycleTripartiteEquiv d)

/-- Regrouping a four-site operator as (A={0}), (B={1,3}), (C={2})
preserves its trace. -/
private theorem fourCycleTripartiteState_trace {rho : ChainOperator d 4} :
    (fourCycleTripartiteState rho).trace = rho.trace := by
  rw [fourCycleTripartiteState, Matrix.trace_reindex]

/-- A four-site GSNNCH state has a quantum Markov decomposition for the
tripartition (A={0}), (B={1,3}), (C={2}).

Derived from arXiv:1606.00608, Definition 4.8, lines 829--850, by applying
Beigi's spatial decomposition and the Hayden--Jozsa--Petz--Winter Markov
structure theorem. CPSV16 does not state this four-cycle consequence as a
separate lemma. -/
theorem nonempty_quantumMarkovDecomposition_fourCycle_of_isGSNNCHAt
    {rho : ChainOperator d 4} (hrho : IsGSNNCHAt rho) :
    Nonempty (Entropy.QuantumMarkovDecomposition
      (fourCycleTripartiteState rho)) := by
  rcases hrho with ⟨hrhoPos, hrhoTrace, data, c, hc, hreal⟩
  have hLpos := data.globalABOperator_posSemidef hc.le
  have hRpos := data.globalBCOperator_posSemidef
  have hGlobalFactor := data.globalABOperator_mul_globalBCOperator hreal
  have hGlobalComm :
      data.globalABOperator c * data.globalBCOperator =
        data.globalBCOperator * data.globalABOperator c := by
    have hLRherm :
        (data.globalABOperator c * data.globalBCOperator).IsHermitian := by
      rw [hGlobalFactor]
      exact hrhoPos.isHermitian
    calc
      data.globalABOperator c * data.globalBCOperator =
          (data.globalABOperator c * data.globalBCOperator)ᴴ := hLRherm.eq.symm
      _ = data.globalBCOperatorᴴ * (data.globalABOperator c)ᴴ :=
        Matrix.conjTranspose_mul _ _
      _ = data.globalBCOperator * data.globalABOperator c := by
        rw [hRpos.isHermitian.eq, hLpos.isHermitian.eq]
  have hConfig : Nonempty (Fin 4 → Fin d) :=
    Matrix.nonempty_of_trace_eq_one rho hrhoTrace
  let z : Fin d := hConfig.some 0
  have hLliftPos :
      (Matrix.leftOverlappingLift (c := Fin d)
        (data.fourCycleABOperator c)).PosSemidef := by
    rw [← data.reindex_globalABOperator_eq_leftOverlappingLift]
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      hLpos.submatrix (fourCycleOverlappingEquiv d)
  have hRliftPos :
      (Matrix.rightOverlappingLift (a := Fin d)
        data.fourCycleBCOperator).PosSemidef := by
    rw [← data.reindex_globalBCOperator_eq_rightOverlappingLift]
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      hRpos.submatrix (fourCycleOverlappingEquiv d)
  have hXpos : (data.fourCycleABOperator c).PosSemidef :=
    Matrix.posSemidef_of_leftOverlappingLift_posSemidef
      (data.fourCycleABOperator c) z hLliftPos
  have hYpos : data.fourCycleBCOperator.PosSemidef :=
    Matrix.posSemidef_of_rightOverlappingLift_posSemidef
      data.fourCycleBCOperator z hRliftPos
  have hComm :
      Matrix.leftOverlappingLift (c := Fin d) (data.fourCycleABOperator c) *
          Matrix.rightOverlappingLift (a := Fin d) data.fourCycleBCOperator =
        Matrix.rightOverlappingLift (a := Fin d) data.fourCycleBCOperator *
          Matrix.leftOverlappingLift (c := Fin d)
            (data.fourCycleABOperator c) := by
    have h := congrArg
      (Matrix.reindex (fourCycleOverlappingEquiv d).symm
        (fourCycleOverlappingEquiv d).symm) hGlobalComm
    change (Matrix.reindexAlgEquiv ℂ ℂ
        (fourCycleOverlappingEquiv d).symm)
          (data.globalABOperator c * data.globalBCOperator) =
      (Matrix.reindexAlgEquiv ℂ ℂ
        (fourCycleOverlappingEquiv d).symm)
          (data.globalBCOperator * data.globalABOperator c) at h
    rw [map_mul, map_mul] at h
    simp only [Matrix.coe_reindexAlgEquiv] at h
    rw [data.reindex_globalABOperator_eq_leftOverlappingLift,
      data.reindex_globalBCOperator_eq_rightOverlappingLift] at h
    exact h
  have hReindexedFactor :
      Matrix.reindex (fourCycleOverlappingEquiv d).symm
          (fourCycleOverlappingEquiv d).symm rho =
        Matrix.leftOverlappingLift (c := Fin d) (data.fourCycleABOperator c) *
          Matrix.rightOverlappingLift (a := Fin d) data.fourCycleBCOperator := by
    calc
      Matrix.reindex (fourCycleOverlappingEquiv d).symm
          (fourCycleOverlappingEquiv d).symm rho =
        Matrix.reindex (fourCycleOverlappingEquiv d).symm
          (fourCycleOverlappingEquiv d).symm
          (data.globalABOperator c * data.globalBCOperator) :=
            congrArg
              (Matrix.reindex (fourCycleOverlappingEquiv d).symm
                (fourCycleOverlappingEquiv d).symm) hGlobalFactor.symm
      _ = Matrix.reindex (fourCycleOverlappingEquiv d).symm
            (fourCycleOverlappingEquiv d).symm (data.globalABOperator c) *
          Matrix.reindex (fourCycleOverlappingEquiv d).symm
            (fourCycleOverlappingEquiv d).symm data.globalBCOperator := by
          change (Matrix.reindexAlgEquiv ℂ ℂ
            (fourCycleOverlappingEquiv d).symm)
              (data.globalABOperator c * data.globalBCOperator) = _
          rw [map_mul]
          simp only [Matrix.coe_reindexAlgEquiv]
      _ = Matrix.leftOverlappingLift (c := Fin d) (data.fourCycleABOperator c) *
          Matrix.rightOverlappingLift (a := Fin d) data.fourCycleBCOperator := by
        rw [data.reindex_globalABOperator_eq_leftOverlappingLift,
          data.reindex_globalBCOperator_eq_rightOverlappingLift]
  apply Matrix.exists_quantumMarkovDecomposition_of_positive_overlapping_product
    (fourCycleTripartiteState rho)
    (by rw [fourCycleTripartiteState_trace, hrhoTrace])
    (data.fourCycleABOperator c) data.fourCycleBCOperator hXpos hYpos hComm
  change ((Matrix.reindex (fourCycleTripartiteEquiv d).symm
      (fourCycleTripartiteEquiv d).symm).trans
      (Matrix.reindex (Equiv.prodAssoc (Fin d) (Fin (d * d)) (Fin d)).symm
        (Equiv.prodAssoc (Fin d) (Fin (d * d)) (Fin d)).symm)) rho = _
  rw [Matrix.reindex_trans]
  have hCoord :
      (fourCycleTripartiteEquiv d).symm.trans
          (Equiv.prodAssoc (Fin d) (Fin (d * d)) (Fin d)).symm =
        (fourCycleOverlappingEquiv d).symm := by
    rw [fourCycleOverlappingEquiv, Equiv.symm_trans]
  rw [hCoord]
  exact hReindexedFactor

/-- A four-site GSNNCH state saturates strong subadditivity after grouping
(A={0}), (B={1,3}), and (C={2}).

Derived from arXiv:1606.00608, Definition 4.8, lines 829--850, through the
four-cycle Beigi/Hayden--Jozsa--Petz--Winter decomposition above. CPSV16
does not state this implication as a separate lemma. -/
theorem isSSAEquality_fourCycle_of_isGSNNCHAt
    {rho : ChainOperator d 4} (hrho : IsGSNNCHAt rho) :
    IsSSAEquality (fourCycleTripartiteState rho)
      (fourCycleTripartiteState_posSemidef hrho.1).isHermitian := by
  apply Entropy.isSSAEquality_of_quantumMarkovDecomposition
    (fourCycleTripartiteState rho)
    ⟨fourCycleTripartiteState_posSemidef hrho.1, ?_⟩
  · exact nonempty_quantumMarkovDecomposition_fourCycle_of_isGSNNCHAt hrho
  · rw [fourCycleTripartiteState_trace, hrho.2.1]

end MPOTensor

namespace MPOTensor.CPSVExample412Literal

/-- The basis regrouping used in the literal entropy calculation is exactly
the specialization of the general four-cycle regrouping to binary sites.

This identifies the coordinate boundary used for CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--938, with the one used for the four-site consequence
of Definition 4.8, lines 829--850. -/
private theorem fourCycleTripartiteEquiv_eq_generic :
    fourCycleTripartiteEquiv = MPOTensor.fourCycleTripartiteEquiv 2 := by
  apply Equiv.ext
  rintro ⟨a, b, c⟩
  funext i
  fin_cases i <;>
    simp [fourCycleTripartiteEquiv, MPOTensor.fourCycleTripartiteEquiv,
      fourCycleMiddleBits, MPOTensor.fourCycleMiddlePair]

/-- The tripartite state used in the literal entropy calculation is the
binary specialization of the general four-cycle regrouping.

This identifies the normalized state in CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--938, with the four-site coordinate boundary derived
from Definition 4.8, lines 829--850. -/
theorem fourCycleTripartiteState_eq_generic :
    fourCycleTripartiteState =
      MPOTensor.fourCycleTripartiteState (normalizedMPO M 4) := by
  ext x y
  simp only [fourCycleTripartiteState, MPOTensor.fourCycleTripartiteState,
    Matrix.reindex_apply, Equiv.symm_symm]
  rw [fourCycleTripartiteEquiv_eq_generic]

/-- The tensor in CPSV16 Example 4.12 is not GSNNCH.

The four-site specialization of Definition 4.8 would force equality in
strong subadditivity for (A={0}), (B={1,3}), (C={2}), whereas the
literal four-site entropy calculation is strict.

Source conclusion: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--938. -/
theorem M_not_isGSNNCH : ¬ IsGSNNCH M := by
  intro hGSNNCH
  have hSSA := MPOTensor.isSSAEquality_fourCycle_of_isGSNNCHAt
    (hGSNNCH 4 (by decide))
  apply fourCycleTripartiteState_not_isSSAEquality
  simpa only [IsSSAEquality, ← fourCycleTripartiteState_eq_generic] using hSSA

end MPOTensor.CPSVExample412Literal
