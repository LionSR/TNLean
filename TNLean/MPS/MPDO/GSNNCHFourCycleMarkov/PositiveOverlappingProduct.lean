/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.CommutingOverlappingDecomp
import QICLean.Algebra.PositiveSemidefiniteNormalization
import QICLean.Entropy.MarkovChain

/-!
# Quantum Markov structure from a positive commuting overlapping product

This file proves a project-derived criterion for a tripartite operator to have
a quantum Markov decomposition. The operator is assumed to factor into
positive semidefinite operators on the overlapping subsystems \(A B\) and
\(B C\), whose natural lifts commute. Beigi's spatial decomposition of the
middle subsystem and the Hayden--Jozsa--Petz--Winter direct-sum form then give
the quantum Markov decomposition.

## References

* S. Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1.
* Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246 (2004), 359--374,
  Theorem 6.
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
