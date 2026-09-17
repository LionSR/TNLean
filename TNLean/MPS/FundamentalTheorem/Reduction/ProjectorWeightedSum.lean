/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# Projector-weighted direct sums as multi-block compressions

A tensor whose one-site matrices are, after one reordering of the bond coordinates, the weighted
sums

`B^i = ∑_{s ∈ S} μ_s · (Π_s ⊗ C_s^i)`

over a family of mutually orthogonal rank-one idempotents `Π_s` of an inner bond space, is a
multi-block asymmetric compression onto the weighted blocks `μ_s · C_s`
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7). In a
basis of the inner bond adapted to the idempotents the one-site matrices are block *diagonal*,
so the remainder of the compression vanishes and the extension splits; the zero slots are the
tensor product of the complement of the idempotents with the block space.

This is the uniform mechanism behind every renormalization fixed point of the P6 work
(`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, "Cross-example notes"): the inner
bond carries a state `∑_b λ_b Π_b`, its `L`-fold periodic contraction contributes `∑_b λ_b^L`,
and the length-dependent structure constant `c^{(L)}` of the fixed point is the power sum of the
weights (`Notes/OpenProblemsTN/strategies/p6_round46_mechanism_and_positioning.tex`).

## Main definitions

* `MPSTensor.basisProj`: the rank-one idempotent of one vector of an adapted basis, the product
  of a column of the inverse gauge with the matching row of the gauge.
* `MPSTensor.projBlockEquiv`, `MPSTensor.projTau`: the labelling of the bond coordinates of the
  weighted direct sum by the graded block space.
* `MPSTensor.innerGauge`, `MPSTensor.projGauge`: the adapted basis of the inner bond, acting on
  the inner factor of the bond space alone.

## Main results

* `MPSTensor.basisProj_mul_basisProj_self`,
  `MPSTensor.basisProj_mul_basisProj_of_ne`: the idempotents of an adapted basis are mutually
  orthogonal idempotents.
* `MPSTensor.MultiBlockCompression.ofProjectorSum`: the compression datum of a
  projector-weighted direct sum.
* `MPSTensor.MultiBlockCompression.remainder_ofProjectorSum`: its remainder vanishes.
* `MPSTensor.MultiBlockCompression.mul_right_eq_right_mul`,
  `MPSTensor.MultiBlockCompression.left_mul_eq_mul_left`: the sitewise intertwining relations
  available whenever the remainder vanishes.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-! ### The rank-one idempotents of an adapted basis -/

section BasisProj

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The rank-one idempotent attached to the `j`-th vector of the basis given by a matrix `U`
with inverse `Uinv`: the product of the `j`-th column of `Uinv` with the `j`-th row of `U`. -/
def basisProj (U Uinv : Matrix (Fin m) (Fin m) R) (j : Fin m) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun x y => Uinv x j * U j y

@[simp] theorem basisProj_apply (U Uinv : Matrix (Fin m) (Fin m) R) (j x y : Fin m) :
    basisProj U Uinv j x y = Uinv x j * U j y := rfl

/-- The idempotent of a basis vector as a matrix product with a single matrix unit. -/
theorem basisProj_eq_mul (U Uinv : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    basisProj U Uinv j = Uinv * Matrix.single j j 1 * U := by
  ext x y
  rw [basisProj_apply, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.single_apply_same, mul_one]
    · intro b _ hb
      rw [Matrix.single_apply_of_row_ne (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro a _
    rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Rescaling the inverse gauge rescales the idempotents of the adapted basis. -/
theorem basisProj_smul (c : R) (U Uinv : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    basisProj U (c • Uinv) j = c • basisProj U Uinv j := by
  ext x y
  simp [mul_assoc]

/-- Conjugating the idempotent of a basis vector by the gauge returns the matrix unit at the
coordinate of that vector. -/
theorem mul_basisProj_mul {U Uinv : Matrix (Fin m) (Fin m) R} (hU : U * Uinv = 1) (j : Fin m) :
    U * basisProj U Uinv j * Uinv = Matrix.single j j 1 := by
  rw [basisProj_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The product of the idempotents of two basis vectors is the product of the matrix units of
those vectors, conjugated back. -/
private theorem basisProj_mul_basisProj_aux {U Uinv : Matrix (Fin m) (Fin m) R}
    (hU : U * Uinv = 1) (j k : Fin m) :
    basisProj U Uinv j * basisProj U Uinv k =
      Uinv * (Matrix.single j j (1 : R) * Matrix.single k k 1 * U) := by
  simp only [basisProj_eq_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uinv, hU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.single j j (1 : R))]

/-- **The idempotents of an adapted basis are idempotent.** -/
theorem basisProj_mul_basisProj_self {U Uinv : Matrix (Fin m) (Fin m) R} (hU : U * Uinv = 1)
    (j : Fin m) : basisProj U Uinv j * basisProj U Uinv j = basisProj U Uinv j := by
  rw [basisProj_mul_basisProj_aux hU, Matrix.single_mul_single_same, mul_one, basisProj_eq_mul,
    Matrix.mul_assoc]

/-- **The idempotents of two distinct basis vectors are orthogonal.** -/
theorem basisProj_mul_basisProj_of_ne {U Uinv : Matrix (Fin m) (Fin m) R} (hU : U * Uinv = 1)
    {j k : Fin m} (h : j ≠ k) : basisProj U Uinv j * basisProj U Uinv k = 0 := by
  have hz : Matrix.single j j (1 : R) * Matrix.single k k (1 : R) = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases eq_or_ne j c with hjc | hjc
    · have hcond : ¬(k = c ∧ k = b) := fun hh => h (hjc.trans hh.1.symm)
      simp [hcond]
    · have hcond : ¬(j = a ∧ j = c) := fun hh => hjc hh.2
      simp [hcond]
  rw [basisProj_mul_basisProj_aux hU, hz, Matrix.zero_mul, Matrix.mul_zero]

end BasisProj

/-- The entrywise coercion of an integer matrix commutes with the idempotents of an adapted
basis. -/
theorem complexOfInt_basisProj {m : ℕ} (A Ainv : Matrix (Fin m) (Fin m) ℤ) (j : Fin m) :
    complexOfInt (basisProj A Ainv j) = basisProj (complexOfInt A) (complexOfInt Ainv) j := by
  ext x y
  simp [basisProj]

/-! ### The graded coordinates of a projector-weighted direct sum -/

section Coordinates

variable {DC zz : ℕ} {ι : Type*}

/-- The graded coordinate space of a projector-weighted direct sum, with `zz * DC` zero slots,
is the product of the inner-bond labels with one block space. -/
def projBlockEquiv (S : Finset ι) (DC zz : ℕ) :
    BlockSpace (fun _ : ι => DC) S (zz * DC) ≃ ({s // s ∈ S} ⊕ Fin zz) × Fin DC :=
  (Equiv.sumSigmaDistrib fun b : BlockIndex S (zz * DC) =>
      Fin (slotSize (fun _ : ι => DC) b)).trans <|
    (Equiv.sumCongr (Equiv.sigmaEquivProd {s // s ∈ S} (Fin DC))
        (((Equiv.sigmaEquivProd (Fin (zz * DC)) (Fin 1)).trans
          (Equiv.prodUnique (Fin (zz * DC)) (Fin 1))).trans
            finProdFinEquiv.symm)).trans
      (Equiv.sumProdDistrib {s // s ∈ S} (Fin zz) (Fin DC)).symm

@[simp] theorem projBlockEquiv_inl (S : Finset ι) (s : {s // s ∈ S}) (p : Fin DC) :
    projBlockEquiv S DC zz ⟨Sum.inl s, p⟩ = (Sum.inl s, p) := rfl

@[simp] theorem projBlockEquiv_inr (S : Finset ι) (t : Fin (zz * DC))
    (p : Fin (slotSize (fun _ : ι => DC) (Sum.inr t : BlockIndex S (zz * DC)))) :
    projBlockEquiv S DC zz ⟨Sum.inr t, p⟩ =
      (Sum.inr (finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2) := rfl

/-- A graded coordinate sits in a target slot exactly when its inner-bond label does. -/
theorem projBlockEquiv_fst_eq_inl {S : Finset ι}
    {x : BlockSpace (fun _ : ι => DC) S (zz * DC)} {s : {s // s ∈ S}}
    (h : (projBlockEquiv S DC zz x).1 = Sum.inl s) : x.1 = Sum.inl s := by
  obtain ⟨b, p⟩ := x
  match b with
  | Sum.inl s' =>
      rw [projBlockEquiv_inl] at h
      exact congrArg Sum.inl (Sum.inl_injective h)
  | Sum.inr t => rw [projBlockEquiv_inr] at h; exact absurd h (by simp)

end Coordinates

/-! ### The gauge of a projector-weighted direct sum -/

section Gauge

variable {m DC DB zz : ℕ} {ι : Type*} [DecidableEq ι]

/-- The change of bond coordinates that acts by `U` on the inner factor of the bond space and
trivially on the block factor. -/
def innerGauge (σ : Fin m × Fin DC ≃ Fin DB) (U : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin DB) (Fin DB) ℂ :=
  (U ⊗ₖ (1 : Matrix (Fin DC) (Fin DC) ℂ)).submatrix σ.symm σ.symm

theorem innerGauge_mul_innerGauge (σ : Fin m × Fin DC ≃ Fin DB)
    {U Uinv : Matrix (Fin m) (Fin m) ℂ} (hU : U * Uinv = 1) :
    innerGauge σ U * innerGauge σ Uinv = 1 := by
  rw [innerGauge, innerGauge, Matrix.submatrix_mul_equiv _ _ _ σ.symm _,
    ← Matrix.mul_kronecker_mul, hU, Matrix.mul_one, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- The labelling of the bond coordinates of a projector-weighted direct sum by the graded block
space: the inner-bond label picks the slot, the block label the coordinate inside it. -/
def projTau (S : Finset ι) (ρ : {s // s ∈ S} ⊕ Fin zz ≃ Fin m)
    (σ : Fin m × Fin DC ≃ Fin DB) :
    BlockSpace (fun _ : ι => DC) S (zz * DC) ≃ Fin DB :=
  (projBlockEquiv S DC zz).trans ((ρ.prodCongr (Equiv.refl (Fin DC))).trans σ)

omit [DecidableEq ι] in
theorem projTau_symm_apply (S : Finset ι) (ρ : {s // s ∈ S} ⊕ Fin zz ≃ Fin m)
    (σ : Fin m × Fin DC ≃ Fin DB) (x : BlockSpace (fun _ : ι => DC) S (zz * DC)) :
    σ.symm (projTau S ρ σ x) =
      (ρ (projBlockEquiv S DC zz x).1, (projBlockEquiv S DC zz x).2) := by
  simp [projTau, Prod.map]

/-- The gauge of a projector-weighted direct sum. -/
noncomputable def projGauge (S : Finset ι) (ρ : {s // s ∈ S} ⊕ Fin zz ≃ Fin m)
    (σ : Fin m × Fin DC ≃ Fin DB) {U Uinv : Matrix (Fin m) (Fin m) ℂ} (hU : U * Uinv = 1)
    (hU' : Uinv * U = 1) :
    (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace (fun _ : ι => DC) S (zz * DC) → ℂ) :=
  gaugeOfMatrix (projTau S ρ σ) (innerGauge σ U) (innerGauge σ Uinv)
    (innerGauge_mul_innerGauge σ hU)
    (innerGauge_mul_innerGauge σ hU')

end Gauge

/-! ### The compression datum -/

section ProjectorSum

variable {d m DC DB zz : ℕ} {ι : Type*} [DecidableEq ι] {S : Finset ι} {μ : ι → ℂ}
  {C : ι → MPSTensor d DC} {B : MPSTensor d DB} {j : ι → Fin m}
  {U Uinv : Matrix (Fin m) (Fin m) ℂ}

/-- The one-site matrices of a projector-weighted direct sum, in the block coordinates: the
weighted blocks sit on the diagonal of the inner-bond label and everything else vanishes. -/
theorem conjMatrix_projGauge (hU : U * Uinv = 1) (hU' : Uinv * U = 1)
    (ρ : {s // s ∈ S} ⊕ Fin zz ≃ Fin m) (σ : Fin m × Fin DC ≃ Fin DB)
    (hB : ∀ i, B i =
      (∑ s ∈ S, μ s • (basisProj U Uinv (j s) ⊗ₖ C s i)).submatrix σ.symm σ.symm)
    (i : Fin d) (x y : BlockSpace (fun _ : ι => DC) S (zz * DC)) :
    conjMatrix (projGauge S ρ σ hU hU') (B i) x y =
      ∑ s ∈ S, μ s * (if j s = ρ (projBlockEquiv S DC zz x).1 ∧
          j s = ρ (projBlockEquiv S DC zz y).1 then (1 : ℂ) else 0) *
        C s i (projBlockEquiv S DC zz x).2 (projBlockEquiv S DC zz y).2 := by
  have hkey : innerGauge σ U * B i * innerGauge σ Uinv =
      (∑ s ∈ S, μ s • (Matrix.single (j s) (j s) (1 : ℂ) ⊗ₖ C s i)).submatrix
        σ.symm σ.symm := by
    rw [hB i, innerGauge, innerGauge, Matrix.submatrix_mul_equiv _ _ _ σ.symm _,
      Matrix.submatrix_mul_equiv _ _ _ σ.symm _]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, mul_basisProj_mul hU]
  rw [projGauge, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hkey, Matrix.submatrix_apply,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, projTau_symm_apply, projTau_symm_apply,
    Matrix.kroneckerMap_apply, Matrix.single_apply, mul_assoc]

variable (hU : U * Uinv = 1) (hU' : Uinv * U = 1) (ρ : {s // s ∈ S} ⊕ Fin zz ≃ Fin m)
  (σ : Fin m × Fin DC ≃ Fin DB) (hj : ∀ s : {s // s ∈ S}, ρ (Sum.inl s) = j s.1)

include hU hU' hj in
/-- Off the diagonal of the inner-bond label the conjugated one-site matrices vanish. -/
private theorem conjMatrix_projGauge_eq_zero
    (hB : ∀ i, B i =
      (∑ s ∈ S, μ s • (basisProj U Uinv (j s) ⊗ₖ C s i)).submatrix σ.symm σ.symm)
    (i : Fin d) (x y : BlockSpace (fun _ : ι => DC) S (zz * DC)) (hxy : x.1 ≠ y.1) :
    conjMatrix (projGauge S ρ σ hU hU') (B i) x y = 0 := by
  rw [conjMatrix_projGauge hU hU' ρ σ hB i x y]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hcond : ¬(j s = ρ (projBlockEquiv S DC zz x).1 ∧
      j s = ρ (projBlockEquiv S DC zz y).1) := by
    rintro ⟨hx, hy⟩
    rw [← hj ⟨s, hs⟩] at hx hy
    exact hxy ((projBlockEquiv_fst_eq_inl (ρ.injective hx).symm).trans
      (projBlockEquiv_fst_eq_inl (ρ.injective hy).symm).symm)
  simp [hcond]

include hU hU' hj in
/-- **Projector-weighted direct sums are multi-block compressions.** A tensor whose one-site
matrices are, in suitable bond coordinates, the weighted sums `∑_s μ_s (Π_s ⊗ C_s^i)` over the
rank-one idempotents of an adapted basis of an inner bond factor is compressed onto the weighted
blocks `μ_s · C_s`, with `zz * DC` zero slots, where `zz` is the number of basis vectors of the
inner bond outside the family (P5 note, Theorem 7.7(i)–(iii)). -/
noncomputable def MultiBlockCompression.ofProjectorSum
    (hB : ∀ i, B i =
      (∑ s ∈ S, μ s • (basisProj U Uinv (j s) ⊗ₖ C s i)).submatrix σ.symm σ.symm) :
    MultiBlockCompression (D := fun _ : ι => DC) B S fun s => μ s • C s where
  z := zz * DC
  ord := Fintype.equivFinOfCardEq (by simp)
  gauge := projGauge S ρ σ hU hU'
  triangular i x y hxy :=
    conjMatrix_projGauge_eq_zero hU hU' ρ σ hj hB i x y fun h => absurd hxy (by simp [h])
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_projGauge hU hU' ρ σ hB i]
    simp only [projBlockEquiv_inl]
    rw [Finset.sum_eq_single s.1]
    · simp [hj s]
    · intro b hb hbs
      have hcond : ¬(j b = ρ (Sum.inl s)) := fun hx =>
        hbs (congrArg Subtype.val (Sum.inl_injective (ρ.injective ((hj ⟨b, hb⟩).trans hx))))
      simp [hcond]
    · intro h
      exact absurd s.2 h
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_projGauge hU hU' ρ σ hB i]
    simp only [projBlockEquiv_inr, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hcond : ∀ u : Fin zz, ¬(j s = ρ (Sum.inr u)) := by
      intro u hx
      rw [← hj ⟨s, hs⟩] at hx
      exact absurd (ρ.injective hx) (by simp)
    simp [hcond]

include hU hU' hj in
/-- **The remainder of a projector-weighted direct sum vanishes** (P5 note, Theorem 7.7(vi)): in
the adapted basis the one-site matrices are block diagonal, so the extension splits. -/
theorem MultiBlockCompression.remainder_ofProjectorSum
    (hB : ∀ i, B i =
      (∑ s ∈ S, μ s • (basisProj U Uinv (j s) ⊗ₖ C s i)).submatrix σ.symm σ.symm) :
    (MultiBlockCompression.ofProjectorSum (zz := zz) hU hU' ρ σ hj hB).remainder = 0 := by
  refine funext fun i => conjMatrix_injective
    (MultiBlockCompression.ofProjectorSum (zz := zz) hU hU' ρ σ hj hB).gauge ?_
  rw [MultiBlockCompression.conjMatrix_remainder _ i, Pi.zero_apply, conjMatrix_zero,
    sub_eq_zero]
  ext x y
  by_cases hxy : x.1 = y.1
  · obtain ⟨bx, px⟩ := x
    obtain ⟨by', py⟩ := y
    cases hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy]
    exact conjMatrix_projGauge_eq_zero hU hU' ρ σ hj hB i _ _ hxy

end ProjectorSum

/-! ### Sitewise intertwiners of a split compression -/

namespace MultiBlockCompression

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {B : MPSTensor d DB}
  {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} (P : MultiBlockCompression B S C)

include P in
/-- A compression with vanishing remainder reconstructs `B` from its blocks (P5 note,
`eq:p5-main-reconstruction` with `R = 0`). -/
theorem eq_sum_right_mul_mul_left (hP : P.remainder = 0) (i : Fin d) :
    B i = ∑ s : {s // s ∈ S}, P.right s * C s.1 i * P.left s := by
  have h : B i - ∑ s : {s // s ∈ S}, P.right s * C s.1 i * P.left s = 0 := congrFun hP i
  exact sub_eq_zero.mp h

include P in
/-- **The sitewise right intertwiner of a split compression**: `B^i V_s = V_s C_s^i`. -/
theorem mul_right_eq_right_mul (hP : P.remainder = 0) (i : Fin d) (t : {s // s ∈ S}) :
    B i * P.right t = P.right t * C t.1 i := by
  rw [P.eq_sum_right_mul_mul_left hP i, Matrix.sum_mul, Finset.sum_eq_single t]
  · rw [Matrix.mul_assoc, P.left_mul_right_self, Matrix.mul_one]
  · intro s _ hst
    rw [Matrix.mul_assoc, P.left_mul_right_of_ne hst, Matrix.mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

include P in
/-- **The sitewise left intertwiner of a split compression**: `W_s B^i = C_s^i W_s`. -/
theorem left_mul_eq_mul_left (hP : P.remainder = 0) (i : Fin d) (t : {s // s ∈ S}) :
    P.left t * B i = C t.1 i * P.left t := by
  rw [P.eq_sum_right_mul_mul_left hP i, Matrix.mul_sum, Finset.sum_eq_single t]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.left_mul_right_self, Matrix.one_mul]
  · intro s _ hst
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.left_mul_right_of_ne (Ne.symm hst),
      Matrix.zero_mul, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ t) h

end MultiBlockCompression

end MPSTensor
