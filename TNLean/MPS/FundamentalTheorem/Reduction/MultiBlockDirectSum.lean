/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Algebra.BigOperators.Fin
import TNLean.MPS.FundamentalTheorem.Reduction.AssemblyLemmas
import TNLean.MPS.FundamentalTheorem.Reduction.ExplicitGauge

/-!
# The direct sum of one-slot compression data

**Source.** None: this is infrastructure of this development for the worked examples of the
multi-block asymmetric compression theorem, and no paper states it.

**Formalized here.** Let `A` be a tensor whose letters are, after a common relabelling `e` of
the bond coordinates, block diagonal with blocks `B k`, `k ∈ κ`, and suppose that each block
`B k` carries a one-slot compression datum onto a target `C k`. The direct sum of the gauges
of the blocks is a gauge of `A`, and the zero slots of the blocks are the zero slots of `A`.
This assembles a multi-block compression datum of `A` onto the family `C` with `∑ₖ zₖ` zero
slots.

The remainder of the assembled datum is the block-diagonal sum of the remainders of the blocks,
relabelled along `e`. Consequently a word in the remainder of `A` vanishes as soon as the same
word vanishes in the remainder of every block: the nilpotency order of the assembled remainder
is the largest of the nilpotency orders of the blocks, instead of the generic bound
`|κ| + ∑ₖ zₖ` of clause (vi) of the compression theorem.

## Main definitions

* `MPSTensor.MultiBlockCompression.directSum`: the assembled compression datum.
* `MPSTensor.MultiBlockCompression.ofTargetEq`: a compression datum read against a family of
  targets equal to the given one, such as a weight-one target `1 • C`.

## Main results

* `MPSTensor.MultiBlockCompression.conjMatrix_directSum`: the letters of `A` in the assembled
  block coordinates are the block-diagonal sum of the letters of the blocks in their own block
  coordinates.
* `MPSTensor.MultiBlockCompression.remainder_directSum`,
  `MPSTensor.MultiBlockCompression.evalWord_remainder_directSum`: the remainder of the assembled
  datum, and its words, are block diagonal with the remainders of the blocks on the diagonal.
* `MPSTensor.MultiBlockCompression.evalWord_remainder_directSum_eq_zero`: a word vanishing in
  every block remainder vanishes in the assembled remainder.

## Provenance

The compression theorem is Theorem 7.7 (`thm:p5-asymmetric-compression`, §7.5) of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, lines 495–569.
-/

open scoped Matrix

namespace Matrix

variable {ι : Type*} [DecidableEq ι] {m : ι → Type*} {α : Type*} [Zero α]

/-- The block-diagonal part of a matrix on a sigma type keeps the entries whose row and column
lie in the same block. -/
theorem blockDiagonal'_blockDiag'_apply (M : Matrix (Σ i, m i) (Σ i, m i) α)
    (x y : Σ i, m i) :
    blockDiagonal' M.blockDiag' x y = if x.1 = y.1 then M x y else 0 := by
  obtain ⟨i, p⟩ := x
  obtain ⟨j, q⟩ := y
  by_cases h : i = j
  · subst h
    simp [blockDiag'_apply]
  · simp [blockDiagonal'_apply_ne _ _ _ h, h]

end Matrix

namespace MPSTensor

namespace MultiBlockCompression

section TargetEq

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {B : MPSTensor d DB}
  {S : Finset ι} {C C' : ∀ s, MPSTensor d (D s)}

/-- A compression datum onto a family `C` is a compression datum onto every family equal to it
letter by letter, with the same gauge and the same zero slots. -/
noncomputable def ofTargetEq (P : MultiBlockCompression B S C) (h : ∀ s i, C s i = C' s i) :
    MultiBlockCompression B S C' where
  z := P.z
  ord := P.ord
  gauge := P.gauge
  triangular := P.triangular
  matched i s := (P.matched i s).trans (h s.1 i)
  unmatched := P.unmatched

@[simp] theorem ofTargetEq_z (P : MultiBlockCompression B S C) (h : ∀ s i, C s i = C' s i) :
    (P.ofTargetEq h).z = P.z := rfl

/-- Changing the target family to an equal one does not change the remainder. -/
@[simp] theorem remainder_ofTargetEq (P : MultiBlockCompression B S C)
    (h : ∀ s i, C s i = C' s i) : (P.ofTargetEq h).remainder = P.remainder := by
  funext i
  simp only [remainder, h]
  rfl

end TargetEq

variable {d DB : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] {n Dt : κ → ℕ}
  {B : ∀ k, MPSTensor d (n k)} {C : ∀ k, MPSTensor d (Dt k)}
  (P : ∀ k, MultiBlockCompression (B k) oneSlot (fun _ : Unit => C k))

/-! ### The labels of the assembled blocks -/

/-- The labelling of the zero slots of the assembled datum by the zero slots of the blocks. -/
noncomputable def directSumZeroEquiv : Fin (∑ k, (P k).z) ≃ Σ k, Fin (P k).z :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])).symm

/-- The labelling of the blocks of the assembled datum by the blocks of the summands: the slot
`k` is the target slot of the block `k`, and every zero slot is a zero slot of one block. -/
noncomputable def directSumIndexEquiv :
    BlockIndex (Finset.univ : Finset κ) (∑ k, (P k).z) ≃ Σ k, BlockIndex oneSlot (P k).z where
  toFun
    | Sum.inl s => ⟨s.1, Sum.inl oneSlotMem⟩
    | Sum.inr t => ⟨(directSumZeroEquiv P t).1, Sum.inr (directSumZeroEquiv P t).2⟩
  invFun
    | ⟨k, Sum.inl _⟩ => Sum.inl ⟨k, Finset.mem_univ k⟩
    | ⟨k, Sum.inr t⟩ => Sum.inr ((directSumZeroEquiv P).symm ⟨k, t⟩)
  left_inv b := by
    rcases b with s | t
    · rfl
    · simp
  right_inv x := by
    obtain ⟨k, u | t⟩ := x
    · obtain rfl : u = oneSlotMem := eq_oneSlotMem u
      rfl
    · have key : ∀ q : Σ k, Fin (P k).z, q = ⟨k, t⟩ →
          (⟨q.1, Sum.inr q.2⟩ : Σ k, BlockIndex oneSlot (P k).z) = ⟨k, Sum.inr t⟩ := by
        rintro _ rfl
        rfl
      exact key _ (Equiv.apply_symm_apply _ _)

/-- The labelling of the coordinates of the assembled datum by the coordinates of the blocks. -/
noncomputable def directSumCoordEquiv :
    BlockSpace Dt (Finset.univ : Finset κ) (∑ k, (P k).z) ≃
      Σ k, BlockSpace (fun _ : Unit => Dt k) oneSlot (P k).z where
  toFun
    | ⟨Sum.inl s, p⟩ => ⟨s.1, ⟨Sum.inl oneSlotMem, p⟩⟩
    | ⟨Sum.inr t, p⟩ => ⟨(directSumZeroEquiv P t).1, ⟨Sum.inr (directSumZeroEquiv P t).2, p⟩⟩
  invFun
    | ⟨k, ⟨Sum.inl _, p⟩⟩ => ⟨Sum.inl ⟨k, Finset.mem_univ k⟩, p⟩
    | ⟨k, ⟨Sum.inr t, p⟩⟩ => ⟨Sum.inr ((directSumZeroEquiv P).symm ⟨k, t⟩), p⟩
  left_inv x := by
    obtain ⟨s | t, p⟩ := x
    · rfl
    · simp
  right_inv x := by
    obtain ⟨k, ⟨u | t, p⟩⟩ := x
    · obtain rfl : u = oneSlotMem := eq_oneSlotMem u
      rfl
    · have key : ∀ q : Σ k, Fin (P k).z, q = ⟨k, t⟩ →
          (⟨q.1, ⟨Sum.inr q.2, p⟩⟩ : Σ k, BlockSpace (fun _ : Unit => Dt k) oneSlot (P k).z) =
            ⟨k, ⟨Sum.inr t, p⟩⟩ := by
        rintro _ rfl
        rfl
      exact key _ (Equiv.apply_symm_apply _ _)

omit [DecidableEq κ] in
theorem directSumCoordEquiv_inl (s : {s // s ∈ (Finset.univ : Finset κ)}) (p : Fin (Dt s.1)) :
    directSumCoordEquiv P ⟨Sum.inl s, p⟩ = ⟨s.1, ⟨Sum.inl oneSlotMem, p⟩⟩ := rfl

omit [DecidableEq κ] in
theorem directSumCoordEquiv_inr (t : Fin (∑ k, (P k).z)) (p : Fin 1) :
    directSumCoordEquiv (Dt := Dt) P ⟨Sum.inr t, p⟩ =
      ⟨(directSumZeroEquiv P t).1, ⟨Sum.inr (directSumZeroEquiv P t).2, p⟩⟩ := rfl

omit [DecidableEq κ] in
/-- The block of a coordinate of the assembled datum, read in the blocks of the summands, is
the block of its coordinate in the summands. -/
theorem directSumIndexEquiv_fst (x : BlockSpace Dt (Finset.univ : Finset κ) (∑ k, (P k).z)) :
    directSumIndexEquiv P x.1 =
      ⟨(directSumCoordEquiv P x).1, (directSumCoordEquiv P x).2.1⟩ := by
  obtain ⟨s | t, p⟩ := x <;> rfl

omit [DecidableEq κ] in
/-- A linear ordering of a sigma type of finite ranges, increasing on every fibre. -/
noncomputable def sigmaFinOrd (N : κ → ℕ) : (Σ k, Fin (N k)) ≃ Fin (∑ k, N k) :=
  (Equiv.sigmaCongrLeft (Fintype.equivFin κ).symm).symm.trans
    (finSigmaFinEquiv.trans (finCongr (Fintype.sum_equiv (Fintype.equivFin κ).symm _ _
      fun _ => rfl)))

omit [DecidableEq κ] in
/-- The ordering `sigmaFinOrd` is increasing on every fibre. -/
theorem sigmaFinOrd_lt_iff (N : κ → ℕ) (k : κ) (a b : Fin (N k)) :
    sigmaFinOrd N ⟨k, a⟩ < sigmaFinOrd N ⟨k, b⟩ ↔ a < b := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ, ∀ c : Fin (N k), ((sigmaFinOrd N ⟨k, c⟩ : Fin _) : ℕ) = F + c := by
    obtain ⟨i, rfl⟩ := (Fintype.equivFin κ).symm.surjective k
    refine ⟨∑ j : Fin i, N ((Fintype.equivFin κ).symm (Fin.castLE i.2.le j)), fun c => ?_⟩
    have h : (Equiv.sigmaCongrLeft (β := fun k => Fin (N k)) (Fintype.equivFin κ).symm).symm
        ⟨(Fintype.equivFin κ).symm i, c⟩ =
          (⟨i, c⟩ : Σ j : Fin (Fintype.card κ), Fin (N ((Fintype.equivFin κ).symm j))) :=
      by rw [Equiv.symm_apply_eq]; rfl
    simp only [sigmaFinOrd, Equiv.trans_apply, h, finCongr_apply, Fin.val_cast]
    exact finSigmaFinEquiv_apply _
  rw [Fin.lt_def, hF, hF, Fin.lt_def]
  omega

/-- The ordering of the blocks of the assembled datum: the blocks of the summands one after
another, each in its own order. -/
noncomputable def directSumOrd :
    BlockIndex (Finset.univ : Finset κ) (∑ k, (P k).z) ≃
      Fin ((Finset.univ : Finset κ).card + ∑ k, (P k).z) :=
  (directSumIndexEquiv P).trans ((Equiv.sigmaCongrRight fun k => (P k).ord).trans
    ((sigmaFinOrd fun k => oneSlot.card + (P k).z).trans (finCongr (by
      rw [Finset.sum_add_distrib, Finset.card_univ]
      simp))))

omit [DecidableEq κ] in
theorem directSumOrd_lt_iff (k : κ) (b c : BlockIndex oneSlot (P k).z) :
    directSumOrd P ((directSumIndexEquiv P).symm ⟨k, b⟩) <
        directSumOrd P ((directSumIndexEquiv P).symm ⟨k, c⟩) ↔ (P k).ord b < (P k).ord c := by
  simp only [directSumOrd, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sigmaCongrRight_apply,
    finCongr_apply, Fin.lt_def, Fin.val_cast]
  rw [← Fin.lt_def, sigmaFinOrd_lt_iff]
  exact Fin.lt_def

/-! ### The assembled gauge -/

/-- The matrix of the assembled gauge: the block-diagonal sum of the gauge matrices of the
summands, relabelled along `e` and the coordinates of the blocks. -/
noncomputable def directSumGaugeMatrix (e : (Σ k, Fin (n k)) ≃ Fin DB) :
    Matrix (BlockSpace Dt (Finset.univ : Finset κ) (∑ k, (P k).z)) (Fin DB) ℂ :=
  (Matrix.blockDiagonal' fun k => gaugeMatrix (P k).gauge).submatrix (directSumCoordEquiv P)
    e.symm

/-- The matrix of the inverse of the assembled gauge. -/
noncomputable def directSumGaugeMatrixInv (e : (Σ k, Fin (n k)) ≃ Fin DB) :
    Matrix (Fin DB) (BlockSpace Dt (Finset.univ : Finset κ) (∑ k, (P k).z)) ℂ :=
  (Matrix.blockDiagonal' fun k => gaugeMatrixInv (P k).gauge).submatrix e.symm
    (directSumCoordEquiv P)

theorem directSumGaugeMatrix_mul_inv (e : (Σ k, Fin (n k)) ≃ Fin DB) :
    directSumGaugeMatrix P e * directSumGaugeMatrixInv P e = 1 := by
  rw [directSumGaugeMatrix, directSumGaugeMatrixInv, Matrix.submatrix_mul_equiv,
    ← Matrix.blockDiagonal'_mul]
  simp only [gaugeMatrix_mul_gaugeMatrixInv]
  rw [show (fun k => (1 : Matrix (BlockSpace (fun _ : Unit => Dt k) oneSlot (P k).z)
      (BlockSpace (fun _ : Unit => Dt k) oneSlot (P k).z) ℂ)) = 1 from rfl,
    Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

theorem directSumGaugeMatrixInv_mul (e : (Σ k, Fin (n k)) ≃ Fin DB) :
    directSumGaugeMatrixInv P e * directSumGaugeMatrix P e = 1 := by
  rw [directSumGaugeMatrix, directSumGaugeMatrixInv, Matrix.submatrix_mul_equiv,
    ← Matrix.blockDiagonal'_mul]
  simp only [gaugeMatrixInv_mul_gaugeMatrix]
  rw [show (fun k => (1 : Matrix (Fin (n k)) (Fin (n k)) ℂ)) = 1 from rfl,
    Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

/-- The assembled gauge: the direct sum of the gauges of the summands. -/
noncomputable def directSumGauge (e : (Σ k, Fin (n k)) ≃ Fin DB) :
    (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace Dt (Finset.univ : Finset κ) (∑ k, (P k).z) → ℂ) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (directSumGaugeMatrix P e))
    (Matrix.toLin' (directSumGaugeMatrixInv P e))
    (by rw [← Matrix.toLin'_mul, directSumGaugeMatrix_mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, directSumGaugeMatrixInv_mul, Matrix.toLin'_one])

/-- **Conjugation by the assembled gauge is blockwise**: a bond-space operator that is block
diagonal along `e` has, in the assembled block coordinates, the block-diagonal sum of the
matrices of its blocks in their own block coordinates. -/
theorem conjMatrix_directSumGauge (e : (Σ k, Fin (n k)) ≃ Fin DB)
    (X : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) :
    conjMatrix (directSumGauge P e) ((Matrix.blockDiagonal' X).submatrix e.symm e.symm) =
      (Matrix.blockDiagonal' fun k => conjMatrix (P k).gauge (X k)).submatrix
        (directSumCoordEquiv P) (directSumCoordEquiv P) := by
  rw [conjMatrix_eq_gaugeMatrix_mul]
  have h1 : gaugeMatrix (directSumGauge P e) = directSumGaugeMatrix P e :=
    LinearMap.toMatrix'_toLin' _
  have h2 : gaugeMatrixInv (directSumGauge P e) = directSumGaugeMatrixInv P e :=
    LinearMap.toMatrix'_toLin' _
  rw [h1, h2, directSumGaugeMatrix, directSumGaugeMatrixInv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  simp only [conjMatrix_eq_gaugeMatrix_mul]

/-! ### The assembled datum -/

variable (e : (Σ k, Fin (n k)) ≃ Fin DB) {A : MPSTensor d DB}
  (hA : ∀ i, A i = (Matrix.blockDiagonal' fun k => B k i).submatrix e.symm e.symm)

include hA in
/-- The letters of `A` in the assembled block coordinates. -/
theorem conjMatrix_directSumGauge_letter (i : Fin d) :
    conjMatrix (directSumGauge P e) (A i) =
      (Matrix.blockDiagonal' fun k => conjMatrix (P k).gauge (B k i)).submatrix
        (directSumCoordEquiv P) (directSumCoordEquiv P) := by
  rw [hA, conjMatrix_directSumGauge]

/-- **The direct sum of one-slot compression data** (P5 note, Theorem 7.7(i)–(iii)). If the
letters of `A` are block diagonal along `e` with blocks `B k`, and every block compresses onto
the single target `C k`, then `A` compresses onto the family `C`, with the zero slots of all
blocks as its zero slots. -/
noncomputable def directSum : MultiBlockCompression A (Finset.univ : Finset κ) C where
  z := ∑ k, (P k).z
  ord := directSumOrd P
  gauge := directSumGauge P e
  triangular i x y hxy := by
    rw [conjMatrix_directSumGauge_letter P e hA, Matrix.submatrix_apply]
    have hx := directSumIndexEquiv_fst P x
    have hy := directSumIndexEquiv_fst P y
    generalize directSumCoordEquiv P x = a at hx
    generalize directSumCoordEquiv P y = b at hy
    obtain ⟨k, a⟩ := a
    obtain ⟨l, b⟩ := b
    by_cases hkl : k = l
    · subst hkl
      rw [Matrix.blockDiagonal'_apply_eq]
      rw [← Equiv.eq_symm_apply] at hx hy
      dsimp only at hxy
      rw [hx, hy, directSumOrd_lt_iff] at hxy
      exact (P k).triangular i hxy
    · exact Matrix.blockDiagonal'_apply_ne _ _ _ hkl
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_directSumGauge_letter P e hA, Matrix.submatrix_apply]
    rw [directSumCoordEquiv_inl, directSumCoordEquiv_inl, Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun ((P s.1).matched i oneSlotMem) p) q
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_directSumGauge_letter P e hA, Matrix.submatrix_apply]
    rw [directSumCoordEquiv_inr, directSumCoordEquiv_inr, Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun ((P (directSumZeroEquiv P t).1).unmatched i
      (directSumZeroEquiv P t).2) p) q

theorem directSum_z : (directSum P e hA).z = ∑ k, (P k).z := rfl

/-- **The remainder of the direct sum is the direct sum of the remainders** (P5 note,
Theorem 7.7(vi)). -/
theorem remainder_directSum (i : Fin d) :
    (directSum P e hA).remainder i =
      (Matrix.blockDiagonal' fun k => (P k).remainder i).submatrix e.symm e.symm := by
  refine conjMatrix_injective (directSum P e hA).gauge ?_
  change conjMatrix (directSumGauge P e) _ = conjMatrix (directSumGauge P e) _
  rw [conjMatrix_directSumGauge]
  change conjMatrix (directSum P e hA).gauge _ = _
  rw [conjMatrix_remainder]
  change conjMatrix (directSumGauge P e) (A i) -
      Matrix.blockDiagonal' (conjMatrix (directSumGauge P e) (A i)).blockDiag' = _
  simp only [conjMatrix_remainder]
  rw [conjMatrix_directSumGauge_letter P e hA]
  ext x y
  simp only [Matrix.sub_apply, Matrix.blockDiagonal'_blockDiag'_apply, Matrix.submatrix_apply]
  have hxy : x.1 = y.1 ↔ directSumIndexEquiv P x.1 = directSumIndexEquiv P y.1 :=
    (directSumIndexEquiv P).injective.eq_iff.symm
  rw [directSumIndexEquiv_fst, directSumIndexEquiv_fst] at hxy
  generalize directSumCoordEquiv P x = a at hxy
  generalize directSumCoordEquiv P y = b at hxy
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  by_cases hkl : k = l
  · subst hkl
    have hab : x.1 = y.1 ↔ a.1 = b.1 := by
      rw [hxy, Sigma.mk.inj_iff]
      simp
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.sub_apply,
      Matrix.blockDiagonal'_blockDiag'_apply, hab]
  · have hne : ¬ x.1 = y.1 := fun h => hkl (congrArg Sigma.fst (hxy.1 h))
    simp only [hne, ↓reduceIte]
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkl,
      Matrix.blockDiagonal'_apply_ne _ _ _ hkl, sub_zero]

/-- The words of the remainder of the direct sum are the direct sums of the words of the
remainders of the blocks. -/
theorem evalWord_remainder_directSum (w : List (Fin d)) :
    Kraus.evalWord (directSum P e hA).remainder w =
      (Matrix.blockDiagonal' fun k => Kraus.evalWord (P k).remainder w).submatrix e.symm
        e.symm := by
  rw [show (directSum P e hA).remainder = fun i =>
      (Matrix.blockDiagonal' fun k => (P k).remainder i).submatrix e.symm e.symm from
    funext (remainder_directSum P e hA)]
  exact evalWord_blockDiagonal'_submatrix e (fun i k => (P k).remainder i) w

/-- **Nilpotency of the remainder of a direct sum, block by block**: a word vanishing in the
remainder of every block vanishes in the remainder of the direct sum. The nilpotency order of
the assembled remainder is therefore the largest nilpotency order of the blocks. -/
theorem evalWord_remainder_directSum_eq_zero (w : List (Fin d))
    (hw : ∀ k, Kraus.evalWord (P k).remainder w = 0) :
    Kraus.evalWord (directSum P e hA).remainder w = 0 := by
  rw [evalWord_remainder_directSum]
  simp only [hw]
  rw [show (fun k => (0 : Matrix (Fin (n k)) (Fin (n k)) ℂ)) = 0 from rfl,
    Matrix.blockDiagonal'_zero, Matrix.submatrix_zero]
  rfl

/-- A word that does not vanish in the remainder of one block does not vanish in the remainder
of the direct sum: the nilpotency order of the assembled remainder is at least that of every
block. -/
theorem evalWord_remainder_directSum_ne_zero (w : List (Fin d)) (k : κ)
    (hk : Kraus.evalWord (P k).remainder w ≠ 0) :
    Kraus.evalWord (directSum P e hA).remainder w ≠ 0 := by
  rw [evalWord_remainder_directSum]
  intro h
  refine hk (Matrix.ext fun p q => ?_)
  have := congrFun (congrFun h (e ⟨k, p⟩)) (e ⟨k, q⟩)
  simpa using this

end MultiBlockCompression

end MPSTensor
