/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.BlockTriangularWord
import TNLean.Algebra.FlagBlockTriangular
import TNLean.MPS.Core.MultiBlockWord
import TNLean.MPS.Core.Reduction
import TNLean.MPS.FundamentalTheorem.Reduction.Flag

/-!
# The multi-block asymmetric compression data

This file records the conclusion of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) as a
structure, and derives from it the biorthogonality, compression, remainder and dimension clauses
(iv)–(vii) of that theorem.

A tensor `B` is compressed onto a finite family of blocks `C s`, `s ∈ S`, when there is a change
of coordinates on the bond space of `B` in which every `B^i` is block upper triangular for one
common decomposition into `|S| + z` blocks, the block of the slot `s` is `C s`, and the remaining
`z` blocks are one-dimensional and zero.

## Main definitions

* `MPSTensor.BlockIndex`, `MPSTensor.slotSize`, `MPSTensor.BlockSpace`: the block labels, their
  sizes and the resulting graded coordinate space.
* `MPSTensor.conjMatrix`: the matrix of a bond-space operator in the block coordinates.
* `MPSTensor.MultiBlockCompression`: the data of Theorem 7.7, clauses (i)–(iii).
* `MPSTensor.MultiBlockCompression.left`, `MPSTensor.MultiBlockCompression.right`: the
  compression pair of a slot (the note's `W_s` and `V_s`).
* `MPSTensor.MultiBlockCompression.remainder`: the remainder `R^i` of clause (vi).

## Main results

* `MPSTensor.MultiBlockCompression.dim_eq`: the dimension count, clause (vii).
* `MPSTensor.MultiBlockCompression.left_mul_right_self`,
  `MPSTensor.MultiBlockCompression.left_mul_right_of_ne`: biorthogonality, clause (iv).
* `MPSTensor.MultiBlockCompression.left_mul_evalWord_mul_right`,
  `MPSTensor.MultiBlockCompression.isReduction`: the compression identity, clause (v).
* `MPSTensor.MultiBlockCompression.evalWord_remainder_eq_zero`: nilpotency of the remainder,
  clause (vi).
* `MPSTensor.exists_multiBlockCompression_of_isNormal`: the theorem itself, that a tensor whose
  positive-length word traces are the sums of the word traces of a finite family of normal
  blocks admits a multi-block compression onto that family.
-/

open scoped Matrix

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} {D : ι → ℕ}

/-- Block labels of a multi-block compression: the target slots `s ∈ S` together with `z`
one-dimensional zero slots (Theorem 7.7(i)–(iii)). -/
abbrev BlockIndex (S : Finset ι) (z : ℕ) : Type _ := {s // s ∈ S} ⊕ Fin z

/-- Block sizes: the bond dimension `D s` on a target slot, and `1` on a zero slot. The
definition is reducible so that the diagonal block of a target slot has the bond dimension of
that slot on the nose. -/
abbrev slotSize (D : ι → ℕ) {S : Finset ι} {z : ℕ} (b : BlockIndex S z) : ℕ :=
  Sum.rec (motive := fun _ => ℕ) (fun s => D s.1) (fun _ => 1) b

/-- The graded coordinate space of a multi-block compression. -/
abbrev BlockSpace (D : ι → ℕ) (S : Finset ι) (z : ℕ) : Type _ :=
  (b : BlockIndex S z) × Fin (slotSize D b)

variable [DecidableEq ι]

section ConjMatrix

variable {S : Finset ι} {z : ℕ}

/-- A coordinate change of the bond space, read as a linear equivalence of matrix algebras. -/
noncomputable def conjMatrixEquiv (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ)) :
    Matrix (Fin DB) (Fin DB) ℂ ≃ₗ[ℂ]
      Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ :=
  Matrix.toLin' ≪≫ₗ g.conj ≪≫ₗ LinearMap.toMatrix'

/-- The matrix of a bond-space operator `A` in the block coordinates given by `g`. -/
noncomputable def conjMatrix (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ))
    (A : Matrix (Fin DB) (Fin DB) ℂ) : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ :=
  conjMatrixEquiv g A

variable (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ))

theorem conjMatrix_apply (A : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix g A = LinearMap.toMatrix' (g.conj (Matrix.toLin' A)) := rfl

/-- The matrix of the coordinate change itself. -/
noncomputable def gaugeMatrix : Matrix (BlockSpace D S z) (Fin DB) ℂ :=
  LinearMap.toMatrix' (g : (Fin DB → ℂ) →ₗ[ℂ] (BlockSpace D S z → ℂ))

/-- The matrix of the inverse coordinate change. -/
noncomputable def gaugeMatrixInv : Matrix (Fin DB) (BlockSpace D S z) ℂ :=
  LinearMap.toMatrix' (g.symm : (BlockSpace D S z → ℂ) →ₗ[ℂ] (Fin DB → ℂ))

@[simp] theorem gaugeMatrix_mul_gaugeMatrixInv : gaugeMatrix g * gaugeMatrixInv g = 1 := by
  rw [gaugeMatrix, gaugeMatrixInv, ← LinearMap.toMatrix'_comp]
  simp

@[simp] theorem gaugeMatrixInv_mul_gaugeMatrix : gaugeMatrixInv g * gaugeMatrix g = 1 := by
  rw [gaugeMatrix, gaugeMatrixInv, ← LinearMap.toMatrix'_comp]
  simp

theorem conjMatrix_eq_gaugeMatrix_mul (A : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix g A = gaugeMatrix g * A * gaugeMatrixInv g := by
  rw [conjMatrix_apply, LinearEquiv.conj_apply, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', gaugeMatrix, gaugeMatrixInv]

theorem conjMatrix_mul (A A' : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix g (A * A') = conjMatrix g A * conjMatrix g A' := by
  rw [conjMatrix_apply, conjMatrix_apply, conjMatrix_apply, Matrix.toLin'_mul,
    LinearEquiv.conj_comp, LinearMap.toMatrix'_comp]

@[simp] theorem conjMatrix_one : conjMatrix g 1 = 1 := by
  rw [conjMatrix_apply, Matrix.toLin'_one, LinearEquiv.conj_id, LinearMap.toMatrix'_id]

@[simp] theorem conjMatrix_zero : conjMatrix g (0 : Matrix (Fin DB) (Fin DB) ℂ) = 0 :=
  map_zero (conjMatrixEquiv g)

theorem conjMatrix_sub (A A' : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix g (A - A') = conjMatrix g A - conjMatrix g A' :=
  map_sub (conjMatrixEquiv g) A A'

theorem conjMatrix_sum {κ : Type*} (t : Finset κ) (f : κ → Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix g (∑ x ∈ t, f x) = ∑ x ∈ t, conjMatrix g (f x) :=
  map_sum (conjMatrixEquiv g) f t

theorem conjMatrix_injective : Function.Injective (conjMatrix (D := D) g) :=
  (conjMatrixEquiv g).injective

/-- Word evaluation commutes with the change of block coordinates. -/
theorem evalWord_conjMatrix (B : MPSTensor d DB) (w : List (Fin d)) :
    _root_.evalWord (fun i => conjMatrix g (B i)) w = conjMatrix g (Kraus.evalWord B w) := by
  induction w with
  | nil => simp [_root_.evalWord, Kraus.evalWord]
  | cons i w ih => rw [_root_.evalWord, ih, Kraus.evalWord, conjMatrix_mul]

end ConjMatrix

/-- **Multi-block asymmetric compression data** (P5 note, Theorem 7.7(i)–(iii)). There are `z`
zero slots, an ordering `ord` of the `|S| + z` blocks, and a change of coordinates `gauge` of the
bond space of `B` in which every `B^i` is block upper triangular, the diagonal block of the slot
`s` is `C s`, and the diagonal block of each zero slot is the `1 × 1` zero matrix. -/
structure MultiBlockCompression (B : MPSTensor d DB) (S : Finset ι)
    (C : ∀ s, MPSTensor d (D s)) where
  /-- the number of zero slots -/
  z : ℕ
  /-- the ordering of the blocks -/
  ord : BlockIndex S z ≃ Fin (S.card + z)
  /-- the change of coordinates of the bond space -/
  gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ)
  /-- every one-site matrix is block upper triangular, clause (i) -/
  triangular : ∀ i, (conjMatrix gauge (B i)).BlockTriangular fun x => ord x.1
  /-- the diagonal block of a target slot is the corresponding block, clause (ii) -/
  matched : ∀ (i : Fin d) (s : {s // s ∈ S}),
    (conjMatrix gauge (B i)).blockDiag' (Sum.inl s) = C s.1 i
  /-- the diagonal block of a zero slot vanishes, clause (iii) -/
  unmatched : ∀ (i : Fin d) (t : Fin z), (conjMatrix gauge (B i)).blockDiag' (Sum.inr t) = 0

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}
  (P : MultiBlockCompression B S C)

/-- **The dimension count** (P5 note, Theorem 7.7(vii), `eq:p5-main-dimension`). -/
theorem dim_eq : DB = ∑ s ∈ S, D s + P.z := by
  have h := P.gauge.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Fintype.card_sigma, Fintype.sum_sum_type] at h
  simpa [Finset.sum_attach S D] using h

/-- The compression out of the bond space of `B` onto the slot `s` (the note's `W_s`). -/
noncomputable def left (s : {s // s ∈ S}) : Matrix (Fin (D s.1)) (Fin DB) ℂ :=
  Matrix.blockProj (slotSize D) (Sum.inl s) * gaugeMatrix P.gauge

/-- The compression into the bond space of `B` from the slot `s` (the note's `V_s`). -/
noncomputable def right (s : {s // s ∈ S}) : Matrix (Fin DB) (Fin (D s.1)) ℂ :=
  gaugeMatrixInv P.gauge * Matrix.blockEmbed (slotSize D) (Sum.inl s)

/-- Sandwiching a bond-space operator between two compressions reads off the corresponding
off-diagonal block of its matrix in the block coordinates. -/
theorem left_mul_mul_right (A : Matrix (Fin DB) (Fin DB) ℂ) (s t : {s // s ∈ S}) :
    P.left s * A * P.right t =
      Matrix.blockProj (slotSize D) (Sum.inl s) * conjMatrix P.gauge A *
        Matrix.blockEmbed (slotSize D) (Sum.inl t) := by
  simp only [left, right, conjMatrix_eq_gaugeMatrix_mul, Matrix.mul_assoc]

/-- **Biorthogonality of a slot with itself** (P5 note, `eq:p5-main-biorthogonality`). -/
theorem left_mul_right_self (s : {s // s ∈ S}) : P.left s * P.right s = 1 := by
  simp only [left, right, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gaugeMatrix P.gauge), gaugeMatrix_mul_gaugeMatrixInv, Matrix.one_mul,
    Matrix.blockProj_mul_blockEmbed_self]

/-- **Biorthogonality of two distinct slots** (P5 note, `eq:p5-main-biorthogonality`). -/
theorem left_mul_right_of_ne {s t : {s // s ∈ S}} (h : s ≠ t) : P.left s * P.right t = 0 := by
  simp only [left, right, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gaugeMatrix P.gauge), gaugeMatrix_mul_gaugeMatrixInv, Matrix.one_mul,
    Matrix.blockProj_mul_blockEmbed_of_ne (fun hst => h (Sum.inl_injective hst))]

/-- **The compression identity** (P5 note, `eq:p5-main-compression`). Compressing a word of `B`
to the slot `s` gives the corresponding word of `C s`. -/
theorem left_mul_evalWord_mul_right (s : {s // s ∈ S}) (w : List (Fin d)) :
    P.left s * Kraus.evalWord B w * P.right s = Kraus.evalWord (C s.1) w := by
  rw [P.left_mul_mul_right, Matrix.blockProj_mul_mul_blockEmbed, ← evalWord_conjMatrix,
    Matrix.blockDiag'_evalWord P.ord.injective P.triangular]
  simp [P.matched]

/-- Each slot of a multi-block compression is a rectangular reduction of `B`. -/
theorem isReduction (s : {s // s ∈ S}) :
    MPSTensor.IsReduction B (C s.1) (P.left s) (P.right s) :=
  ⟨P.left_mul_right_self s, P.left_mul_evalWord_mul_right s⟩

/-- **The remainder** `R^i = B^i - ∑_s V_s C_s^i W_s` (P5 note,
`eq:p5-main-reconstruction`). -/
noncomputable def remainder : MPSTensor d DB :=
  fun i => B i - ∑ s : {s // s ∈ S}, P.right s * C s.1 i * P.left s

/-- Conjugating a slot-supported operator back to the block coordinates places it in the
diagonal block of that slot. -/
theorem conjMatrix_right_mul_mul_left (s : {s // s ∈ S})
    (X : Matrix (Fin (D s.1)) (Fin (D s.1)) ℂ) :
    conjMatrix P.gauge (P.right s * X * P.left s) =
      Matrix.blockEmbed (slotSize D) (Sum.inl s) * X *
        Matrix.blockProj (slotSize D) (Sum.inl s) := by
  simp only [conjMatrix_eq_gaugeMatrix_mul, left, right, Matrix.mul_assoc]
  rw [gaugeMatrix_mul_gaugeMatrixInv, Matrix.mul_one,
    ← Matrix.mul_assoc (gaugeMatrix P.gauge), gaugeMatrix_mul_gaugeMatrixInv, Matrix.one_mul]

/-- In the block coordinates the remainder is the matrix of `B^i` with its diagonal blocks
removed. -/
theorem conjMatrix_remainder (i : Fin d) :
    conjMatrix P.gauge (P.remainder i) =
      conjMatrix P.gauge (B i) -
        Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' := by
  have hsum : ∑ s : {s // s ∈ S}, conjMatrix P.gauge (P.right s * C s.1 i * P.left s) =
      Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' := by
    rw [← Matrix.sum_blockEmbed_mul_mul_blockProj, Fintype.sum_sum_type]
    have h2 : ∑ t : Fin P.z, Matrix.blockEmbed (slotSize D) (Sum.inr t) *
        (conjMatrix P.gauge (B i)).blockDiag' (Sum.inr t) *
        Matrix.blockProj (slotSize D) (Sum.inr t) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [P.unmatched i t]; simp
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun s _ => by
      rw [P.conjMatrix_right_mul_mul_left, P.matched i s]
  rw [remainder, conjMatrix_sub, conjMatrix_sum, hsum]

/-- **Nilpotency of the remainder** (P5 note, `eq:p5-main-nilpotency`). A product of as many
remainder matrices as there are blocks vanishes. -/
theorem evalWord_remainder_eq_zero (w : List (Fin d)) (hw : S.card + P.z ≤ w.length) :
    Kraus.evalWord P.remainder w = 0 := by
  have hstrict : ∀ i, Matrix.StrictBlockTriangular (⇑P.ord)
      (conjMatrix P.gauge (P.remainder i)) := by
    intro i
    rw [P.conjMatrix_remainder i]
    exact Matrix.StrictBlockTriangular.sub_blockDiagonal'_blockDiag' P.ord.injective
      (P.triangular i)
  have hzero := Matrix.evalWord_eq_zero_of_strictBlockTriangular hstrict w hw
  rw [evalWord_conjMatrix] at hzero
  refine conjMatrix_injective P.gauge ?_
  rw [hzero, conjMatrix_zero]

end MultiBlockCompression


/-- Conjugating an endomorphism of a coordinate space by a relabelling of the coordinates
reindexes its matrix. -/
theorem toMatrix'_conj_funCongrLeft {α γ : Type*} [Fintype α] [DecidableEq α] [Fintype γ]
    [DecidableEq γ] (τ : γ ≃ α) (Y : Module.End ℂ (α → ℂ)) :
    LinearMap.toMatrix' ((LinearEquiv.funCongrLeft ℂ ℂ τ).conj Y) =
      (LinearMap.toMatrix' Y).submatrix τ τ := by
  ext c c'
  have hv : (LinearEquiv.funCongrLeft ℂ ℂ τ).symm (Pi.single c' (1 : ℂ)) =
      Pi.single (τ c') (1 : ℂ) := by
    funext a
    simp only [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  simp only [LinearMap.toMatrix'_apply, Matrix.submatrix_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, hv]

/-- The prescribed diagonal block at a block label: the target block on a slot, and the
`1 × 1` zero matrix on a zero slot. -/
def blockOf (D : ι → ℕ) {S : Finset ι} {z : ℕ} (C : ∀ s, MPSTensor d (D s)) (i : Fin d) :
    ∀ b : BlockIndex S z, Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) ℂ :=
  Sum.rec (motive := fun b => Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) ℂ)
    (fun s => C s.1 i) fun _ => 0

open WordAlgebra in
/-- **The multi-block asymmetric compression theorem** (P5 note, Theorem 7.7,
`thm:p5-asymmetric-compression`, clauses (i)–(iii)). A tensor whose positive-length word traces
are the sums of the word traces of a finite family of normal blocks of positive bond dimension
admits a multi-block compression onto that family. -/
theorem exists_multiBlockCompression_of_isNormal (S : Finset ι) (C : ∀ s, MPSTensor d (D s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) :
    Nonempty (MultiBlockCompression B S C) := by
  classical
  obtain ⟨F⟩ := exists_flagData C hC hD B.WordModule
    fun w hw => by rw [traceWord_wordModule]; exact htr w hw
  set lab : Fin F.r ≃ BlockIndex S F.z := Equiv.ofBijective F.label F.label_bijective with hlab
  have hr : F.r = S.card + F.z := by
    simpa [Fintype.card_sum] using Fintype.card_congr lab
  set ord : BlockIndex S F.z ≃ Fin (S.card + F.z) := lab.symm.trans (finCongr hr) with hord
  set H : Fin (F.r + 1) → Submodule ℂ B.WordModule := fun k => (F.H k).restrictScalars ℂ with hH
  have h0 : H 0 = ⊥ := by simp [hH, F.H_zero]
  have htop : H (Fin.last F.r) = ⊤ := by simp [hH, F.H_last]
  have hmono : Monotone H := fun a b hab _ hx => F.H_mono hab hx
  set f : Fin d → Module.End ℂ B.WordModule :=
    fun i => actAlgHom B.WordModule (ofWord [i]) with hfdef
  have hf : ∀ (i : Fin d) (k : Fin (F.r + 1)), ∀ x ∈ H k, f i x ∈ H k :=
    fun i k _ hx => (F.H k).smul_mem _ hx
  -- Coordinates on each subquotient of the flag, matching the prescribed diagonal blocks.
  have hψ : ∀ k : Fin F.r, ∃ ψ : Submodule.flagQuot H k ≃ₗ[ℂ] (Fin (slotSize D (F.label k)) → ℂ),
      ∀ i : Fin d, LinearMap.toMatrix' (ψ.conj (LinearMap.flagQuotMap H (f i) (hf i) k)) =
        blockOf D C i (F.label k) := by
    intro k
    let β : Submodule.flagQuot H k ≃ₗ[ℂ] F.step k :=
      Submodule.Quotient.restrictScalarsEquiv ℂ ((F.H k.castSucc).comap (F.H k.succ).subtype)
    have hβ : ∀ (i : Fin d) (x : Submodule.flagQuot H k),
        β (LinearMap.flagQuotMap H (f i) (hf i) k x) = (ofWord [i] : WordAlgebra d) • β x := by
      intro i x
      refine Submodule.Quotient.induction_on _ x fun v => ?_
      rfl
    rcases hk : F.label k with s | t
    · obtain ⟨ε⟩ := F.matched k s hk
      refine ⟨β.trans ((ε.restrictScalars ℂ).trans (C s.1).wordRep.asModuleEquiv), fun i => ?_⟩
      have hcomm : ∀ x : Submodule.flagQuot H k,
          (C s.1).wordRep.asModuleEquiv (ε (β (LinearMap.flagQuotMap H (f i) (hf i) k x))) =
            Matrix.toLin' (C s.1 i)
              ((C s.1).wordRep.asModuleEquiv (ε (β x))) := by
        intro x
        rw [hβ i x, map_smul, MPSTensor.asModuleEquiv_ofWord_smul, Matrix.toLin'_apply]
        simp [Kraus.evalWord]
      have hmap : (β.trans ((ε.restrictScalars ℂ).trans (C s.1).wordRep.asModuleEquiv)).conj
          (LinearMap.flagQuotMap H (f i) (hf i) k) = Matrix.toLin' (C s.1 i) := by
        refine LinearMap.ext fun y => ?_
        rw [LinearEquiv.conj_apply_apply]
        simpa using hcomm ((β.trans ((ε.restrictScalars ℂ).trans
          (C s.1).wordRep.asModuleEquiv)).symm y)
      rw [hmap, LinearMap.toMatrix'_toLin']
      rfl
    · have hdim : Module.finrank ℂ (Submodule.flagQuot H k) =
          Module.finrank ℂ (Fin (slotSize D (Sum.inr t : BlockIndex S F.z)) → ℂ) := by
        rw [β.finrank_eq, F.unmatched_finrank k t hk, Module.finrank_fintype_fun_eq_card]
        simp
      refine ⟨LinearEquiv.ofFinrankEq _ _ hdim, fun i => ?_⟩
      have hzero : LinearMap.flagQuotMap H (f i) (hf i) k = 0 := by
        refine LinearMap.ext fun x => ?_
        have hx := hβ i x
        rw [F.unmatched_smul k t hk i (β x)] at hx
        simpa using β.map_eq_zero_iff.1 hx
      rw [hzero]
      simp [blockOf]
  choose ψ hψprop using hψ
  obtain ⟨e, htri, hdiag, -, -⟩ := exists_linearEquiv_blockTriangular_of_flag H h0 htop hmono f hf
    (fun k => slotSize D (F.label k)) ψ
  set σ : ((k : Fin F.r) × Fin (slotSize D (F.label k))) ≃ BlockSpace D S F.z :=
    Equiv.sigmaCongrLeft (β := fun b : BlockIndex S F.z => Fin (slotSize D b)) lab with hσ
  set gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S F.z → ℂ) :=
    (B.wordRep.asModuleEquiv.symm.trans e).trans (LinearEquiv.funCongrLeft ℂ ℂ σ.symm) with hgauge
  have hconj : ∀ i, conjMatrix gauge (B i) =
      (LinearMap.toMatrix' (e.conj (f i))).submatrix σ.symm σ.symm := by
    intro i
    have hfi : B.wordRep.asModuleEquiv.symm.conj (Matrix.toLin' (B i)) = f i := by
      simp only [hfdef, MPSTensor.actAlgHom_wordModule_ofWord B [i]]
      simp [Kraus.evalWord]
    rw [conjMatrix_apply, hgauge,
      show ((B.wordRep.asModuleEquiv.symm.trans e).trans
          (LinearEquiv.funCongrLeft ℂ ℂ σ.symm)).conj (Matrix.toLin' (B i)) =
        (LinearEquiv.funCongrLeft ℂ ℂ σ.symm).conj
          (e.conj (B.wordRep.asModuleEquiv.symm.conj (Matrix.toLin' (B i)))) from rfl,
      hfi, toMatrix'_conj_funCongrLeft]
  have hfst : ∀ b : BlockSpace D S F.z, (σ.symm b).1 = lab.symm b.1 := fun _ => rfl
  have htriangular : ∀ i, (conjMatrix gauge (B i)).BlockTriangular fun x => ord x.1 := by
    intro i x y hlt
    rw [hconj i, Matrix.submatrix_apply]
    refine htri i ?_
    simp only [hfst]
    exact hlt
  have hblock : ∀ (i : Fin d) (b : BlockIndex S F.z),
      (conjMatrix gauge (B i)).blockDiag' b = blockOf D C i b := by
    intro i b
    obtain ⟨k, rfl⟩ := F.label_bijective.2 b
    have hx : ∀ p : Fin (slotSize D (F.label k)),
        σ.symm ⟨F.label k, p⟩ = (⟨k, p⟩ : (k : Fin F.r) × Fin (slotSize D (F.label k))) :=
      fun p => σ.symm_apply_apply ⟨k, p⟩
    ext p q
    have hd := congrFun (congrFun (hdiag i k) p) q
    rw [Matrix.blockDiag'_apply] at hd
    rw [hconj i, Matrix.blockDiag'_apply, Matrix.submatrix_apply, hx p, hx q, hd, hψprop k i]
  exact ⟨{ z := F.z
           ord := ord
           gauge := gauge
           triangular := htriangular
           matched := fun i s => hblock i (Sum.inl s)
           unmatched := fun i t => hblock i (Sum.inr t) }⟩

end MPSTensor
