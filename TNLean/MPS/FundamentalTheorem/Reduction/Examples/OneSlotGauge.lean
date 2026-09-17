/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.CanonicalForm.TranslationInvariantUniqueness
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# One-slot compression data and integer certificates

The pair blocks of a stacked matrix product operator tensor compress onto a single target each.
This file packages the two shapes of one-slot compression data (P5 note,
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, Theorem 7.7) that occur
in the worked examples, together with the integer certificates that reduce the remaining
verifications to decidable identities between integer matrices.

* A tensor conjugate to its target by an explicit invertible matrix is a one-slot datum with no
  zero slots (`MPSTensor.MultiBlockCompression.ofConjMatrix`); its remainder vanishes.
* A four-dimensional tensor with a one-dimensional target sitting at the third position of a
  four-step flag, with two zero slots below and one above, is a one-slot datum with three zero
  slots (`MPSTensor.MultiBlockCompression.ofScalarFlagFour`).
* A tensor whose length-two words realise every matrix unit up to a common nonzero integer
  factor is normal at blocking length two (`MPSTensor.isNBlkInjective_two_of_int`).
* A sitewise intertwiner space vanishes as soon as four rows of the stacked sitewise system form
  an invertible integer matrix (`MPSTensor.right_intertwiner_eq_zero_of_int`,
  `MPSTensor.left_intertwiner_eq_zero_of_int`).

## Main definitions

* `MPSTensor.stackedInt`: the integer letters of a stacked product over the pair alphabet.
* `MPSTensor.oneSlot`, `MPSTensor.oneSlotMem`: the singleton slot set and its element.
* `MPSTensor.MultiBlockCompression.ofConjMatrix`, `MPSTensor.MultiBlockCompression.ofConjInt`,
  `MPSTensor.MultiBlockCompression.ofEq`: the datum of a conjugate tensor.
* `MPSTensor.MultiBlockCompression.ofScalarFlagFour`: the datum of a four-dimensional tensor
  with a one-dimensional target and three zero slots.

## Main results

* `MPSTensor.MultiBlockCompression.remainder_ofConjMatrix`: the remainder of a conjugate datum
  vanishes.
* `MPSTensor.isNBlkInjective_two_of_int`, `MPSTensor.isNormal_smul`: normality certificates.
* `MPSTensor.right_intertwiner_eq_zero_of_int`, `MPSTensor.left_intertwiner_eq_zero_of_int`:
  vanishing of a sitewise intertwiner space from an integer certificate.
-/

open scoped Matrix

namespace MPSTensor

variable {d : ℕ}

theorem complexOfInt_zero {m n : Type*} : complexOfInt (0 : Matrix m n ℤ) = 0 := by
  ext i j
  simp [complexOfInt]

/-! ### Stacked products over the pair alphabet -/

section Stacked

variable {D₁ D₂ : ℕ}

/-- The integer letters of the stacked product of two integer matrix product operator tensors,
read over the pair alphabet `Fin (d * d)`, letter `a = d o + i`. -/
def stackedInt (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) ℤ)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) ℤ) (a : Fin (d * d)) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℤ :=
  mulIntTensor M N a.divNat a.modNat

/-- The pair-alphabet view of the stacked product of two integer tensors is the coercion of
`stackedInt`. -/
theorem toMPSTensor_mulTensor_complexOfInt (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) ℤ)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) ℤ) (a : Fin (d * d)) :
    (MPOTensor.mulTensor (fun i j => complexOfInt (M i j))
      (fun i j => complexOfInt (N i j))).toMPSTensor a = complexOfInt (stackedInt M N a) :=
  mulTensor_complexOfInt M N _ _

end Stacked

/-! ### The single slot -/

/-- The slot set of a one-slot compression datum. -/
abbrev oneSlot : Finset Unit := {()}

/-- The single slot as an element of the slot subtype. -/
abbrev oneSlotMem : {s // s ∈ oneSlot} := ⟨(), Finset.mem_singleton_self ()⟩

theorem eq_oneSlotMem (s : {s // s ∈ oneSlot}) : s = oneSlotMem :=
  Subtype.ext (Subsingleton.elim _ _)

/-! ### Conjugate tensors -/

/-- The labelling of the bond coordinates by the graded block space of a one-slot datum with no
zero slots: the block space is the bond space of the target. -/
def oneSlotTau (D : ℕ) : BlockSpace (fun _ : Unit => D) oneSlot 0 ≃ Fin D where
  toFun x :=
    match x with
    | ⟨Sum.inl _, p⟩ => p
    | ⟨Sum.inr t, _⟩ => t.elim0
  invFun p := ⟨Sum.inl oneSlotMem, p⟩
  left_inv := by
    rintro ⟨s | t, p⟩
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      rfl
    · exact t.elim0
  right_inv _ := rfl

/-- The block ordering of a one-slot datum with no zero slots. -/
def oneSlotOrdZero : BlockIndex oneSlot 0 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := Sum.inl oneSlotMem
  left_inv := by
    rintro (s | t)
    · exact congrArg Sum.inl (eq_oneSlotMem s).symm
    · exact t.elim0
  right_inv _ := Subsingleton.elim _ _

namespace MultiBlockCompression

variable {D : ℕ} {B C : MPSTensor d D}

/-- **A conjugate tensor is a one-slot compression datum with no zero slots.** If
`G * B i * Ginv = C i` for an invertible `G` with inverse `Ginv`, then `B` compresses onto the
single target `C` with `z = 0` (P5 note, Theorem 7.7(i)–(iii)). -/
noncomputable def ofConjMatrix (G Ginv : Matrix (Fin D) (Fin D) ℂ) (hG : G * Ginv = 1)
    (hG' : Ginv * G = 1) (h : ∀ i, G * B i * Ginv = C i) :
    MultiBlockCompression B oneSlot (fun _ : Unit => C) where
  z := 0
  ord := oneSlotOrdZero
  gauge := gaugeOfMatrix (oneSlotTau D) G Ginv hG hG'
  triangular _ _ _ hxy := absurd hxy (lt_irrefl _)
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, h i]
    rfl
  unmatched _ t := t.elim0

/-- The integer form of `ofConjMatrix`: all matrices are entrywise coercions of integer
matrices, and the conjugation identity is an identity between integer matrices. -/
noncomputable def ofConjInt (BInt CInt : Fin d → Matrix (Fin D) (Fin D) ℤ)
    (hB : ∀ i, B i = complexOfInt (BInt i)) (hC : ∀ i, C i = complexOfInt (CInt i))
    (G Ginv : Matrix (Fin D) (Fin D) ℤ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (h : ∀ i, G * BInt i * Ginv = CInt i) :
    MultiBlockCompression B oneSlot (fun _ : Unit => C) :=
  ofConjMatrix (complexOfInt G) (complexOfInt Ginv)
    (by rw [← complexOfInt_mul, hG, complexOfInt_one])
    (by rw [← complexOfInt_mul, hG', complexOfInt_one])
    (fun i => by rw [hB, ← complexOfInt_mul, ← complexOfInt_mul, h, hC])

/-- **A tensor equal to its target is a one-slot compression datum** with the identity gauge and
no zero slots. -/
noncomputable def ofEq (h : ∀ i, B i = C i) :
    MultiBlockCompression B oneSlot (fun _ : Unit => C) :=
  ofConjMatrix 1 1 (Matrix.one_mul 1) (Matrix.one_mul 1)
    fun i => by rw [Matrix.one_mul, Matrix.mul_one, h]

variable (G Ginv : Matrix (Fin D) (Fin D) ℂ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
  (h : ∀ i, G * B i * Ginv = C i)

theorem left_ofConjMatrix : (ofConjMatrix G Ginv hG hG' h).left oneSlotMem = G := by
  rw [left_gaugeOfMatrix (ofConjMatrix G Ginv hG hG' h) (hG := hG) (hG' := hG') rfl]
  ext i j
  rfl

theorem right_ofConjMatrix : (ofConjMatrix G Ginv hG hG' h).right oneSlotMem = Ginv := by
  rw [right_gaugeOfMatrix (ofConjMatrix G Ginv hG hG' h) (hG := hG) (hG' := hG') rfl]
  ext i j
  rfl

/-- The remainder of a conjugate datum vanishes: the compression is an exact change of
coordinates. -/
theorem remainder_ofConjMatrix : (ofConjMatrix G Ginv hG hG' h).remainder = 0 := by
  funext i
  rw [remainder, Finset.sum_eq_single_of_mem oneSlotMem (Finset.mem_univ oneSlotMem)
    fun b _ hb => absurd (eq_oneSlotMem b) hb, left_ofConjMatrix, right_ofConjMatrix]
  change B i - Ginv * C i * G = 0
  rw [← h i, Matrix.mul_assoc, Matrix.mul_assoc, hG', Matrix.mul_one, ← Matrix.mul_assoc, hG',
    Matrix.one_mul, sub_self]

/-- The remainder of the datum of a tensor equal to its target vanishes. -/
theorem remainder_ofEq (h : ∀ i, B i = C i) : (ofEq h).remainder = 0 :=
  remainder_ofConjMatrix 1 1 (Matrix.one_mul 1) (Matrix.one_mul 1)
    fun i => by rw [Matrix.one_mul, Matrix.mul_one, h]

/-- The remainder of an integer conjugate datum vanishes. -/
theorem remainder_ofConjInt (BInt CInt : Fin d → Matrix (Fin D) (Fin D) ℤ)
    (hB : ∀ i, B i = complexOfInt (BInt i)) (hC : ∀ i, C i = complexOfInt (CInt i))
    (G Ginv : Matrix (Fin D) (Fin D) ℤ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (h : ∀ i, G * BInt i * Ginv = CInt i) :
    (ofConjInt BInt CInt hB hC G Ginv hG hG' h).remainder = 0 := by
  unfold ofConjInt
  exact remainder_ofConjMatrix _ _ _ _ _

end MultiBlockCompression

namespace MultiBlockCompression

variable {DB DC : ℕ} {B : MPSTensor d DB} {C : MPSTensor d DC}

/-- The word traces of a one-slot datum: the trace of every nonempty word of `B` is the trace
of the corresponding word of the target. -/
theorem trace_evalWord_oneSlot (P : MultiBlockCompression B oneSlot (fun _ : Unit => C))
    (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B w) = Matrix.trace (Kraus.evalWord C w) := by
  have := P.trace_evalWord_eq_sum w hw
  rwa [Finset.sum_singleton] at this

/-- The word traces of a weighted one-slot datum: the trace of every nonempty word of `B` is
the corresponding power of the weight times the trace of the word of the unweighted target. -/
theorem trace_evalWord_oneSlot_smul {c : ℂ}
    (P : MultiBlockCompression B oneSlot (fun _ : Unit => c • C)) (w : List (Fin d))
    (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B w) = c ^ w.length * Matrix.trace (Kraus.evalWord C w) := by
  rw [P.trace_evalWord_oneSlot w hw, show c • C = fun i => c • C i from rfl,
    Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]

end MultiBlockCompression

/-! ### A one-dimensional target in a four-step flag -/

/-- The block ordering of a four-dimensional bond space with a one-dimensional target: two zero
slots below the target and one above. -/
def scalarFlagOrd : BlockIndex oneSlot 3 ≃ Fin 4 where
  toFun
    | Sum.inl _ => 2
    | Sum.inr t => ![0, 1, 3] t
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inr 1
    | 2 => Sum.inl oneSlotMem
    | 3 => Sum.inr 2
  left_inv := by decide
  right_inv := by decide

/-- The labelling of the four bond coordinates by the graded block space; every block is
one-dimensional, so it agrees with `scalarFlagOrd`. -/
def scalarFlagTau : BlockSpace (fun _ : Unit => 1) oneSlot 3 ≃ Fin 4 where
  toFun x := scalarFlagOrd x.1
  invFun
    | 0 => ⟨Sum.inr 0, 0⟩
    | 1 => ⟨Sum.inr 1, 0⟩
    | 2 => ⟨Sum.inl oneSlotMem, 0⟩
    | 3 => ⟨Sum.inr 2, 0⟩
  left_inv := by decide
  right_inv := by decide

namespace MultiBlockCompression

variable {B : MPSTensor d 4} {c : MPSTensor d 1}

/-- **A four-dimensional tensor with a one-dimensional target and three zero slots.** The
integer gauge `G` with inverse `Ginv` conjugates every letter to `conjInt i`, which is block
upper triangular for `scalarFlagOrd`, carries the scalar target at the third coordinate, and
vanishes on the other three diagonal entries (P5 note, Theorem 7.7(i)–(iii)). -/
noncomputable def ofScalarFlagFour (BInt : Fin d → Matrix (Fin 4) (Fin 4) ℤ)
    (cInt : Fin d → Matrix (Fin 1) (Fin 1) ℤ)
    (hB : ∀ i, B i = complexOfInt (BInt i)) (hc : ∀ i, c i = complexOfInt (cInt i))
    (G Ginv : Matrix (Fin 4) (Fin 4) ℤ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (conjInt : Fin d → Matrix (Fin 4) (Fin 4) ℤ) (hconj : ∀ i, G * BInt i * Ginv = conjInt i)
    (htri : ∀ (i : Fin d) (x y : BlockSpace (fun _ : Unit => 1) oneSlot 3),
      scalarFlagOrd y.1 < scalarFlagOrd x.1 → conjInt i (scalarFlagTau x) (scalarFlagTau y) = 0)
    (htarget : ∀ i, conjInt i (scalarFlagTau ⟨Sum.inl oneSlotMem, 0⟩)
      (scalarFlagTau ⟨Sum.inl oneSlotMem, 0⟩) = cInt i 0 0)
    (hzero : ∀ (i : Fin d) (t : Fin 3),
      conjInt i (scalarFlagTau ⟨Sum.inr t, 0⟩) (scalarFlagTau ⟨Sum.inr t, 0⟩) = 0) :
    MultiBlockCompression B oneSlot (fun _ : Unit => c) where
  z := 3
  ord := scalarFlagOrd
  gauge := gaugeOfMatrix scalarFlagTau (complexOfInt G) (complexOfInt Ginv)
    (by rw [← complexOfInt_mul, hG, complexOfInt_one])
    (by rw [← complexOfInt_mul, hG', complexOfInt_one])
  triangular i x y hxy := by
    rw [conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hB, ← complexOfInt_mul,
      ← complexOfInt_mul, hconj, complexOfInt_apply, Int.cast_eq_zero]
    exact htri i x y hxy
  matched i s := by
    obtain rfl : s = oneSlotMem := eq_oneSlotMem s
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hB,
      ← complexOfInt_mul, ← complexOfInt_mul, hconj, hc, complexOfInt_apply, complexOfInt_apply,
      Int.cast_inj]
    exact htarget i
  unmatched i t := by
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hB,
      ← complexOfInt_mul, ← complexOfInt_mul, hconj, Matrix.zero_apply, complexOfInt_apply,
      Int.cast_eq_zero]
    exact hzero i t

variable (BInt : Fin d → Matrix (Fin 4) (Fin 4) ℤ) (cInt : Fin d → Matrix (Fin 1) (Fin 1) ℤ)
  (hB : ∀ i, B i = complexOfInt (BInt i)) (hc : ∀ i, c i = complexOfInt (cInt i))
  (G Ginv : Matrix (Fin 4) (Fin 4) ℤ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
  (conjInt : Fin d → Matrix (Fin 4) (Fin 4) ℤ) (hconj : ∀ i, G * BInt i * Ginv = conjInt i)
  (htri : ∀ (i : Fin d) (x y : BlockSpace (fun _ : Unit => 1) oneSlot 3),
    scalarFlagOrd y.1 < scalarFlagOrd x.1 → conjInt i (scalarFlagTau x) (scalarFlagTau y) = 0)
  (htarget : ∀ i, conjInt i (scalarFlagTau ⟨Sum.inl oneSlotMem, 0⟩)
    (scalarFlagTau ⟨Sum.inl oneSlotMem, 0⟩) = cInt i 0 0)
  (hzero : ∀ (i : Fin d) (t : Fin 3),
    conjInt i (scalarFlagTau ⟨Sum.inr t, 0⟩) (scalarFlagTau ⟨Sum.inr t, 0⟩) = 0)

/-- The compression out of the bond space of a four-step scalar-flag datum is the third row of
the gauge. -/
theorem left_ofScalarFlagFour :
    (ofScalarFlagFour BInt cInt hB hc G Ginv hG hG' conjInt hconj htri htarget hzero).left
      oneSlotMem = Matrix.of fun (_ : Fin 1) j => (G 2 j : ℂ) := by
  rw [left_gaugeOfMatrix (ofScalarFlagFour BInt cInt hB hc G Ginv hG hG' conjInt hconj htri
    htarget hzero) (hG := by rw [← complexOfInt_mul, hG, complexOfInt_one])
    (hG' := by rw [← complexOfInt_mul, hG', complexOfInt_one]) rfl]
  ext i j
  rfl

/-- The compression into the bond space of a four-step scalar-flag datum is the third column of
the inverse gauge. -/
theorem right_ofScalarFlagFour :
    (ofScalarFlagFour BInt cInt hB hc G Ginv hG hG' conjInt hconj htri htarget hzero).right
      oneSlotMem = Matrix.of fun i (_ : Fin 1) => (Ginv i 2 : ℂ) := by
  rw [right_gaugeOfMatrix (ofScalarFlagFour BInt cInt hB hc G Ginv hG hG' conjInt hconj htri
    htarget hzero) (hG := by rw [← complexOfInt_mul, hG, complexOfInt_one])
    (hG' := by rw [← complexOfInt_mul, hG', complexOfInt_one]) rfl]
  ext i j
  rfl

end MultiBlockCompression

/-! ### Normality certificates -/

/-- **Normality at blocking length two from an integer certificate.** If every matrix unit is,
up to the common nonzero integer factor `m`, an integer combination of the length-two words
`A (a k) * A (b k)`, then the length-two words span the full matrix algebra. -/
theorem isNBlkInjective_two_of_int {D K : ℕ} {A : MPSTensor d D}
    (AInt : Fin d → Matrix (Fin D) (Fin D) ℤ) (hA : ∀ i, A i = complexOfInt (AInt i))
    (a b : Fin K → Fin d) (T : Fin D → Fin D → Fin K → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : ∀ x y, ∑ k, T x y k • (AInt (a k) * AInt (b k)) = m • Matrix.single x y 1) :
    Kraus.IsNBlkInjective A 2 := by
  rw [Kraus.IsNBlkInjective, eq_top_iff]
  intro X _
  have hword : ∀ k, A (a k) * A (b k) ∈ Kraus.wordSpan A 2 := fun k => by
    simpa [Kraus.evalWord] using Kraus.evalWord_mem_wordSpan A [a k, b k]
  have hsingle : ∀ x y : Fin D,
      complexOfInt (Matrix.single x y (1 : ℤ)) = Matrix.single x y (1 : ℂ) := by
    intro x y
    ext p q
    simp [complexOfInt, Matrix.single_apply]
  have hunit : ∀ x y, Matrix.single x y (1 : ℂ) ∈ Kraus.wordSpan A 2 := by
    intro x y
    have hsum : ∑ k, (T x y k : ℂ) • (A (a k) * A (b k)) =
        (m : ℂ) • Matrix.single x y 1 := by
      have hc := congrArg complexOfInt (h x y)
      rw [complexOfInt_sum, complexOfInt_zsmul, hsingle] at hc
      rw [← hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [complexOfInt_zsmul, complexOfInt_mul, hA, hA]
    have hmem : ∑ k, (T x y k : ℂ) • (A (a k) * A (b k)) ∈ Kraus.wordSpan A 2 :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hword k)
    rw [hsum] at hmem
    have hinv := Submodule.smul_mem _ (m : ℂ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hm), one_smul] at hinv
  rw [Matrix.matrix_eq_sum_single X]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      Submodule.smul_mem _ (X i j) (hunit i j)

/-- Nonzero scalar multiplication preserves normality. -/
theorem isNormal_smul {D : ℕ} {A : MPSTensor d D} (hA : Kraus.IsNormal A) {c : ℂ}
    (hc : c ≠ 0) : Kraus.IsNormal (c • A) := by
  obtain ⟨N, hN, h⟩ := hA
  exact ⟨N, hN, isNBlkInjective_smul c hc h⟩

/-! ### Integer certificates for vanishing intertwiner spaces -/

/-- A vector annihilated by an integer matrix with an integer left inverse up to a nonzero
factor is zero. -/
theorem eq_zero_of_complexOfInt_mulVec_eq_zero {D : ℕ} (K K' : Matrix (Fin D) (Fin D) ℤ)
    (m : ℤ) (hm : m ≠ 0) (hK : K' * K = m • 1) (v : Fin D → ℂ)
    (hv : complexOfInt K *ᵥ v = 0) : v = 0 := by
  have hmv : (m : ℂ) • v = 0 := by
    have hKK := congrArg (fun X => complexOfInt X *ᵥ v) hK
    simp only [complexOfInt_mul, complexOfInt_zsmul, complexOfInt_one, ← Matrix.mulVec_mulVec,
      hv, Matrix.mulVec_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hKK
    exact hKK.symm
  exact (smul_eq_zero.mp hmv).resolve_left (Int.cast_ne_zero.mpr hm)

/-- **No nonzero right sitewise intertwiner, from an integer certificate.** If the rows `r k` of
the letters `ℓ k` of the sitewise system `B i *ᵥ v = c i • v` form an integer matrix with an
integer left inverse up to a nonzero factor, the only solution is `v = 0`. -/
theorem right_intertwiner_eq_zero_of_int {D : ℕ} {B : MPSTensor d D} {c : MPSTensor d 1}
    (BInt : Fin d → Matrix (Fin D) (Fin D) ℤ) (cInt : Fin d → Matrix (Fin 1) (Fin 1) ℤ)
    (hB : ∀ i, B i = complexOfInt (BInt i)) (hc : ∀ i, c i = complexOfInt (cInt i))
    (ℓ : Fin D → Fin d) (r : Fin D → Fin D) (K' : Matrix (Fin D) (Fin D) ℤ) (m : ℤ)
    (hm : m ≠ 0)
    (hK : K' * Matrix.of (fun k j => BInt (ℓ k) (r k) j - if r k = j then cInt (ℓ k) 0 0 else 0)
      = m • 1)
    (v : Fin D → ℂ) (h : ∀ i, B i *ᵥ v = c i 0 0 • v) : v = 0 := by
  refine eq_zero_of_complexOfInt_mulVec_eq_zero _ K' m hm hK v ?_
  funext k
  have hk := congrFun (h (ℓ k)) (r k)
  rw [hB, hc] at hk
  simp only [Matrix.mulVec, dotProduct, complexOfInt_apply, Pi.smul_apply, smul_eq_mul] at hk
  simp only [Matrix.mulVec, dotProduct, complexOfInt_apply, Matrix.of_apply, Int.cast_sub,
    Int.cast_ite, Int.cast_zero, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply, hk, sub_self]

/-- **No nonzero left sitewise intertwiner, from an integer certificate.** If the columns `q k`
of the letters `ℓ k` of the sitewise system `u ᵥ* B i = c i • u` form an integer matrix with
an integer left inverse up to a nonzero factor, the only solution is `u = 0`. -/
theorem left_intertwiner_eq_zero_of_int {D : ℕ} {B : MPSTensor d D} {c : MPSTensor d 1}
    (BInt : Fin d → Matrix (Fin D) (Fin D) ℤ) (cInt : Fin d → Matrix (Fin 1) (Fin 1) ℤ)
    (hB : ∀ i, B i = complexOfInt (BInt i)) (hc : ∀ i, c i = complexOfInt (cInt i))
    (ℓ : Fin D → Fin d) (q : Fin D → Fin D) (K' : Matrix (Fin D) (Fin D) ℤ) (m : ℤ)
    (hm : m ≠ 0)
    (hK : K' * Matrix.of (fun k p => BInt (ℓ k) p (q k) - if p = q k then cInt (ℓ k) 0 0 else 0)
      = m • 1)
    (u : Fin D → ℂ) (h : ∀ i, u ᵥ* B i = c i 0 0 • u) : u = 0 := by
  refine eq_zero_of_complexOfInt_mulVec_eq_zero _ K' m hm hK u ?_
  funext k
  have hk := congrFun (h (ℓ k)) (q k)
  rw [hB, hc] at hk
  simp only [Matrix.vecMul, dotProduct, complexOfInt_apply, Pi.smul_apply, smul_eq_mul] at hk
  simp only [Matrix.mulVec, dotProduct, complexOfInt_apply, Matrix.of_apply, Int.cast_sub,
    Int.cast_ite, Int.cast_zero, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply]
  rw [sub_eq_zero, ← hk]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

end MPSTensor
