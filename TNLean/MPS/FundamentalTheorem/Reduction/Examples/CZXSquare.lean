/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXTensor
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# Example D: the square of an anomalous `ℤ/2` symmetry

A machine-checked instance of the multi-block asymmetric compression theorem (P5 note,
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`, Example D,
`ex:p5ft-czx`; verified numerically by `checks/p5_examples_verify.py`, section D).

The CZX symmetry satisfies `U_L² = (-1)^L id` at every length. The stacked product tensor
`B^{ij} = ∑_m M^{im} ⊗ M^{mj}` of bond dimension four therefore has the word traces of the
single one-dimensional normal target `δ` carried with the weight `-1`, and the theorem applies
with three zero slots. The compression is genuinely asymmetric: the target has bond dimension
one, the source bond dimension four, and both sitewise intertwiner spaces vanish, so the
word-level compression is the strongest local relation available for this tensor.

The flag is the one produced by hand from the two rank-one letters of `B`: the line spanned by
`(1,0,0,-1)` is annihilated by every letter, the plane it spans together with
`(1,1,-1,-1)` is the image of every letter, and the quotient of the plane by the line carries
the weight `-1`. The remaining two steps of the flag are arbitrary completions, on which every
letter acts as zero.

## Main results

* `CZXCompression.czxSquare_compression`: the multi-block compression datum of Theorem 7.7.
* `CZXCompression.czxSquare_trace_evalWord`: the word-trace identity `U_L² = (-1)^L id`.
* `CZXCompression.czxSquare_isReduction`: the explicit compression pair of the note,
  `W = (0,0,-1,0)` and `V = (1,1,-1,-1)ᵀ`, with `W V = 1`.
* `CZXCompression.czxSquare_evalWord_remainder_eq_zero`: the remainder of the compression is
  nilpotent of length four.
* `CZXCompression.czxSquare_dim_eq`: the dimension count `4 = 1 + 3`.
* `CZXCompression.czxSquare_right_intertwiner_eq_zero`,
  `CZXCompression.czxSquare_left_intertwiner_eq_zero`: both sitewise intertwiner spaces vanish.
-/

noncomputable section

open scoped Matrix

namespace CZXCompression

open MPSTensor

/-! ### The target family and the flag -/

/-- The single slot of Example D. -/
abbrev squareSlots : Finset Unit := {()}

/-- The bond dimension of the single slot of Example D. -/
abbrev squareDim : Unit → ℕ := fun _ => 1

/-- The single target of Example D: the bond-one identity tensor carried with the weight `-1`
(P5 note, `ex:p5ft-czx`). -/
def czxSquareTarget : (s : Unit) → MPSTensor 4 (squareDim s) := fun _ => (-1 : ℂ) • identityMPS

theorem czxSquareTarget_eq (s : Unit) (a : Fin 4) :
    czxSquareTarget s a = complexOfInt (negIdentityIntMPS a) :=
  negIdentityMPS_eq a

/-- The change of bond coordinates of Example D: its columns are, in the order of the flag,
`(1,0,0,-1)`, `(1,1,-1,-1)` and two arbitrary completions. This matrix is its inverse. -/
def czxSquareGaugeInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, -1; 0, 0, -1, 0; 1, 0, 0, 1; 0, 1, 1, 0]

/-- The inverse change of bond coordinates of Example D, whose columns are the basis adapted
to the flag. -/
def czxSquareGaugeInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 1, 0; 0, 1, 0, 1; 0, -1, 0, 0; -1, -1, 0, 0]

theorem czxSquareGauge_mul_inv : czxSquareGaugeInt * czxSquareGaugeInvInt = 1 := by decide

theorem czxSquareGaugeInv_mul : czxSquareGaugeInvInt * czxSquareGaugeInt = 1 := by decide

theorem czxSquareGaugeComplex_mul_inv :
    complexOfInt czxSquareGaugeInt * complexOfInt czxSquareGaugeInvInt = 1 := by
  rw [← complexOfInt_mul, czxSquareGauge_mul_inv, complexOfInt_one]

theorem czxSquareGaugeComplex_inv_mul :
    complexOfInt czxSquareGaugeInvInt * complexOfInt czxSquareGaugeInt = 1 := by
  rw [← complexOfInt_mul, czxSquareGaugeInv_mul, complexOfInt_one]

/-- The block ordering of Example D: a zero slot at position `0`, the weighted target at
position `1`, and two more zero slots at positions `2` and `3`. -/
def czxSquareOrd : BlockIndex squareSlots 3 ≃ Fin 4 where
  toFun
    | Sum.inl _ => 1
    | Sum.inr t => ![0, 2, 3] t
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inl ⟨(), Finset.mem_singleton_self ()⟩
    | 2 => Sum.inr 1
    | 3 => Sum.inr 2
  left_inv := by decide
  right_inv := by decide

/-- The labelling of the four bond coordinates of Example D by the graded block space; each
block is one-dimensional, so it agrees with `czxSquareOrd`. -/
def czxSquareTau : BlockSpace squareDim squareSlots 3 ≃ Fin 4 where
  toFun x := czxSquareOrd x.1
  invFun
    | 0 => ⟨Sum.inr 0, 0⟩
    | 1 => ⟨Sum.inl ⟨(), Finset.mem_singleton_self ()⟩, 0⟩
    | 2 => ⟨Sum.inr 1, 0⟩
    | 3 => ⟨Sum.inr 2, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The gauge of Example D. -/
def czxSquareGauge : (Fin 4 → ℂ) ≃ₗ[ℂ] (BlockSpace squareDim squareSlots 3 → ℂ) :=
  gaugeOfMatrix czxSquareTau (complexOfInt czxSquareGaugeInt) (complexOfInt czxSquareGaugeInvInt)
    czxSquareGaugeComplex_mul_inv czxSquareGaugeComplex_inv_mul

/-- The letters of Example D in the block coordinates: block upper triangular, with the weight
`-1` on the diagonal of the second block and zero on the other three. -/
def czxSquareConjInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 2, 0, 2; 0, -1, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0]

theorem czxSquare_conj_int (i : Fin 4) :
    czxSquareGaugeInt * czxSquareInt i * czxSquareGaugeInvInt = czxSquareConjInt i := by
  revert i
  decide

theorem czxSquare_conjMatrix (i : Fin 4) :
    conjMatrix czxSquareGauge (czxSquare i) =
      (complexOfInt (czxSquareConjInt i)).submatrix czxSquareTau czxSquareTau := by
  rw [czxSquareGauge, conjMatrix_gaugeOfMatrix, czxSquare_eq, ← complexOfInt_mul,
    ← complexOfInt_mul, czxSquare_conj_int]

/-! ### The compression datum -/

/-- The single slot of Example D as an element of the slot subtype. -/
abbrev squareSlot : {s // s ∈ squareSlots} := ⟨(), Finset.mem_singleton_self ()⟩

private theorem czxSquare_triangular_int (i : Fin 4)
    (x y : BlockSpace squareDim squareSlots 3) (h : czxSquareOrd y.1 < czxSquareOrd x.1) :
    czxSquareConjInt i (czxSquareTau x) (czxSquareTau y) = 0 := by
  revert i x y
  decide

private theorem czxSquare_matched_int (i : Fin 4) (p q : Fin 1) :
    czxSquareConjInt i (czxSquareTau ⟨Sum.inl squareSlot, p⟩)
        (czxSquareTau ⟨Sum.inl squareSlot, q⟩) = negIdentityIntMPS i p q := by
  obtain rfl : p = 0 := Subsingleton.elim p 0
  obtain rfl : q = 0 := Subsingleton.elim q 0
  revert i
  decide

private theorem czxSquare_unmatched_int (i : Fin 4) (t : Fin 3) (p q : Fin 1) :
    czxSquareConjInt i (czxSquareTau ⟨Sum.inr t, p⟩) (czxSquareTau ⟨Sum.inr t, q⟩) = 0 := by
  revert i t p q
  decide

/-- **The multi-block asymmetric compression datum of Example D** (P5 note, Theorem 7.7,
clauses (i)–(iii), for `ex:p5ft-czx`). -/
def czxSquare_compression : MultiBlockCompression czxSquare squareSlots czxSquareTarget where
  z := 3
  ord := czxSquareOrd
  gauge := czxSquareGauge
  triangular i x y h := by
    rw [czxSquare_conjMatrix, Matrix.submatrix_apply, complexOfInt_apply, Int.cast_eq_zero]
    exact czxSquare_triangular_int i x y h
  matched i s := by
    have hs : s = squareSlot := Subtype.ext (Subsingleton.elim _ _)
    subst hs
    ext p q
    rw [Matrix.blockDiag'_apply, czxSquare_conjMatrix, Matrix.submatrix_apply,
      complexOfInt_apply, czxSquareTarget_eq, complexOfInt_apply, Int.cast_inj]
    exact czxSquare_matched_int i p q
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, czxSquare_conjMatrix, Matrix.submatrix_apply,
      complexOfInt_apply, Matrix.zero_apply, Int.cast_eq_zero]
    exact czxSquare_unmatched_int i t p q

/-! ### Consequences -/

/-- **The word-trace identity of Example D**: at every positive length the stacked tensor has
`(-1)^L` times the word traces of the bond-one identity tensor. This is `U_L² = (-1)^L id` at
the level of traces (P5 note, `ex:p5ft-czx`). -/
theorem czxSquare_trace_evalWord (w : List (Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord czxSquare w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord identityMPS w) := by
  have h := czxSquare_compression.trace_evalWord_eq_sum w hw
  rw [Finset.sum_singleton, czxSquareTarget,
    show ((-1 : ℂ) • identityMPS) = fun i => (-1 : ℂ) • identityMPS i from rfl,
    Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul] at h
  exact h

/-- The left compression witness of the note, `W = (0,0,-1,0)` (P5 note, `ex:p5ft-czx`). -/
def czxSquareLeft : Matrix (Fin 1) (Fin 4) ℂ := !![0, 0, -1, 0]

/-- The right compression witness of the note, `V = (1,1,-1,-1)ᵀ` (P5 note,
`ex:p5ft-czx`). -/
def czxSquareRight : Matrix (Fin 4) (Fin 1) ℂ := !![1; 1; -1; -1]

theorem czxSquare_left_eq : czxSquare_compression.left squareSlot = czxSquareLeft := by
  rw [MultiBlockCompression.left_gaugeOfMatrix czxSquare_compression
    (hG := czxSquareGaugeComplex_mul_inv) (hG' := czxSquareGaugeComplex_inv_mul) rfl]
  ext i y
  change ((czxSquareGaugeInt 1 y : ℤ) : ℂ) = czxSquareLeft i y
  fin_cases i
  fin_cases y <;> norm_num [czxSquareGaugeInt, czxSquareLeft]

theorem czxSquare_right_eq : czxSquare_compression.right squareSlot = czxSquareRight := by
  rw [MultiBlockCompression.right_gaugeOfMatrix czxSquare_compression
    (hG := czxSquareGaugeComplex_mul_inv) (hG' := czxSquareGaugeComplex_inv_mul) rfl]
  ext x j
  change ((czxSquareGaugeInvInt x 1 : ℤ) : ℂ) = czxSquareRight x j
  fin_cases j
  fin_cases x <;> norm_num [czxSquareGaugeInvInt, czxSquareRight]

/-- **The explicit compression pair of Example D** (P5 note, `ex:p5ft-czx`): the note's
witnesses `W = (0,0,-1,0)` and `V = (1,1,-1,-1)ᵀ` compress every word of the stacked tensor
onto the corresponding word of the weighted identity block. -/
theorem czxSquare_isReduction :
    IsReduction czxSquare (czxSquareTarget ()) czxSquareLeft czxSquareRight := by
  have h := czxSquare_compression.isReduction squareSlot
  rwa [czxSquare_left_eq, czxSquare_right_eq] at h

/-- The note's witnesses satisfy `W V = 1`. -/
theorem czxSquareLeft_mul_right : czxSquareLeft * czxSquareRight = 1 :=
  czxSquare_isReduction.mul_eq_one

/-- **Nilpotency of the remainder of Example D** (P5 note, `ex:p5ft-czx`, with the nilpotency
length `z + 1 = 4` of Theorem 7.7(vi)). -/
theorem czxSquare_evalWord_remainder_eq_zero (w : List (Fin 4)) (hw : 4 ≤ w.length) :
    Kraus.evalWord
      (fun i => czxSquare i - czxSquareRight * czxSquareTarget () i * czxSquareLeft) w = 0 := by
  have hsum : (fun i => czxSquare i - czxSquareRight * czxSquareTarget () i * czxSquareLeft) =
      czxSquare_compression.remainder := by
    funext i
    rw [MultiBlockCompression.remainder,
      Finset.sum_eq_single_of_mem squareSlot (Finset.mem_univ squareSlot)
        fun b _ hb => absurd (Subtype.ext (Subsingleton.elim b.1 squareSlot.1)) hb,
      czxSquare_left_eq, czxSquare_right_eq]
  rw [hsum]
  refine czxSquare_compression.evalWord_remainder_eq_zero w ?_
  change (1 : ℕ) + 3 ≤ w.length
  omega

/-- **The dimension count of Example D**: `4 = 1 + 3` (P5 note, Theorem 7.7(vii)). -/
theorem czxSquare_dim_eq : (4 : ℕ) = ∑ s ∈ squareSlots, squareDim s + 3 :=
  czxSquare_compression.dim_eq

/-! ### Absence of sitewise intertwiners -/

theorem czxSquare_apply_zero :
    czxSquare 0 = !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0] := by
  rw [czxSquare_eq]
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [czxSquareInt, complexOfInt]

theorem czxSquare_apply_three :
    czxSquare 3 = !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0] := by
  rw [czxSquare_eq]
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [czxSquareInt, complexOfInt]

private theorem czxSquareTarget_scalar_zero : czxSquareTarget () 0 0 0 = (-1 : ℂ) := by
  rw [czxSquareTarget_eq]
  norm_num [negIdentityIntMPS, identityIntMPS, complexOfInt]

private theorem czxSquareTarget_scalar_three : czxSquareTarget () 3 0 0 = (-1 : ℂ) := by
  rw [czxSquareTarget_eq]
  norm_num [negIdentityIntMPS, identityIntMPS, complexOfInt]

/-- **No nonzero right sitewise intertwiner in Example D** (P5 note, `ex:p5ft-czx`). -/
theorem czxSquare_right_intertwiner_eq_zero (v : Fin 4 → ℂ)
    (h : ∀ i, czxSquare i *ᵥ v = czxSquareTarget () i 0 0 • v) : v = 0 := by
  have h0 := h 0
  have h3 := h 3
  rw [czxSquare_apply_zero, czxSquareTarget_scalar_zero] at h0
  rw [czxSquare_apply_three, czxSquareTarget_scalar_three] at h3
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e3 := congrFun h0 3
  have f0 := congrFun h3 0
  have f2 := congrFun h3 2
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one, Fin.sum_univ_four, zero_mul,
    one_mul, neg_mul, zero_add, add_zero, Pi.smul_apply, smul_eq_mul] at e0 e1 e3 f0 f2
  have hv1 : v 1 = 0 := by linear_combination (e1 + f0 - e0) / 2
  have hv2 : v 2 = 0 := by linear_combination f2 - hv1
  have hv0 : v 0 = 0 := by linear_combination e0 - hv2
  have hv3 : v 3 = 0 := by linear_combination e3 + hv2
  funext k
  fin_cases k
  exacts [hv0, hv1, hv2, hv3]

/-- **No nonzero left sitewise intertwiner in Example D** (P5 note, `ex:p5ft-czx`). -/
theorem czxSquare_left_intertwiner_eq_zero (u : Fin 4 → ℂ)
    (h : ∀ i, u ᵥ* czxSquare i = czxSquareTarget () i 0 0 • u) : u = 0 := by
  have h0 := h 0
  have h3 := h 3
  rw [czxSquare_apply_zero, czxSquareTarget_scalar_zero] at h0
  rw [czxSquare_apply_three, czxSquareTarget_scalar_three] at h3
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e3 := congrFun h0 3
  have f2 := congrFun h3 2
  simp only [Matrix.vecMul_apply_eq_sum, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one, Fin.sum_univ_four, mul_zero,
    add_zero, Pi.smul_apply, smul_eq_mul, neg_one_mul] at e0 e1 e3 f2
  have hu0 : u 0 = 0 := by linear_combination e0
  have hu1 : u 1 = 0 := by linear_combination e1
  have hu3 : u 3 = 0 := by linear_combination e3
  have hu2 : u 2 = 0 := by linear_combination f2
  funext k
  fin_cases k
  exacts [hu0, hu1, hu2, hu3]

end CZXCompression
