/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.ExplicitGauge
import TNLean.MPS.Examples.MultiBlock.Running

/-!
# Sharpness of the one-block bound for one and two zero slots

Let `d = 1`, let the block be `C = (1)`, and let `B = [[1, 1], [0, 0]]` act on `ℂ²`, so that
`D_B - D_C = 1` and every reduction of `B` onto `C` has one zero slot. The tensor has two reductions
onto `C` (*The asymmetric fundamental theorem of matrix product states*, Example 6.15, the case
`z = 1` of Example 6.10):

* the identity gauge, with the block first: the flag `0 ⊂ ℂ e₁ ⊂ ℂ²`, reading map `W = (1, 0)` and
  injection `V = e₁`;
* the gauge `g' = [[0, -1], [1, 1]]`, with inverse `[[1, 1], [-1, 0]]` and
  `g' B g'⁻¹ = [[0, 0], [0, 1]]`, with the zero slot first: the flag `0 ⊂ ℂ (e₁ - e₂) ⊂ ℂ²`, reading
  map `W' = (1, 1)` and injection `V' = e₁`.

The reading maps are not proportional, so the identity `W' B^w = λ W B^w` of the one-block theorem
(blueprint `cor:asym_uniq_one_block`, *Bare uniqueness at the ends of the flag; the one-block
theorem*) fails for the empty word, while it holds with `λ = 1` for every word of length at least
`1 = D_B - D_C`. The bound of the one-block theorem therefore cannot be lowered for `z = 1`.

The case `z = 2` of *The asymmetric fundamental theorem of matrix product states*, Example 6.10,
takes `B = [[1, 1, 0], [0, 0, 1], [0, 0, 0]]` on `ℂ³`, that is `B e₀ = e₀`, `B e₁ = e₀`,
`B e₂ = e₁`, so that `D_B - D_C = 2`. Its two reductions onto `C = (1)` are

* the identity gauge, in the order block, zero slot, zero slot: reading map `W = (1, 0, 0)` and
  injection `V = e₀`;
* the gauge `g̃ = [[0, -1, -1], [0, 0, -1], [1, 1, 1]]`, whose inverse has the columns
  `f₁ = e₀ - e₁`, `f₂ = e₁ - e₂`, `e₀`, with `g̃ B g̃⁻¹ = [[0, 1, 0], [0, 0, 0], [0, 0, 1]]`, in the
  order zero slot, zero slot, block: reading map `W̃ = (1, 1, 1)` and injection `Ṽ = e₀`.

Here `W B = (1, 1, 0)` and `W̃ B = (1, 1, 1)` are not proportional, so the identity fails at
`|w| = 1 = z - 1`, while `B² = [[1, 1, 1], [0, 0, 0], [0, 0, 0]]` gives `W B² = W̃ B² = (1, 1, 1)`,
and the identity holds with `λ = 1` for every word of length at least `2 = D_B - D_C`. The bound
therefore cannot be lowered for `z = 2` either. The general case `z ≥ 1` (*The asymmetric
fundamental theorem of matrix product states*, Example 6.10) is the last section: `B` on `ℂ^{1+z}`
with `B e₀ = e₀`, `B e_j = e_{j-1}`; `W Bⁿ` and `W̃ Bⁿ` are proportional exactly when `n ≥ z`.

## Main definitions

* `MultiBlockExamples.SharpnessOneBlock.firstCompression`,
  `MultiBlockExamples.SharpnessOneBlock.lastCompression`: the two reductions for `z = 1`.
* `MultiBlockExamples.SharpnessOneBlock.firstCompressionTwo`,
  `MultiBlockExamples.SharpnessOneBlock.lastCompressionTwo`: the two reductions for `z = 2`.

## Main results

* `MultiBlockExamples.SharpnessOneBlock.not_exists_left_eq_smul`: the two reading maps are not
  proportional.
* `MultiBlockExamples.SharpnessOneBlock.left_mul_evalWord_eq`: `W' B^w = W B^w` for every nonempty
  word.
* `MultiBlockExamples.SharpnessOneBlock.right_eq`: the two injections agree.
* `MultiBlockExamples.SharpnessOneBlock.not_exists_left_mul_eq_smul_two`: for `z = 2`, `W̃ B^w` and
  `W B^w` are not proportional for words of length one.
* `MultiBlockExamples.SharpnessOneBlock.left_mul_sq_eq_two`,
  `MultiBlockExamples.SharpnessOneBlock.left_mul_evalWord_eq_two`: for `z = 2`, `W̃ B^w = W B^w` for
  words of length two, and of every length at least two.
* `MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_first`,
  `MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_last`,
  `MultiBlockExamples.SharpnessOneBlock.rowE0_mul_pow_and_rowOnes_mul_pow`,
  `MultiBlockExamples.SharpnessOneBlock.exists_rowOnes_mul_pow_eq_smul_iff`,
  `MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul`,
  `MultiBlockExamples.SharpnessOneBlock.pow_mul_right_eq_of_eq_colE0`: every `z ≥ 1`.
* `MultiBlockExamples.SharpnessOneBlock.right_eq_two`: for `z = 2`, the two injections agree.

## References

*The asymmetric fundamental theorem of matrix product states*, Examples 6.10 and 6.15; blueprint
`cor:asym_uniq_one_block`, *Bare uniqueness at the ends of the flag; the one-block theorem*.
-/

open scoped Matrix

namespace MultiBlockExamples.SharpnessOneBlock

open MPSTensor

/-- The integer matrix of the single letter, `B = [[1, 1], [0, 0]]` (*The asymmetric fundamental
theorem of matrix product states*, Example 6.15). -/
def bInt : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 0]

/-- The tensor of *The asymmetric fundamental theorem of matrix product states*, Example 6.15: one
letter, `B = [[1, 1], [0, 0]]`. -/
noncomputable def tensorB : MPSTensor 1 2 := fun _ => complexOfInt bInt

/-- The block `C = (1)`, indexed by the single label. -/
noncomputable def blockC : ∀ _ : Unit, MPSTensor 1 1 := fun _ _ => 1

/-- The block ordering with the block first and the zero slot second. -/
def firstOrd : BlockIndex oneSlot 1 ≃ Fin 2 where
  toFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  invFun
    | 0 => Sum.inl oneSlotMem
    | 1 => Sum.inr 0
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates with the block first and the zero slot second. -/
def firstTau : BlockSpace (fun _ : Unit => 1) oneSlot 1 ≃ Fin 2 where
  toFun x := firstOrd x.1
  invFun
    | 0 => ⟨Sum.inl oneSlotMem, 0⟩
    | 1 => ⟨Sum.inr 0, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The block ordering with the zero slot first and the block second. -/
def lastOrd : BlockIndex oneSlot 1 ≃ Fin 2 where
  toFun
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inl oneSlotMem
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates with the zero slot first and the block second. -/
def lastTau : BlockSpace (fun _ : Unit => 1) oneSlot 1 ≃ Fin 2 where
  toFun x := lastOrd x.1
  invFun
    | 0 => ⟨Sum.inr 0, 0⟩
    | 1 => ⟨Sum.inl oneSlotMem, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- A reduction of `B` onto `C = (1)` with one zero slot from an integer gauge `G` with inverse
`Ginv` conjugating `B` to a matrix `K` that is upper triangular for the ordering `ord`, with `1` at
the block and `0` at the zero slot (blueprint `thm:asym_multiblock`, *Multi-block asymmetric
compression theorem*, clauses (i)–(iii)). -/
noncomputable def compressionOf (ord : BlockIndex oneSlot 1 ≃ Fin 2)
    (τ : BlockSpace (fun _ : Unit => 1) oneSlot 1 ≃ Fin 2) (G Ginv K : Matrix (Fin 2) (Fin 2) ℤ)
    (hG : G * Ginv = 1) (hG' : Ginv * G = 1) (hK : G * bInt * Ginv = K)
    (htri : ∀ x y : BlockSpace (fun _ : Unit => 1) oneSlot 1, ord y.1 < ord x.1 →
      K (τ x) (τ y) = 0)
    (htarget : K (τ ⟨Sum.inl oneSlotMem, 0⟩) (τ ⟨Sum.inl oneSlotMem, 0⟩) = 1)
    (hzero : K (τ ⟨Sum.inr 0, 0⟩) (τ ⟨Sum.inr 0, 0⟩) = 0) :
    MultiBlockCompression tensorB oneSlot blockC :=
  MultiBlockCompression.ofRing (Int.castRingHom ℂ) ord τ
    (gaugeOfRingMatrix _ τ G Ginv hG hG') (fun _ => K)
    (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix (Int.castRingHom ℂ) τ hG hG'
        (show tensorB i = complexOfRing (Int.castRingHom ℂ) bInt from rfl), hK])
    (fun _ _ => 1) (fun _ _ => (complexOfRing_one _).symm) (fun _ => htri)
    (fun _ s p q => by
      obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      obtain rfl : p = 0 := Subsingleton.elim p 0
      obtain rfl : q = 0 := Subsingleton.elim q 0
      exact htarget.trans (Matrix.one_apply_eq 0).symm)
    fun _ t p q => by
      obtain rfl : t = 0 := Subsingleton.elim t 0
      obtain rfl : p = 0 := Subsingleton.elim p 0
      obtain rfl : q = 0 := Subsingleton.elim q 0
      exact hzero

/-- The gauge of the reduction with the zero slot first, `g' = [[0, -1], [1, 1]]`. -/
def gInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 1]

/-- The inverse gauge `g'⁻¹ = [[1, 1], [-1, 0]]`; its columns `e₁ - e₂` and `e₁` are the
basis adapted to the flag `0 ⊂ ℂ (e₁ - e₂) ⊂ ℂ²`. -/
def gInvInt : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; -1, 0]

/-- **The reduction with the block first** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.15): the identity gauge and the flag `0 ⊂ ℂ e₁ ⊂ ℂ²`. -/
noncomputable def firstCompression : MultiBlockCompression tensorB oneSlot blockC :=
  compressionOf firstOrd firstTau 1 1 bInt (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The reduction with the zero slot first** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.15): the gauge `g' = [[0, -1], [1, 1]]`, with
`g' B g'⁻¹ = [[0, 0], [0, 1]]`, and the flag `0 ⊂ ℂ (e₁ - e₂) ⊂ ℂ²`. -/
noncomputable def lastCompression : MultiBlockCompression tensorB oneSlot blockC :=
  compressionOf lastOrd lastTau gInt gInvInt !![0, 0; 0, 1] (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)


section Maps

variable (ord : BlockIndex oneSlot 1 ≃ Fin 2)
  (τ : BlockSpace (fun _ : Unit => 1) oneSlot 1 ≃ Fin 2) (G Ginv K : Matrix (Fin 2) (Fin 2) ℤ)
  (hG : G * Ginv = 1) (hG' : Ginv * G = 1) (hK : G * bInt * Ginv = K)
  (htri : ∀ x y : BlockSpace (fun _ : Unit => 1) oneSlot 1, ord y.1 < ord x.1 →
    K (τ x) (τ y) = 0)
  (htarget : K (τ ⟨Sum.inl oneSlotMem, 0⟩) (τ ⟨Sum.inl oneSlotMem, 0⟩) = 1)
  (hzero : K (τ ⟨Sum.inr 0, 0⟩) (τ ⟨Sum.inr 0, 0⟩) = 0)

/-- The reading map of the reduction built from an integer gauge `G` is the row of `G` at the
block coordinate. -/
theorem left_compressionOf :
    (compressionOf ord τ G Ginv K hG hG' hK htri htarget hzero).left oneSlotMem =
      Matrix.of fun (_ : Fin 1) j => (G (τ ⟨Sum.inl oneSlotMem, 0⟩) j : ℂ) := by
  rw [MultiBlockCompression.left_gaugeOfMatrix
    (compressionOf ord τ G Ginv K hG hG' hK htri htarget hzero)
    (hG := complexOfRing_mul_eq_one _ hG) (hG' := complexOfRing_mul_eq_one _ hG') rfl]
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  rfl

/-- The injection of the reduction built from an integer gauge `G` with inverse `Ginv` is the
column of `Ginv` at the block coordinate. -/
theorem right_compressionOf :
    (compressionOf ord τ G Ginv K hG hG' hK htri htarget hzero).right oneSlotMem =
      Matrix.of fun i (_ : Fin 1) => (Ginv i (τ ⟨Sum.inl oneSlotMem, 0⟩) : ℂ) := by
  rw [MultiBlockCompression.right_gaugeOfMatrix
    (compressionOf ord τ G Ginv K hG hG' hK htri htarget hzero)
    (hG := complexOfRing_mul_eq_one _ hG) (hG' := complexOfRing_mul_eq_one _ hG') rfl]
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  rfl

end Maps

/-- The reading map of the reduction with the block first is `W = (1, 0)`. -/
theorem left_firstCompression : firstCompression.left oneSlotMem = !![1, 0] := by
  rw [firstCompression, left_compressionOf]
  ext i j
  fin_cases i; fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Int.cast_eq_one]
    decide
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_eq_zero]
    decide

/-- The reading map of the reduction with the zero slot first is `W' = (1, 1)`. -/
theorem left_lastCompression : lastCompression.left oneSlotMem = !![1, 1] := by
  rw [lastCompression, left_compressionOf]
  ext i j
  fin_cases i; fin_cases j <;> simp [gInt, lastTau, lastOrd]

/-- **The reading maps are not proportional** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.15): `W' e₂ = 1` while `W e₂ = 0`. So the identity `W' B^w = λ W B^w` of the
one-block theorem (blueprint `cor:asym_uniq_one_block`) fails for the empty word, of length
`0 < 1 = D_B - D_C`.
-/
theorem not_exists_left_eq_smul :
    ¬ ∃ c : ℂ, lastCompression.left oneSlotMem = c • firstCompression.left oneSlotMem := by
  rintro ⟨c, hc⟩
  have h := congrFun (congrFun hc 0) 1
  rw [left_firstCompression, left_lastCompression] at h
  simp at h

/-- `W' B = W B` (*The asymmetric fundamental theorem of matrix product states*, Example 6.15): `B`
maps `ℂ²` into `U = ℂ e₁`, where the two reading maps agree. -/
theorem left_mul_eq (i : Fin 1) :
    lastCompression.left oneSlotMem * tensorB i = firstCompression.left oneSlotMem * tensorB i := by
  rw [left_firstCompression, left_lastCompression]
  ext a b
  fin_cases a
  fin_cases b <;> simp [tensorB, bInt, Matrix.mul_apply, Fin.sum_univ_two, complexOfRing_apply]

/-- **The one-block identity from length one on** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.15 and the one-block theorem (blueprint `cor:asym_uniq_one_block`) with
`z = 1`): `W' B^w = W B^w` for every nonempty word. -/
theorem left_mul_evalWord_eq (w : List (Fin 1)) (hw : w ≠ []) :
    lastCompression.left oneSlotMem * Kraus.evalWord tensorB w =
      firstCompression.left oneSlotMem * Kraus.evalWord tensorB w := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  rw [Kraus.evalWord, ← Matrix.mul_assoc, ← Matrix.mul_assoc, left_mul_eq]

/-- **The injections agree** (*The asymmetric fundamental theorem of matrix product states*, Example
6.15): `V' = V = e₁`. -/
theorem right_eq : lastCompression.right oneSlotMem = firstCompression.right oneSlotMem := by
  rw [lastCompression, right_compressionOf, firstCompression, right_compressionOf]
  ext i j
  fin_cases i <;> rfl

/-! ### Two zero slots -/

/-- The integer matrix of the single letter for two zero slots,
`B = [[1, 1, 0], [0, 0, 1], [0, 0, 0]]`, that is `B e₀ = e₀`, `B e₁ = e₀`, `B e₂ = e₁` (*The
asymmetric fundamental theorem of matrix product states*, Example 6.10, the case `z = 2`). -/
def bIntTwo : Matrix (Fin 3) (Fin 3) ℤ := !![1, 1, 0; 0, 0, 1; 0, 0, 0]

/-- The tensor of *The asymmetric fundamental theorem of matrix product states*, Example 6.10, with
`z = 2`: one letter, `B = [[1, 1, 0], [0, 0, 1], [0, 0, 0]]`. -/
noncomputable def tensorBTwo : MPSTensor 1 3 := fun _ => complexOfInt bIntTwo

/-- The block ordering with the block first and the two zero slots after it. -/
def firstOrdTwo : BlockIndex oneSlot 2 ≃ Fin 3 where
  toFun
    | Sum.inl _ => 0
    | Sum.inr 0 => 1
    | Sum.inr 1 => 2
  invFun
    | 0 => Sum.inl oneSlotMem
    | 1 => Sum.inr 0
    | 2 => Sum.inr 1
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates with the block first and the two zero slots after it. -/
def firstTauTwo : BlockSpace (fun _ : Unit => 1) oneSlot 2 ≃ Fin 3 where
  toFun x := firstOrdTwo x.1
  invFun
    | 0 => ⟨Sum.inl oneSlotMem, 0⟩
    | 1 => ⟨Sum.inr 0, 0⟩
    | 2 => ⟨Sum.inr 1, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The block ordering with the two zero slots first and the block last. -/
def lastOrdTwo : BlockIndex oneSlot 2 ≃ Fin 3 where
  toFun
    | Sum.inl _ => 2
    | Sum.inr 0 => 0
    | Sum.inr 1 => 1
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inr 1
    | 2 => Sum.inl oneSlotMem
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates with the two zero slots first and the block last. -/
def lastTauTwo : BlockSpace (fun _ : Unit => 1) oneSlot 2 ≃ Fin 3 where
  toFun x := lastOrdTwo x.1
  invFun
    | 0 => ⟨Sum.inr 0, 0⟩
    | 1 => ⟨Sum.inr 1, 0⟩
    | 2 => ⟨Sum.inl oneSlotMem, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- A reduction of the `3 × 3` letter onto `C = (1)` with two zero slots from an integer gauge `G`
with inverse `Ginv` conjugating `B` to a matrix `K` that is upper triangular for the ordering `ord`,
with `1` at the block and `0` at both zero slots (blueprint `thm:asym_multiblock`, *Multi-block
asymmetric compression theorem*, clauses (i)–(iii)). -/
noncomputable def compressionOfTwo (ord : BlockIndex oneSlot 2 ≃ Fin 3)
    (τ : BlockSpace (fun _ : Unit => 1) oneSlot 2 ≃ Fin 3) (G Ginv K : Matrix (Fin 3) (Fin 3) ℤ)
    (hG : G * Ginv = 1) (hG' : Ginv * G = 1) (hK : G * bIntTwo * Ginv = K)
    (htri : ∀ x y : BlockSpace (fun _ : Unit => 1) oneSlot 2, ord y.1 < ord x.1 →
      K (τ x) (τ y) = 0)
    (htarget : K (τ ⟨Sum.inl oneSlotMem, 0⟩) (τ ⟨Sum.inl oneSlotMem, 0⟩) = 1)
    (hzero : ∀ t : Fin 2, K (τ ⟨Sum.inr t, 0⟩) (τ ⟨Sum.inr t, 0⟩) = 0) :
    MultiBlockCompression tensorBTwo oneSlot blockC :=
  MultiBlockCompression.ofRing (Int.castRingHom ℂ) ord τ
    (gaugeOfRingMatrix _ τ G Ginv hG hG') (fun _ => K)
    (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix (Int.castRingHom ℂ) τ hG hG'
        (show tensorBTwo i = complexOfRing (Int.castRingHom ℂ) bIntTwo from rfl), hK])
    (fun _ _ => 1) (fun _ _ => (complexOfRing_one _).symm) (fun _ => htri)
    (fun _ s p q => by
      obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      obtain rfl : p = 0 := Subsingleton.elim p 0
      obtain rfl : q = 0 := Subsingleton.elim q 0
      exact htarget.trans (Matrix.one_apply_eq 0).symm)
    fun _ t p q => by
      obtain rfl : p = 0 := Subsingleton.elim p 0
      obtain rfl : q = 0 := Subsingleton.elim q 0
      exact hzero t

/-- The gauge of the reduction with the zero slots first, `g̃ = [[0, -1, -1], [0, 0, -1],
[1, 1, 1]]`; its rows read off the coefficients of `f₁ = e₀ - e₁`, `f₂ = e₁ - e₂` and `e₀`. -/
def gIntTwo : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, -1; 0, 0, -1; 1, 1, 1]

/-- The inverse gauge `g̃⁻¹ = [[1, 0, 1], [-1, 1, 0], [0, -1, 0]]`, whose columns are the basis
`f₁ = e₀ - e₁`, `f₂ = e₁ - e₂`, `e₀` adapted to the flag `0 ⊂ ℂ f₁ ⊂ ℂ f₁ + ℂ f₂ ⊂ ℂ³`. -/
def gInvIntTwo : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 1; -1, 1, 0; 0, -1, 0]

/-- **The reduction with the block first, two zero slots** (*The asymmetric fundamental theorem of
matrix product states*, Example 6.10, `z = 2`): the identity gauge and the flag
`0 ⊂ ℂ e₀ ⊂ ℂ e₀ + ℂ e₁ ⊂ ℂ³`. -/
noncomputable def firstCompressionTwo : MultiBlockCompression tensorBTwo oneSlot blockC :=
  compressionOfTwo firstOrdTwo firstTauTwo 1 1 bIntTwo (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The reduction with the two zero slots first** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10, `z = 2`): the gauge `g̃` with
`g̃ B g̃⁻¹ = [[0, 1, 0], [0, 0, 0], [0, 0, 1]]`, in the order zero slot, zero slot, block. -/
noncomputable def lastCompressionTwo : MultiBlockCompression tensorBTwo oneSlot blockC :=
  compressionOfTwo lastOrdTwo lastTauTwo gIntTwo gInvIntTwo !![0, 1, 0; 0, 0, 0; 0, 0, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

section MapsTwo

variable (ord : BlockIndex oneSlot 2 ≃ Fin 3)
  (τ : BlockSpace (fun _ : Unit => 1) oneSlot 2 ≃ Fin 3) (G Ginv K : Matrix (Fin 3) (Fin 3) ℤ)
  (hG : G * Ginv = 1) (hG' : Ginv * G = 1) (hK : G * bIntTwo * Ginv = K)
  (htri : ∀ x y : BlockSpace (fun _ : Unit => 1) oneSlot 2, ord y.1 < ord x.1 →
    K (τ x) (τ y) = 0)
  (htarget : K (τ ⟨Sum.inl oneSlotMem, 0⟩) (τ ⟨Sum.inl oneSlotMem, 0⟩) = 1)
  (hzero : ∀ t : Fin 2, K (τ ⟨Sum.inr t, 0⟩) (τ ⟨Sum.inr t, 0⟩) = 0)

/-- The reading map of the reduction built from an integer gauge `G` is the row of `G` at the
block coordinate. -/
theorem left_compressionOfTwo :
    (compressionOfTwo ord τ G Ginv K hG hG' hK htri htarget hzero).left oneSlotMem =
      Matrix.of fun (_ : Fin 1) j => (G (τ ⟨Sum.inl oneSlotMem, 0⟩) j : ℂ) := by
  rw [MultiBlockCompression.left_gaugeOfMatrix
    (compressionOfTwo ord τ G Ginv K hG hG' hK htri htarget hzero)
    (hG := complexOfRing_mul_eq_one _ hG) (hG' := complexOfRing_mul_eq_one _ hG') rfl]
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  rfl

/-- The injection of the reduction built from an integer gauge `G` with inverse `Ginv` is the
column of `Ginv` at the block coordinate. -/
theorem right_compressionOfTwo :
    (compressionOfTwo ord τ G Ginv K hG hG' hK htri htarget hzero).right oneSlotMem =
      Matrix.of fun i (_ : Fin 1) => (Ginv i (τ ⟨Sum.inl oneSlotMem, 0⟩) : ℂ) := by
  rw [MultiBlockCompression.right_gaugeOfMatrix
    (compressionOfTwo ord τ G Ginv K hG hG' hK htri htarget hzero)
    (hG := complexOfRing_mul_eq_one _ hG) (hG' := complexOfRing_mul_eq_one _ hG') rfl]
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  rfl

end MapsTwo

/-- The reading map of the reduction with the block first is `W = (1, 0, 0)`. -/
theorem left_firstCompressionTwo : firstCompressionTwo.left oneSlotMem = !![1, 0, 0] := by
  rw [firstCompressionTwo, left_compressionOfTwo]
  ext i j
  fin_cases i; fin_cases j <;> simp [firstTauTwo, firstOrdTwo, Matrix.one_apply]

/-- The reading map of the reduction with the zero slots first is `W̃ = (1, 1, 1)`. -/
theorem left_lastCompressionTwo : lastCompressionTwo.left oneSlotMem = !![1, 1, 1] := by
  rw [lastCompressionTwo, left_compressionOfTwo]
  ext i j
  fin_cases i; fin_cases j <;> simp [gIntTwo, lastTauTwo, lastOrdTwo]

/-- `W B = (1, 1, 0)`: the first row of `B`. -/
theorem left_firstCompressionTwo_mul (i : Fin 1) :
    firstCompressionTwo.left oneSlotMem * tensorBTwo i = !![1, 1, 0] := by
  rw [left_firstCompressionTwo]
  ext a b
  fin_cases a
  fin_cases b <;> simp [tensorBTwo, bIntTwo, Matrix.mul_apply, Fin.sum_univ_three]

/-- `W̃ B = (1, 1, 1)`: the sum of the rows of `B`. -/
theorem left_lastCompressionTwo_mul (i : Fin 1) :
    lastCompressionTwo.left oneSlotMem * tensorBTwo i = !![1, 1, 1] := by
  rw [left_lastCompressionTwo]
  ext a b
  fin_cases a
  fin_cases b <;> simp [tensorBTwo, bIntTwo, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The one-block identity fails at length one for `z = 2`** (*The asymmetric fundamental theorem
of matrix product states*, Example 6.10): for every word of length `1 = z - 1`, `W̃ B^w = (1, 1, 1)`
is not proportional to `W B^w = (1, 1, 0)`. So the bound `|w| ≥ D_B - D_C = 2` of the one-block
theorem (blueprint `cor:asym_uniq_one_block`) cannot be lowered for `z = 2`. -/
theorem not_exists_left_mul_eq_smul_two (w : List (Fin 1)) (hw : w.length = 1) :
    ¬ ∃ c : ℂ, lastCompressionTwo.left oneSlotMem * Kraus.evalWord tensorBTwo w =
      c • (firstCompressionTwo.left oneSlotMem * Kraus.evalWord tensorBTwo w) := by
  match w, hw with
  | [i], _ =>
    rintro ⟨c, hc⟩
    rw [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, left_firstCompressionTwo_mul,
      left_lastCompressionTwo_mul] at hc
    have h := congrFun (congrFun hc 0) 2
    simp at h

/-- `W B² = (1, 1, 1)`, from `B² = [[1, 1, 1], [0, 0, 0], [0, 0, 0]]`. -/
theorem left_firstCompressionTwo_mul_mul (i j : Fin 1) :
    firstCompressionTwo.left oneSlotMem * (tensorBTwo i * tensorBTwo j) = !![1, 1, 1] := by
  rw [← Matrix.mul_assoc, left_firstCompressionTwo_mul]
  ext a b
  fin_cases a
  fin_cases b <;> simp [tensorBTwo, bIntTwo, Matrix.mul_apply, Fin.sum_univ_three]

/-- `W̃ B² = (1, 1, 1)`. -/
theorem left_lastCompressionTwo_mul_mul (i j : Fin 1) :
    lastCompressionTwo.left oneSlotMem * (tensorBTwo i * tensorBTwo j) = !![1, 1, 1] := by
  rw [← Matrix.mul_assoc, left_lastCompressionTwo_mul]
  ext a b
  fin_cases a
  fin_cases b <;> simp [tensorBTwo, bIntTwo, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The one-block identity at length two for `z = 2`** (*The asymmetric fundamental theorem of
matrix product states*, Example 6.10): `W̃ B² = W B² = (1, 1, 1)`, the identity of the one-block
theorem (blueprint `cor:asym_uniq_one_block`) with scalar `1` at `|w| = 2 = z`. -/
theorem left_mul_sq_eq_two (i j : Fin 1) :
    lastCompressionTwo.left oneSlotMem * (tensorBTwo i * tensorBTwo j) =
      firstCompressionTwo.left oneSlotMem * (tensorBTwo i * tensorBTwo j) := by
  rw [left_firstCompressionTwo_mul_mul, left_lastCompressionTwo_mul_mul]

/-- **The one-block identity from length two on, for `z = 2`** (*The asymmetric fundamental theorem
of matrix product states*, Example 6.10, and the one-block theorem (blueprint
`cor:asym_uniq_one_block`)): `W̃ B^w = W B^w` for every word of length at least `2`. -/
theorem left_mul_evalWord_eq_two (w : List (Fin 1)) (hw : 2 ≤ w.length) :
    lastCompressionTwo.left oneSlotMem * Kraus.evalWord tensorBTwo w =
      firstCompressionTwo.left oneSlotMem * Kraus.evalWord tensorBTwo w := by
  match w, hw with
  | i :: j :: w, _ =>
    simp only [Kraus.evalWord_cons, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (lastCompressionTwo.left oneSlotMem),
      Matrix.mul_assoc (firstCompressionTwo.left oneSlotMem), left_mul_sq_eq_two]

/-- **The injections agree for `z = 2`** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.10): `Ṽ = V = e₀`. -/
theorem right_eq_two :
    lastCompressionTwo.right oneSlotMem = firstCompressionTwo.right oneSlotMem := by
  rw [lastCompressionTwo, right_compressionOfTwo, firstCompressionTwo, right_compressionOfTwo]
  ext i j
  fin_cases i <;> rfl

/-! ### Every number of zero slots

*The asymmetric fundamental theorem of matrix product states*, Example 6.10: `B` on `ℂ^{1+z}` with
`B e₀ = e₀` and `B e_j = e_{j-1}` for `1 ≤ j ≤ z`, and the block `C = (1)`. The identity gauge puts
the block first, `W = e₀ᵀ`, `V = e₀`; the gauge `g̃` with `g̃⁻¹ = (f₁, …, f_z, e₀)`,
`f_j = e_{j-1} - e_j`, puts the block last, `W̃ = e₀ᵀ + ⋯ + e_zᵀ`, `Ṽ = e₀`. Then
`W Bⁿ = ∑_{j ≤ min(n,z)} e_jᵀ` and `W̃ Bⁿ = ∑_{j ≤ z} e_jᵀ`, proportional exactly when `n ≥ z`: the
bound `|w| ≥ D_B - D_C` of the one-block theorem cannot be lowered for any `z ≥ 1`. The cases
`z = 1, 2` above are instances (`tensorBGen_one`, `tensorBGen_two`). -/

section General

variable (z : ℕ)

/-- **The tensor** (*The asymmetric fundamental theorem of matrix product states*, Example 6.10):
`B` on `ℂ^{1+z}` with `B e₀ = e₀`, `B e_j = e_{j-1}`. -/
noncomputable def tensorBGen : MPSTensor 1 (1 + z) := fun _ =>
  Matrix.of fun i j => if (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 then 1 else 0

/-- The row `e₀ᵀ`. -/
noncomputable def rowE0 : Matrix (Fin 1) (Fin (1 + z)) ℂ :=
  Matrix.of fun _ j => if j.val = 0 then 1 else 0

/-- The row `e₀ᵀ + ⋯ + e_zᵀ`. -/
noncomputable def rowOnes : Matrix (Fin 1) (Fin (1 + z)) ℂ := Matrix.of fun _ _ => 1

/-- The column `e₀`. -/
noncomputable def colE0 : Matrix (Fin (1 + z)) (Fin 1) ℂ :=
  Matrix.of fun i _ => if i.val = 0 then 1 else 0

/-- The case `z = 1` is the tensor `[[1, 1], [0, 0]]`. -/
theorem tensorBGen_one : tensorBGen 1 = tensorB := by
  funext a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensorBGen, tensorB, bInt, complexOfRing_apply]

/-- The case `z = 2` is the tensor `[[1, 1, 0], [0, 0, 1], [0, 0, 0]]`. -/
theorem tensorBGen_two : tensorBGen 2 = tensorBTwo := by
  funext a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensorBGen, tensorBTwo, bIntTwo, complexOfRing_apply]

variable {z}

/-- A sum against the indicator of one coordinate value. -/
theorem sum_mul_ite_val {n : ℕ} (f : Fin n → ℂ) (k : ℕ) :
    ∑ b : Fin n, f b * (if b.val = k then 1 else 0) = if h : k < n then f ⟨k, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      have hbk : b.val ≠ k := fun h' => hb (Fin.ext h')
      simp [hbk]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun b _ => ?_
    have hbk : b.val ≠ k := fun h' => h (by rw [← h']; exact b.isLt)
    simp [hbk]
/-- A row times `B`: `(r B)_j = r_0` for `j = 0` and `r_{j-1}` for `j ≥ 1`. -/
theorem mul_tensorBGen_apply (r : Matrix (Fin 1) (Fin (1 + z)) ℂ) (j : Fin (1 + z)) :
    (r * tensorBGen z 0) 0 j =
      if j.val = 0 then r 0 ⟨0, by omega⟩ else r 0 ⟨j.val - 1, by omega⟩ := by
  rw [Matrix.mul_apply]
  have h : ∀ c : Fin (1 + z), r 0 c * tensorBGen z 0 c j =
      r 0 c * (if j.val = 0 then 1 else 0) * (if c.val = 0 then 1 else 0) +
        r 0 c * (if j.val = 0 then 0 else 1) * (if c.val = j.val - 1 then 1 else 0) := by
    intro c
    simp only [tensorBGen, Matrix.of_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h, Finset.sum_add_distrib, sum_mul_ite_val]
  split_ifs <;> simp_all
  omega

/-- `r Bⁿ` for the row `e₀ᵀ`: `∑_{j ≤ min(n,z)} e_jᵀ`. -/
theorem rowE0_mul_pow (n : ℕ) :
    rowE0 z * tensorBGen z 0 ^ n = Matrix.of (fun _ j => if j.val ≤ n then 1 else 0) := by
  induction n with
  | zero =>
    ext i j
    simp [rowE0]
  | succ n ih =>
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [pow_succ, ← Matrix.mul_assoc, mul_tensorBGen_apply, ih]
    split_ifs <;> simp_all

/-- `r Bⁿ` for the row of ones: the row of ones. -/
theorem rowOnes_mul_pow (n : ℕ) : rowOnes z * tensorBGen z 0 ^ n = rowOnes z := by
  induction n with
  | zero => rw [pow_zero, Matrix.mul_one]
  | succ n ih =>
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [pow_succ, ← Matrix.mul_assoc, ih, mul_tensorBGen_apply]
    split_ifs <;> simp [rowOnes]

/-- **The reading maps after words** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.10): `W Bⁿ = ∑_{j ≤ min(n,z)} e_jᵀ` and `W̃ Bⁿ = ∑_{j ≤ z} e_jᵀ` for every `n ≥ 0`. -/
theorem rowE0_mul_pow_and_rowOnes_mul_pow (n : ℕ) :
    rowE0 z * tensorBGen z 0 ^ n = Matrix.of (fun _ j => if j.val ≤ n then 1 else 0) ∧
    rowOnes z * tensorBGen z 0 ^ n = rowOnes z :=
  ⟨rowE0_mul_pow n, rowOnes_mul_pow n⟩

/-- **Proportional exactly from length `z` on** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10): `W̃ Bⁿ = λ W Bⁿ` for some `λ` iff `n ≥ z`. -/
theorem exists_rowOnes_mul_pow_eq_smul_iff (n : ℕ) :
    (∃ c : ℂ, rowOnes z * tensorBGen z 0 ^ n = c • (rowE0 z * tensorBGen z 0 ^ n)) ↔ z ≤ n := by
  rw [rowE0_mul_pow, rowOnes_mul_pow]
  constructor
  · rintro ⟨c, hc⟩
    by_contra hlt
    have := congrFun (congrFun hc 0) ⟨z, by omega⟩
    simp [rowOnes, show ¬ z ≤ n by omega] at this
  · intro hzn
    refine ⟨1, ?_⟩
    ext i j
    have : j.val ≤ n := by have := j.isLt; omega
    simp [rowOnes, this]

theorem evalWord_replicate (n : ℕ) :
    Kraus.evalWord (tensorBGen z) (List.replicate n 0) = tensorBGen z 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, Kraus.evalWord_cons, ih, pow_succ']

/-! #### The two reductions for every `z` -/

theorem slotSize_unit (b : BlockIndex oneSlot z) : slotSize (fun _ : Unit => 1) b = 1 := by
  cases b <;> rfl

/-- The bond coordinates of a reduction with one-dimensional slots, read off its order. -/
def coordOfOrd (ord : BlockIndex oneSlot z ≃ Fin (1 + z)) :
    BlockSpace (fun _ : Unit => 1) oneSlot z ≃ Fin (1 + z) where
  toFun x := ord x.1
  invFun n := ⟨ord.symm n, ⟨0, by rw [slotSize_unit]; exact Nat.one_pos⟩⟩
  left_inv x := by
    obtain ⟨b, p⟩ := x
    have hp : p.val = 0 := by have h1 := p.isLt; have h2 := slotSize_unit b; omega
    refine Sigma.ext (ord.symm_apply_apply b)
      ((Fin.heq_ext_iff (congrArg (slotSize (fun _ : Unit => 1)) (ord.symm_apply_apply b))).2 ?_)
    exact hp.symm
  right_inv n := by simp

/-- A reduction of `B` onto `C = (1)` with `z` zero slots from an explicit gauge `G` with
`G B G⁻¹ = K` upper triangular, `1` at the position of the block and `0` at the zero slots
(blueprint `thm:asym_multiblock`, *Multi-block asymmetric compression theorem*, clauses (i)–(iii)).
-/
noncomputable def compressionGen (ord : BlockIndex oneSlot z ≃ Fin (1 + z))
    (G Ginv K : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (hK : G * tensorBGen z 0 * Ginv = K) (htri : ∀ a b, b < a → K a b = 0)
    (hblock : K (ord (Sum.inl oneSlotMem)) (ord (Sum.inl oneSlotMem)) = 1)
    (hzero : ∀ t, K (ord (Sum.inr t)) (ord (Sum.inr t)) = 0) :
    MultiBlockCompression (tensorBGen z) oneSlot blockC where
  z := z
  ord := ord
  gauge := gaugeOfMatrix (coordOfOrd ord) G Ginv hG hG'
  triangular i x y hxy := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hK]
    exact htri _ _ hxy
  matched i s := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : s = oneSlotMem := eq_oneSlotMem s
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hK]
    simpa [blockC, coordOfOrd] using hblock
  unmatched i t := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hK]
    exact hzero t

theorem gauge_compressionGen (ord : BlockIndex oneSlot z ≃ Fin (1 + z))
    (G Ginv K : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (hK : G * tensorBGen z 0 * Ginv = K) (htri : ∀ a b, b < a → K a b = 0)
    (hblock : K (ord (Sum.inl oneSlotMem)) (ord (Sum.inl oneSlotMem)) = 1)
    (hzero : ∀ t, K (ord (Sum.inr t)) (ord (Sum.inr t)) = 0) :
    (compressionGen ord G Ginv K hG hG' hK htri hblock hzero).gauge =
      gaugeOfMatrix (coordOfOrd ord) G Ginv hG hG' := rfl

theorem tensorBGen_apply (a b : Fin (1 + z)) :
    tensorBGen z 0 a b = if (a.val = 0 ∧ b.val = 0) ∨ b.val = a.val + 1 then 1 else 0 := rfl

theorem tensorBGen_tri (a b : Fin (1 + z)) (h : b < a) : tensorBGen z 0 a b = 0 := by
  rw [tensorBGen_apply, ite_eq_right]
  have := Fin.lt_def.1 h
  omega

/-- The order with the block first: the block at position `0`, the zero slot `t` at `t + 1`. -/
def firstOrdGen : BlockIndex oneSlot z ≃ Fin (1 + z) where
  toFun
    | Sum.inl _ => ⟨0, by omega⟩
    | Sum.inr t => ⟨t.val + 1, by have := t.isLt; omega⟩
  invFun n := if h : n.val = 0 then Sum.inl oneSlotMem else Sum.inr ⟨n.val - 1, by omega⟩
  left_inv b := by
    rcases b with s | t
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      simp
    · simp
  right_inv n := by
    by_cases h : n.val = 0
    · simp only [h, dite_true]
      ext
      simp [h]
    · simp only [h, dite_false]
      ext
      simp only
      omega

/-- **The reduction `g = 1`** with the block first (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10). -/
noncomputable def firstCompressionGen : MultiBlockCompression (tensorBGen z) oneSlot blockC :=
  compressionGen firstOrdGen 1 1 (tensorBGen z 0) (Matrix.mul_one 1) (Matrix.mul_one 1)
    (by rw [Matrix.one_mul, Matrix.mul_one]) tensorBGen_tri
    (by simp [tensorBGen_apply, firstOrdGen])
    (fun t => by
      rw [tensorBGen_apply, ite_eq_right]
      simp [firstOrdGen])

/-- The order with the block last: the zero slot `t` at position `t`, the block at `z`. -/
def lastOrdGen : BlockIndex oneSlot z ≃ Fin (1 + z) where
  toFun
    | Sum.inl _ => ⟨z, by omega⟩
    | Sum.inr t => ⟨t.val, by have := t.isLt; omega⟩
  invFun n := if h : n.val < z then Sum.inr ⟨n.val, h⟩ else Sum.inl oneSlotMem
  left_inv b := by
    rcases b with s | t
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      simp
    · simp [t.isLt]
  right_inv n := by
    by_cases h : n.val < z
    · simp [h]
    · simp only [h, dite_false]
      ext
      simp only
      have := n.isLt
      omega

/-- `g̃`: the row `z` is `e₀ᵀ + ⋯ + e_zᵀ`, the row `p < z` is `-(e_{p+1}ᵀ + ⋯ + e_zᵀ)`. -/
noncomputable def gGen : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ :=
  Matrix.of fun a b => if a.val = z then 1 else if a.val < b.val then -1 else 0

/-- `g̃⁻¹ = (f₁, …, f_z, e₀)`, `f_j = e_{j-1} - e_j`. -/
noncomputable def gInvGen : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ :=
  Matrix.of fun b c =>
    if c.val = z then (if b.val = 0 then 1 else 0)
    else if b.val = c.val then 1 else if b.val = c.val + 1 then -1 else 0

/-- `g̃ B g̃⁻¹`: `1` at `(z, z)` and at `(p - 1, p)` for `1 ≤ p < z`. -/
noncomputable def kGen : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ :=
  Matrix.of fun a b => if (a.val = z ∧ b.val = z) ∨ (b.val = a.val + 1 ∧ b.val < z) then 1 else 0

theorem gGen_mul_gInvGen : gGen (z := z) * gInvGen = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  have h : ∀ b : Fin (1 + z), gGen a b * gInvGen b c =
      gGen a b * (if c.val = z then 1 else 0) * (if b.val = 0 then 1 else 0) +
        gGen a b * (if c.val = z then 0 else 1) * (if b.val = c.val then 1 else 0) -
        gGen a b * (if c.val = z then 0 else 1) * (if b.val = c.val + 1 then 1 else 0) := by
    intro b
    simp only [gInvGen, Matrix.of_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_mul_ite_val]
  simp only [gGen, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  have := a.isLt
  have := c.isLt
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem gGen_mul_tensorBGen : gGen (z := z) * tensorBGen z 0 = kGen * gGen := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have h1 : ∀ c : Fin (1 + z), gGen a c * tensorBGen z 0 c b =
      gGen a c * (if b.val = 0 then 1 else 0) * (if c.val = 0 then 1 else 0) +
        gGen a c * (if b.val = 0 then 0 else 1) * (if c.val = b.val - 1 then 1 else 0) := by
    intro c
    simp only [tensorBGen_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have h2 : ∀ c : Fin (1 + z), kGen a c * gGen c b =
      gGen c b * (if a.val = z then 1 else 0) * (if c.val = z then 1 else 0) +
        gGen c b * (if a.val + 1 < z then 1 else 0) * (if c.val = a.val + 1 then 1 else 0) := by
    intro c
    simp only [kGen, Matrix.of_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h1, h2, Finset.sum_add_distrib, sum_mul_ite_val]
  simp only [gGen, Matrix.of_apply]
  have := a.isLt
  have := b.isLt
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem gGen_conj : gGen (z := z) * tensorBGen z 0 * gInvGen = kGen := by
  rw [gGen_mul_tensorBGen, Matrix.mul_assoc, gGen_mul_gInvGen, Matrix.mul_one]

/-- **The reduction `g̃`** with the block last (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10). -/
noncomputable def lastCompressionGen : MultiBlockCompression (tensorBGen z) oneSlot blockC :=
  compressionGen lastOrdGen gGen gInvGen kGen gGen_mul_gInvGen
    (mul_eq_one_comm.1 gGen_mul_gInvGen) gGen_conj
    (fun a b h => by
      have := Fin.lt_def.1 h
      simp only [kGen, Matrix.of_apply]
      rw [ite_eq_right]
      omega)
    (by simp [kGen, lastOrdGen])
    (fun t => by
      simp only [kGen, Matrix.of_apply, lastOrdGen, Equiv.coe_fn_mk]
      rw [ite_eq_right]
      have := t.isLt
      omega)

theorem gauge_firstCompressionGen :
    (firstCompressionGen (z := z)).gauge =
      gaugeOfMatrix (coordOfOrd firstOrdGen) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1) := rfl

theorem gauge_lastCompressionGen :
    (lastCompressionGen (z := z)).gauge =
      gaugeOfMatrix (coordOfOrd lastOrdGen) gGen gInvGen gGen_mul_gInvGen
        (mul_eq_one_comm.1 gGen_mul_gInvGen) := rfl

theorem coordOfOrd_apply (ord : BlockIndex oneSlot z ≃ Fin (1 + z))
    (x : BlockSpace (fun _ : Unit => 1) oneSlot z) : coordOfOrd ord x = ord x.1 := rfl

theorem firstOrdGen_inl (s : {s // s ∈ oneSlot}) : (firstOrdGen (z := z) (Sum.inl s)).val = 0 :=
  rfl

theorem firstOrdGen_inr (t : Fin z) : (firstOrdGen (z := z) (Sum.inr t)).val = t.val + 1 := rfl

theorem lastOrdGen_inl (s : {s // s ∈ oneSlot}) : (lastOrdGen (z := z) (Sum.inl s)).val = z := rfl

theorem lastOrdGen_inr (t : Fin z) : (lastOrdGen (z := z) (Sum.inr t)).val = t.val := rfl

/-- **The first reduction** (*The asymmetric fundamental theorem of matrix product states*, Example
6.10): `g = 1` is a reduction onto `C = (1)` with the block first and `z` zero blocks, `W = e₀ᵀ`,
`V = e₀`; the zero slot at position `p` reads `e_pᵀ`. -/
theorem exists_multiBlockCompression_block_first :
    ∃ P : MultiBlockCompression (tensorBGen z) oneSlot blockC, P.z = z ∧
    (∀ b, P.ord (Sum.inl oneSlotMem) ≤ P.ord b) ∧
    P.left oneSlotMem = rowE0 z ∧ P.right oneSlotMem = colE0 z ∧
    ∀ t, P.leftRow (Sum.inr t) =
      Matrix.of fun _ j => if j.val = (P.ord (Sum.inr t)).val then 1 else 0 := by
  refine ⟨firstCompressionGen, rfl, fun b => ?_, ?_, ?_, fun t => ?_⟩
  · change firstOrdGen (Sum.inl oneSlotMem) ≤ firstOrdGen b
    rw [Fin.le_def]
    simp [firstOrdGen]
  · rw [← MultiBlockCompression.leftRow_inl,
      MultiBlockExamples.leftRow_gaugeOfMatrix _ gauge_firstCompressionGen]
    ext i j
    change (1 : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) (firstOrdGen (Sum.inl oneSlotMem)) j =
      rowE0 z i j
    simp only [Matrix.one_apply, Fin.ext_iff,
      firstOrdGen_inl, rowE0, Matrix.of_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [← MultiBlockCompression.rightCol_inl,
      MultiBlockExamples.rightCol_gaugeOfMatrix _ gauge_firstCompressionGen]
    ext i j
    change (1 : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) i (firstOrdGen (Sum.inl oneSlotMem)) =
      colE0 z i j
    simp only [Matrix.one_apply, Fin.ext_iff,
      firstOrdGen_inl, colE0, Matrix.of_apply]
  · rw [MultiBlockExamples.leftRow_gaugeOfMatrix _ gauge_firstCompressionGen,
      show firstCompressionGen.ord = firstOrdGen from rfl]
    ext i j
    have ht : t.val < z := t.isLt
    change (1 : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) ⟨t.val + 1, by omega⟩ j =
      (if j.val = t.val + 1 then 1 else 0)
    simp only [Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **The second reduction** (*The asymmetric fundamental theorem of matrix product states*, Example
6.10): `g̃` with `g̃⁻¹ = (f₁, …, f_z, e₀)`, `f_j = e_{j-1} - e_j`, is a reduction with the block
last, `W̃ = e₀ᵀ + ⋯ + e_zᵀ`, `Ṽ = e₀`; the zero slot at position `p` has injection `f_{p+1}`. -/
theorem exists_multiBlockCompression_block_last :
    ∃ Q : MultiBlockCompression (tensorBGen z) oneSlot blockC, Q.z = z ∧
    (∀ b, Q.ord b ≤ Q.ord (Sum.inl oneSlotMem)) ∧
    Q.left oneSlotMem = rowOnes z ∧ Q.right oneSlotMem = colE0 z ∧
    ∀ t, Q.rightCol (Sum.inr t) = Matrix.of fun i _ =>
      if i.val = (Q.ord (Sum.inr t)).val then 1
      else if i.val = (Q.ord (Sum.inr t)).val + 1 then -1 else 0 := by
  refine ⟨lastCompressionGen, rfl, fun b => ?_, ?_, ?_, fun t => ?_⟩
  · change lastOrdGen b ≤ lastOrdGen (Sum.inl oneSlotMem)
    rw [Fin.le_def]
    rcases b with s | t
    · simp [lastOrdGen]
    · simp only [lastOrdGen, Equiv.coe_fn_mk]
      exact t.isLt.le
  · rw [← MultiBlockCompression.leftRow_inl,
      MultiBlockExamples.leftRow_gaugeOfMatrix _ gauge_lastCompressionGen]
    ext i j
    change gGen (lastOrdGen (Sum.inl oneSlotMem)) j = rowOnes z i j
    simp only [gGen, Matrix.of_apply,
      lastOrdGen_inl, rowOnes]
    simp
  · rw [← MultiBlockCompression.rightCol_inl,
      MultiBlockExamples.rightCol_gaugeOfMatrix _ gauge_lastCompressionGen]
    ext i j
    change gInvGen i (lastOrdGen (Sum.inl oneSlotMem)) = colE0 z i j
    simp only [gInvGen, Matrix.of_apply,
      lastOrdGen_inl, colE0]
    simp
  · rw [MultiBlockExamples.rightCol_gaugeOfMatrix _ gauge_lastCompressionGen,
      show lastCompressionGen.ord = lastOrdGen from rfl]
    ext i j
    have ht : t.val < z := t.isLt
    change gInvGen i ⟨t.val, by omega⟩ = (if i.val = t.val then 1
      else if i.val = t.val + 1 then -1 else 0)
    simp only [gInvGen, Matrix.of_apply]
    rw [ite_eq_right (by omega)]

variable (hz : 0 < z)

include hz in
/-- **Sharpness** (*The asymmetric fundamental theorem of matrix product states*, Example 6.10;
blueprint `cor:asym_uniq_one_block`, *Bare uniqueness at the ends of the flag; the one-block
theorem*): the identity `W̃ B^w = λ W B^w` fails at a word of length `z - 1 = D_B - D_A - 1`, so the
bound `|w| ≥ D_B - D_A` of the one-block theorem cannot be lowered. -/
theorem exists_length_eq_sub_one_not_exists_smul : ∃ w : List (Fin 1), w.length = z - 1 ∧
    ¬ ∃ c : ℂ, rowOnes z * Kraus.evalWord (tensorBGen z) w =
      c • (rowE0 z * Kraus.evalWord (tensorBGen z) w) := by
  refine ⟨List.replicate (z - 1) 0, List.length_replicate, ?_⟩
  rw [evalWord_replicate, exists_rowOnes_mul_pow_eq_smul_iff]
  omega

/-- **The injections after words** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.10): `Bⁿ Ṽ = Bⁿ V` for reductions with `V = Ṽ = e₀`. -/
theorem pow_mul_right_eq_of_eq_colE0 (P Q : MultiBlockCompression (tensorBGen z) oneSlot blockC)
    (hP : P.right oneSlotMem = colE0 z) (hQ : Q.right oneSlotMem = colE0 z) (n : ℕ) :
    tensorBGen z 0 ^ n * Q.right oneSlotMem = tensorBGen z 0 ^ n * P.right oneSlotMem := by
  rw [hP, hQ]

end General

end MultiBlockExamples.SharpnessOneBlock
