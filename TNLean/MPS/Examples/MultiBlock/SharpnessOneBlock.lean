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
fundamental theorem of matrix product states*, Example 6.10) is
`TNLean.MPS.Examples.MultiBlock.SharpnessOneBlockGeneral`: `B` on `ℂ^{1+z}` with `B e₀ = e₀`,
`B e_j = e_{j-1}`; `W Bⁿ` and `W̃ Bⁿ` are proportional exactly when `n ≥ z`.

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

end MultiBlockExamples.SharpnessOneBlock
