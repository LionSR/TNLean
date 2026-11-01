/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Multiplicity
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# The worked example

The tensor `B = (B¹, B²)` on `ℂ⁴` of *The asymmetric fundamental theorem of matrix product states*,
Example 6.16, with the letters as printed there (the normal block `C₁ = (σ_x, E₁₁)`), is
`B^i = g₀⁻¹ (C₁^i ⊕ T^i) g₀` with `T = ([[0, 1], [0, 1]], [[0, 0], [0, 2]])`, a non-split extension
of `C₂ = ((1), (2))` by a zero block. It has the reduction `g = g₀` in the order `(C₁, 0, C₂)` and
the reduction `g_tilde = h P g₀` in the order `(0, C₂, C₁')` onto the second family `(C₁', C₂)`,
`C₁' = Y C₁ Y⁻¹`, `Y = [[1, 1], [0, 1]]`. The dimension matrix and the basis adapted to both
flags are in `TNLean.MPS.Examples.MultiBlock.WorkedAdaptedBasis`.

## Main results

* `MultiBlockExamples.Worked.wordSpan_tensorC₁_three_eq_top_and_isNormal`,
  `isInvariantSubmodule_span_tensorT_iff_and_mulVec_eq_zero`: the blocks.
* `MultiBlockExamples.Worked.redG_spec`, `redGt_spec`: the two reductions.
* `MultiBlockExamples.Worked.flagVec_redG_redGt_and_matching`, `inf_sup_intertwiner_redG_redGt`:
  the flags, the matching and the matched pairs.
* `MultiBlockExamples.Worked.not_exists_left_redGt_eq_smul_left_redG`: the reading maps of `C₂` are
  not proportional.
* `MultiBlockExamples.Worked.trace_evalWord_tensorB_eq_add`: the word traces.

## References

*The asymmetric fundamental theorem of matrix product states*, Example 6.16, with the letters as
printed there; the numbers are those of `check/worked_example_normal.py` and
`check/example-2x2-normal.tex`. Blueprint `prop:asym_uniq_matching`, *The matching*, and
`thm:asym_uniq_different_flags`, *Two compressions with different flags*.
-/

open scoped Matrix

namespace MultiBlockExamples

namespace Worked

open MPSTensor

/-- The integer letters of `B`, as printed in *The asymmetric fundamental theorem of matrix product
states*, Example 6.16. -/
def tensorBInt : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![-2, -2, -1, 0; 2, 3, 1, 0; -2, -4, -1, 0; 2, 2, 1, 1],
    !![2, 0, 1, 3; 0, 2, 0, -2; -2, -2, -1, -1; 0, 0, 0, 0]]

/-- **The worked example** `B = (B¹, B²)` of *The asymmetric fundamental theorem of matrix product
states*, Example 6.16, with the letters as printed there. -/
noncomputable def tensorB : MPSTensor 2 4 :=
  ![!![-2, -2, -1, 0; 2, 3, 1, 0; -2, -4, -1, 0; 2, 2, 1, 1],
    !![2, 0, 1, 3; 0, 2, 0, -2; -2, -2, -1, -1; 0, 0, 0, 0]]

theorem tensorB_eq_complexOfRing (i : Fin 2) :
    tensorB i = complexOfRing (Int.castRingHom ℂ) (tensorBInt i) := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [tensorB, tensorBInt, complexOfRing_apply]

/-- `C₁ = (σ_x, E₁₁)`, as printed in *The asymmetric fundamental theorem of matrix product states*,
Example 6.16. -/
noncomputable def tensorC₁ : MPSTensor 2 2 := Multiplicity.tensorC

/-- `C₂ = ((1), (2))`. -/
noncomputable def tensorC₂ : MPSTensor 2 1 := ![!![1], !![2]]

/-- `T = ([[0, 1], [0, 1]], [[0, 0], [0, 2]])`. -/
noncomputable def tensorT : MPSTensor 2 2 := ![!![0, 1; 0, 1], !![0, 0; 0, 2]]

/-- `Y = [[1, 1], [0, 1]]`. -/
noncomputable def matY : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]

/-- `C₁' = Y C₁ Y⁻¹ = ([[1, 0], [1, -1]], [[1, -1], [0, 0]])`. -/
noncomputable def tensorC₁' : MPSTensor 2 2 := ![!![1, 0; 1, -1], !![1, -1; 0, 0]]

/-- **The block `C₁` is normal** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.16): `C₁` is normal, its words of length `3` spanning `M₂(ℂ)`. -/
theorem wordSpan_tensorC₁_three_eq_top_and_isNormal :
    Kraus.wordSpan tensorC₁ 3 = ⊤ ∧ Kraus.IsNormal tensorC₁ :=
  Multiplicity.wordSpan_tensorC_three_eq_top_and_isNormal

/-- **The invariant line of `T`** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.16): `T` has exactly one invariant line, `ℂ e₁`, and both letters vanish on it. -/
theorem isInvariantSubmodule_span_tensorT_iff_and_mulVec_eq_zero : (∀ v : Fin 2 → ℂ, v ≠ 0 →
      (Matrix.IsInvariantSubmodule tensorT (Submodule.span ℂ {v}) ↔
        Submodule.span ℂ {v} = Submodule.span ℂ {e 0})) ∧
    ∀ i, tensorT i *ᵥ e 0 = 0 := by
  refine ⟨fun v hv => ?_, fun i => ?_⟩
  · rw [isInvariantSubmodule_span_singleton_iff]
    constructor
    · intro h
      obtain ⟨c₀, h₀⟩ := h 0
      obtain ⟨c₁, h₁⟩ := h 1
      have a0 : v 1 = c₀ * v 0 := by
        simpa [tensorT, Matrix.mulVec, dotProduct] using congrFun h₀ 0
      have a1 : v 1 = c₀ * v 1 := by
        simpa [tensorT, Matrix.mulVec, dotProduct] using congrFun h₀ 1
      have b0 : 0 = c₁ * v 0 := by
        simpa [tensorT, Matrix.mulVec, dotProduct] using congrFun h₁ 0
      have b1 : 2 * v 1 = c₁ * v 1 := by
        simpa [tensorT, Matrix.mulVec, dotProduct] using congrFun h₁ 1
      have hv1 : v 1 = 0 := by
        by_contra hv1
        have hc₁ : c₁ = 2 := by
          have h' : (c₁ - 2) * v 1 = 0 := by linear_combination -b1
          exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv1)
        have hv0 : v 0 = 0 := by
          rw [hc₁] at b0
          linear_combination -b0 / 2
        have hc₀ : c₀ = 1 := by
          have h' : (c₀ - 1) * v 1 = 0 := by linear_combination -a1
          exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv1)
        rw [hv0, mul_zero] at a0
        exact hv1 a0
      have hv0 : v 0 ≠ 0 := fun h0 => hv (by ext i; fin_cases i <;> simp [h0, hv1])
      refine span_singleton_eq_of_eq_smul hv0 ?_
      ext i; fin_cases i <;> simp [hv1]
    · intro h i
      obtain ⟨c, hc⟩ := exists_eq_smul_of_span_singleton_eq h
      have hv1 : v 1 = 0 := by simpa using congrFun hc 1
      refine ⟨0, ?_⟩
      ext j; fin_cases i <;> fin_cases j <;> simp [tensorT, Matrix.mulVec, dotProduct, hv1]
  · ext j; fin_cases i <;> fin_cases j <;> simp [tensorT, Matrix.mulVec, dotProduct]

/-! ### The two reductions -/

/-- Labels: `0` for `C₁` (or `C₁'`), `1` for `C₂`. -/
abbrev labels : Finset (Fin 2) := Finset.univ

/-- Block sizes `2` and `1`. -/
abbrev dims : Fin 2 → ℕ := ![2, 1]

/-- The first family `(C₁, C₂)`. -/
noncomputable def blocks : ∀ s : Fin 2, MPSTensor 2 (dims s)
  | 0 => tensorC₁
  | 1 => tensorC₂

/-- The second family `(C₁', C₂)`. -/
noncomputable def blocks' : ∀ s : Fin 2, MPSTensor 2 (dims s)
  | 0 => tensorC₁'
  | 1 => tensorC₂

/-- The integer letters of the first family. -/
def blocksInt : ∀ s : Fin 2, Fin 2 → Matrix (Fin (dims s)) (Fin (dims s)) ℤ
  | 0 => ![!![0, 1; 1, 0], !![1, 0; 0, 0]]
  | 1 => ![!![1], !![2]]

/-- The integer letters of the second family. -/
def blocksInt' : ∀ s : Fin 2, Fin 2 → Matrix (Fin (dims s)) (Fin (dims s)) ℤ
  | 0 => ![!![1, 0; 1, -1], !![1, -1; 0, 0]]
  | 1 => ![!![1], !![2]]

theorem blocks_eq_complexOfRing (s : Fin 2) (i : Fin 2) :
    blocks s i = complexOfRing (Int.castRingHom ℂ) (blocksInt s i) := by
  ext a b
  fin_cases s <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [blocks, blocksInt, tensorC₁, tensorC₂, Multiplicity.tensorC, complexOfRing_apply]

theorem blocks'_eq_complexOfRing (s : Fin 2) (i : Fin 2) :
    blocks' s i = complexOfRing (Int.castRingHom ℂ) (blocksInt' s i) := by
  ext a b
  fin_cases s <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [blocks', blocksInt', tensorC₁', tensorC₂, complexOfRing_apply]

/-- The slot of `C₁` (or `C₁'`). -/
abbrev slotC1 : {s // s ∈ labels} := ⟨0, Finset.mem_univ _⟩

/-- The slot of `C₂`. -/
abbrev slotC2 : {s // s ∈ labels} := ⟨1, Finset.mem_univ _⟩

/-- The order `(C₁, 0, C₂)`. -/
def ordG : BlockIndex labels 1 ≃ Fin 3 where
  toFun
    | Sum.inl s => if s.1 = 0 then 0 else 2
    | Sum.inr _ => 1
  invFun
    | 0 => Sum.inl slotC1
    | 1 => Sum.inr 0
    | 2 => Sum.inl slotC2
  left_inv := by decide
  right_inv := by decide

/-- The order `(0, C₂, C₁')`. -/
def ordGt : BlockIndex labels 1 ≃ Fin 3 where
  toFun
    | Sum.inl s => if s.1 = 0 then 2 else 1
    | Sum.inr _ => 0
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inl slotC2
    | 2 => Sum.inl slotC1
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates of `g`: `C₁` on `0, 1`, the zero block on `2`, `C₂` on `3`. -/
def tauG : BlockSpace dims labels 1 ≃ Fin 4 where
  toFun
    | ⟨Sum.inl s, p⟩ => if s.1 = 0 then ⟨p.val % 4, Nat.mod_lt _ (by norm_num)⟩ else 3
    | ⟨Sum.inr _, _⟩ => 2
  invFun
    | 0 => ⟨Sum.inl slotC1, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inl slotC1, ⟨1, by decide⟩⟩
    | 2 => ⟨Sum.inr 0, ⟨0, by decide⟩⟩
    | 3 => ⟨Sum.inl slotC2, ⟨0, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates of `g_tilde`: the zero block on `0`, `C₂` on `1`, `C₁'` on `2, 3`. -/
def tauGt : BlockSpace dims labels 1 ≃ Fin 4 where
  toFun
    | ⟨Sum.inl s, p⟩ => if s.1 = 0 then ⟨(p.val + 2) % 4, Nat.mod_lt _ (by norm_num)⟩ else 1
    | ⟨Sum.inr _, _⟩ => 0
  invFun
    | 0 => ⟨Sum.inr 0, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inl slotC2, ⟨0, by decide⟩⟩
    | 2 => ⟨Sum.inl slotC1, ⟨0, by decide⟩⟩
    | 3 => ⟨Sum.inl slotC1, ⟨1, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

/-- `g₀`. -/
def g0Int : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 2, 1, 1; 0, 0, 0, 1; 1, 1, 1, 1; 0, -1, 0, 1]

/-- `g₀⁻¹`. -/
def g0InvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, -1, 1; 0, 1, 0, -1; -1, -1, 2, 0; 0, 1, 0, 0]

/-- `P`, moving the `C₁` pair behind the `T` pair and applying `Y` to it. -/
def permInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 1, 0, 0; 0, 1, 0, 0]

/-- `h`, unipotent block upper triangular in the order `(0, C₂, C₁')`. -/
def hInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 1, -1; 0, 1, -1, 2; 0, 0, 1, 0; 0, 0, 0, 1]

/-- `g_tilde = h P g₀`. -/
def gtInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3, 2, 2, 3; -2, -3, -1, 1; 2, 2, 1, 2; 0, 0, 0, 1]

/-- `g_tilde⁻¹`. -/
def gtInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1, 2, 4, -7; 0, -1, -1, 3; 2, -2, -5, 6; 0, 0, 0, 1]

/-- `g B¹ g⁻¹`, `g B² g⁻¹`: `C₁^i ⊕ T^i`. -/
def conjG : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2]]

/-- `g_tilde B¹ g_tilde⁻¹`, `g_tilde B² g_tilde⁻¹` as printed in *The asymmetric fundamental theorem
of matrix product states*, Example 6.16. -/
def conjGt : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0, 2, 2, -3; 0, 1, 2, -4; 0, 0, 1, 0; 0, 0, 1, -1],
    !![0, 2, 3, -5; 0, 2, 1, -3; 0, 0, 1, -1; 0, 0, 0, 0]]

theorem conjG_eq (i : Fin 2) : g0Int * tensorBInt i * g0InvInt = conjG i := by
  fin_cases i <;> decide +kernel

theorem conjGt_eq (i : Fin 2) : gtInt * tensorBInt i * gtInvInt = conjGt i := by
  fin_cases i <;> decide +kernel

/-- **The reduction `g = g₀`** in the order `(C₁, 0, C₂)` (*The asymmetric fundamental theorem of
matrix product states*, Example 6.16). -/
noncomputable def redG : MultiBlockCompression tensorB labels blocks :=
  MultiBlockCompression.ofRing (Int.castRingHom ℂ) ordG tauG
    (gaugeOfRingMatrix _ tauG g0Int g0InvInt (by decide +kernel) (by decide +kernel)) conjG
    (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix (Int.castRingHom ℂ) tauG (by decide +kernel)
        (by decide +kernel) (tensorB_eq_complexOfRing i), conjG_eq])
    blocksInt blocks_eq_complexOfRing (fun i x y h => by revert i x y; decide +kernel)
    (fun i s p q => by
      obtain ⟨s, hs⟩ := s
      obtain rfl : hs = Finset.mem_univ s := rfl
      revert p q
      fin_cases s <;> fin_cases i <;> intro p q <;> fin_cases p <;> fin_cases q <;> decide +kernel)
    (by decide +kernel)

/-- **The reduction `g_tilde = h P g₀`** in the order `(0, C₂, C₁')` onto the second family (*The
asymmetric fundamental theorem of matrix product states*, Example 6.16). -/
noncomputable def redGt : MultiBlockCompression tensorB labels blocks' :=
  MultiBlockCompression.ofRing (Int.castRingHom ℂ) ordGt tauGt
    (gaugeOfRingMatrix _ tauGt gtInt gtInvInt (by decide +kernel) (by decide +kernel)) conjGt
    (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix (Int.castRingHom ℂ) tauGt (by decide +kernel)
        (by decide +kernel) (tensorB_eq_complexOfRing i), conjGt_eq])
    blocksInt' blocks'_eq_complexOfRing (fun i x y h => by revert i x y; decide +kernel)
    (fun i s p q => by
      obtain ⟨s, hs⟩ := s
      obtain rfl : hs = Finset.mem_univ s := rfl
      revert p q
      fin_cases s <;> fin_cases i <;> intro p q <;> fin_cases p <;> fin_cases q <;> decide +kernel)
    (by decide +kernel)

/-- An integer matrix read in `ℂ`. -/
noncomputable abbrev toC {m n : Type*} (M : Matrix m n ℤ) : Matrix m n ℂ :=
  complexOfRing (Int.castRingHom ℂ) M

theorem gauge_redG : redG.gauge = gaugeOfMatrix tauG (toC g0Int) (toC g0InvInt)
    (complexOfRing_mul_eq_one _ (by decide +kernel))
    (complexOfRing_mul_eq_one _ (by decide +kernel)) :=
  rfl

theorem gauge_redGt : redGt.gauge = gaugeOfMatrix tauGt (toC gtInt) (toC gtInvInt)
    (complexOfRing_mul_eq_one _ (by decide +kernel))
    (complexOfRing_mul_eq_one _ (by decide +kernel)) :=
  rfl

theorem leftRow_redG (b : BlockIndex labels 1) :
    redG.leftRow b = toC (g0Int.submatrix (fun i => tauG ⟨b, i⟩) id) := by
  rw [leftRow_gaugeOfMatrix redG gauge_redG b]
  rfl

theorem rightCol_redG (b : BlockIndex labels 1) :
    redG.rightCol b = toC (g0InvInt.submatrix id fun j => tauG ⟨b, j⟩) := by
  rw [rightCol_gaugeOfMatrix redG gauge_redG b]
  rfl

theorem leftRow_redGt (b : BlockIndex labels 1) :
    redGt.leftRow b = toC (gtInt.submatrix (fun i => tauGt ⟨b, i⟩) id) := by
  rw [leftRow_gaugeOfMatrix redGt gauge_redGt b]
  rfl

theorem rightCol_redGt (b : BlockIndex labels 1) :
    redGt.rightCol b = toC (gtInvInt.submatrix id fun j => tauGt ⟨b, j⟩) := by
  rw [rightCol_gaugeOfMatrix redGt gauge_redGt b]
  rfl

/-- The zero slot. -/
abbrev zeroSlot : BlockIndex labels 1 := Sum.inr ⟨0, Nat.one_pos⟩

/-- **The first reduction** (*The asymmetric fundamental theorem of matrix product states*, Example
6.16): `g = g₀` is a reduction in the order `(C₁, 0, C₂)`, `g₀ B^i g₀⁻¹ = C₁^i ⊕ T^i`, and the
reading maps and injections are the row blocks of `g₀` and the column blocks of `g₀⁻¹`. -/
theorem redG_spec : redG.z = 1 ∧ (redG.ord (Sum.inl slotC1)).val = 0 ∧
    (redG.ord zeroSlot).val = 1 ∧ (redG.ord (Sum.inl slotC2)).val = 2 ∧
    g0Int * g0InvInt = 1 ∧ (∀ i, toC g0Int * tensorB i * toC g0InvInt = toC (conjG i)) ∧
    redG.leftRow (Sum.inl slotC1) = toC !![2, 2, 1, 1; 0, 0, 0, 1] ∧
    redG.leftRow zeroSlot = toC !![1, 1, 1, 1] ∧
    redG.leftRow (Sum.inl slotC2) = toC !![0, -1, 0, 1] ∧
    redG.rightCol (Sum.inl slotC1) = toC !![1, -1; 0, 1; -1, -1; 0, 1] ∧
    redG.rightCol zeroSlot = toC !![-1; 0; 2; 0] ∧
    redG.rightCol (Sum.inl slotC2) = toC !![1; -1; 0; 0] := by
  refine ⟨rfl, rfl, rfl, rfl, by decide +kernel, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tensorB_eq_complexOfRing, ← complexOfRing_mul, ← complexOfRing_mul, conjG_eq]
  · exact (leftRow_redG (Sum.inl slotC1)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))
  · exact (leftRow_redG zeroSlot).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i; fin_cases j <;> decide))
  · exact (leftRow_redG (Sum.inl slotC2)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i; fin_cases j <;> decide))
  · exact (rightCol_redG (Sum.inl slotC1)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))
  · exact (rightCol_redG zeroSlot).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))
  · exact (rightCol_redG (Sum.inl slotC2)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))

/-- **The second reduction** (*The asymmetric fundamental theorem of matrix product states*, Example
6.16): `g_tilde = h P g₀` is a reduction in the order `(0, C₂, C₁')` onto `(C₁', C₂)`, with
`g_tilde B¹ g_tilde⁻¹` and `g_tilde B² g_tilde⁻¹` as printed, and its reading maps and injections
are the row blocks of `g_tilde` and the column blocks of `g_tilde⁻¹`. -/
theorem redGt_spec : redGt.z = 1 ∧ (redGt.ord zeroSlot).val = 0 ∧
    (redGt.ord (Sum.inl slotC2)).val = 1 ∧ (redGt.ord (Sum.inl slotC1)).val = 2 ∧
    hInt * permInt * g0Int = gtInt ∧ gtInt * gtInvInt = 1 ∧
    (∀ i, toC gtInt * tensorB i * toC gtInvInt = toC (conjGt i)) ∧
    redGt.leftRow zeroSlot = toC !![3, 2, 2, 3] ∧
    redGt.leftRow (Sum.inl slotC2) = toC !![-2, -3, -1, 1] ∧
    redGt.leftRow (Sum.inl slotC1) = toC !![2, 2, 1, 2; 0, 0, 0, 1] ∧
    redGt.rightCol zeroSlot = toC !![-1; 0; 2; 0] ∧
    redGt.rightCol (Sum.inl slotC2) = toC !![2; -1; -2; 0] ∧
    redGt.rightCol (Sum.inl slotC1) = toC !![4, -7; -1, 3; -5, 6; 0, 1] := by
  refine ⟨rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel, fun i => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [tensorB_eq_complexOfRing, ← complexOfRing_mul, ← complexOfRing_mul, conjGt_eq]
  · exact (leftRow_redGt zeroSlot).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i; fin_cases j <;> decide))
  · exact (leftRow_redGt (Sum.inl slotC2)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i; fin_cases j <;> decide))
  · exact (leftRow_redGt (Sum.inl slotC1)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))
  · exact (rightCol_redGt zeroSlot).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))
  · exact (rightCol_redGt (Sum.inl slotC2)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))
  · exact (rightCol_redGt (Sum.inl slotC1)).trans (congrArg toC
      (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> decide))

/-- **The reading maps of `C₂` are not proportional** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.16): `W_tilde_{C₂} = (-2, -3, -1, 1)` and `W_{C₂} = (0, -1, 0, 1)` are
not proportional. -/
theorem not_exists_left_redGt_eq_smul_left_redG : redGt.left slotC2 = toC !![-2, -3, -1, 1] ∧
    redG.left slotC2 = toC !![0, -1, 0, 1] ∧
    ¬ ∃ c : ℂ, redGt.left slotC2 = c • redG.left slotC2 := by
  have h1 : redGt.left slotC2 = toC !![-2, -3, -1, 1] := redGt_spec.2.2.2.2.2.2.2.2.1
  have h2 : redG.left slotC2 = toC !![0, -1, 0, 1] := redG_spec.2.2.2.2.2.2.2.2.1
  refine ⟨h1, h2, ?_⟩
  rintro ⟨c, hc⟩
  rw [h1, h2] at hc
  have h00 : toC !![(-2 : ℤ), -3, -1, 1] 0 0 = c * toC !![(0 : ℤ), -1, 0, 1] 0 0 := by
    rw [hc]; rfl
  simp [toC, complexOfRing_apply] at h00

/-- **The word traces** (*The asymmetric fundamental theorem of matrix product states*, Example
6.16): `tr B^w = tr C₁^w + tr C₂^w` for every nonempty word, and `tr B^∅ = 4`. -/
theorem trace_evalWord_tensorB_eq_add :
    (∀ w : List (Fin 2), w ≠ [] → (Kraus.evalWord tensorB w).trace =
      (Kraus.evalWord tensorC₁ w).trace + (Kraus.evalWord tensorC₂ w).trace) ∧
    (Kraus.evalWord tensorB []).trace = 4 := by
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [redG.trace_evalWord_eq_sum w hw, Fin.sum_univ_two]
    rfl
  · rw [Kraus.evalWord_nil, Matrix.trace_one, Fintype.card_fin]
    norm_num

/-! ### The flags and the matching -/

/-- `C₁' = Y C₁ Y⁻¹`. -/
theorem tensorC₁'_eq (i : Fin 2) : tensorC₁' i = matY * tensorC₁ i * !![1, -1; 0, 1] := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [tensorC₁', tensorC₁, Multiplicity.tensorC, matY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Matrix.single_apply]

theorem isNormal_tensorC₂ : Kraus.IsNormal tensorC₂ := by
  refine Kraus.IsInjective.isNormal (Submodule.eq_top_of_forall_single_mem _ fun x y => ?_)
  obtain rfl : x = 0 := Subsingleton.elim x 0
  obtain rfl : y = 0 := Subsingleton.elim y 0
  have h1 : Matrix.single (0 : Fin 1) (0 : Fin 1) (1 : ℂ) = tensorC₂ 0 := by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [tensorC₂]
  rw [h1]
  exact Submodule.subset_span ⟨0, rfl⟩

theorem isNormal_tensorC₁' : Kraus.IsNormal tensorC₁' := by
  refine isNormal_of_gaugeEquiv Multiplicity.isNormal_tensorC
    ⟨⟨matY, !![1, -1; 0, 1], ?_, ?_⟩, fun i => ?_⟩
  · ext a b; fin_cases a <;> fin_cases b <;> simp [matY, Matrix.mul_apply, Fin.sum_univ_two]
  · ext a b; fin_cases a <;> fin_cases b <;> simp [matY, Matrix.mul_apply, Fin.sum_univ_two]
  · exact tensorC₁'_eq i

theorem isNormal_blocks : ∀ s ∈ labels, Kraus.IsNormal (blocks s) := by
  intro s _
  fin_cases s
  · exact Multiplicity.isNormal_tensorC
  · exact isNormal_tensorC₂

theorem isNormal_blocks' : ∀ s ∈ labels, Kraus.IsNormal (blocks' s) := by
  intro s _
  fin_cases s
  · exact isNormal_tensorC₁'
  · exact isNormal_tensorC₂

theorem dims_pos : ∀ s ∈ labels, 0 < dims s := by
  intro s _
  fin_cases s <;> decide

theorem toC_g0Int_mulVec (v : Fin 4 → ℂ) :
    toC g0Int *ᵥ v = ![2 * v 0 + 2 * v 1 + v 2 + v 3, v 3, v 0 + v 1 + v 2 + v 3, -v 1 + v 3] := by
  ext i
  fin_cases i <;>
    simp [g0Int, toC, complexOfRing_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem toC_gtInt_mulVec (v : Fin 4 → ℂ) :
    toC gtInt *ᵥ v = ![3 * v 0 + 2 * v 1 + 2 * v 2 + 3 * v 3, -2 * v 0 - 3 * v 1 - v 2 + v 3,
      2 * v 0 + 2 * v 1 + v 2 + 2 * v 3, v 3] := by
  ext i
  fin_cases i <;>
    simp [gtInt, toC, complexOfRing_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- Membership in the flag of `g`: the coordinates `g₀ v` at the positions `≥ k` vanish. -/
theorem mem_flagVec_redG (k : Fin (labels.card + redG.z + 1)) (v : Fin 4 → ℂ) :
    v ∈ flagVec redG k ↔
      ∀ n : Fin 4, k.val ≤ (![0, 0, 1, 2] : Fin 4 → ℕ) n → (toC g0Int *ᵥ v) n = 0 := by
  have hpos : ∀ n : Fin 4, ((redG.ord (tauG.symm n).1).castSucc).val =
      (![0, 0, 1, 2] : Fin 4 → ℕ) n := by
    intro n; fin_cases n <;> rfl
  rw [mem_flagVec_gaugeOfMatrix redG gauge_redG]
  constructor
  · intro h n hn
    have := h (tauG.symm n) (Fin.le_def.2 (by rw [hpos]; exact hn))
    erw [Equiv.apply_symm_apply] at this
    exact this
  · intro h y hy
    obtain ⟨n, rfl⟩ := tauG.symm.surjective y
    erw [Equiv.apply_symm_apply]
    exact h n (by rw [← hpos]; exact Fin.le_def.1 hy)

/-- Membership in the flag of `g_tilde`: the coordinates `g_tilde v` at the positions `≥ k` vanish.
-/
theorem mem_flagVec_redGt (k : Fin (labels.card + redGt.z + 1)) (v : Fin 4 → ℂ) :
    v ∈ flagVec redGt k ↔
      ∀ n : Fin 4, k.val ≤ (![0, 1, 2, 2] : Fin 4 → ℕ) n → (toC gtInt *ᵥ v) n = 0 := by
  have hpos : ∀ n : Fin 4, ((redGt.ord (tauGt.symm n).1).castSucc).val =
      (![0, 1, 2, 2] : Fin 4 → ℕ) n := by
    intro n; fin_cases n <;> rfl
  rw [mem_flagVec_gaugeOfMatrix redGt gauge_redGt]
  constructor
  · intro h n hn
    have := h (tauGt.symm n) (Fin.le_def.2 (by rw [hpos]; exact hn))
    erw [Equiv.apply_symm_apply] at this
    exact this
  · intro h y hy
    obtain ⟨n, rfl⟩ := tauGt.symm.surjective y
    erw [Equiv.apply_symm_apply]
    exact h n (by rw [← hpos]; exact Fin.le_def.1 hy)

theorem mem_flagVec_redG_one (k : Fin (labels.card + redG.z + 1)) (hk : k.val = 1) (v : Fin 4 → ℂ) :
    v ∈ flagVec redG k ↔ v 0 + v 1 + v 2 + v 3 = 0 ∧ -v 1 + v 3 = 0 := by
  rw [mem_flagVec_redG, hk, toC_g0Int_mulVec]
  constructor
  · intro h
    exact ⟨by simpa using h 2 (by decide), by simpa using h 3 (by decide)⟩
  · rintro ⟨h2, h3⟩ n hn
    fin_cases n
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · simpa using h2
    · simpa using h3

theorem mem_flagVec_redG_two (k : Fin (labels.card + redG.z + 1)) (hk : k.val = 2) (v : Fin 4 → ℂ) :
    v ∈ flagVec redG k ↔ -v 1 + v 3 = 0 := by
  rw [mem_flagVec_redG, hk, toC_g0Int_mulVec]
  constructor
  · intro h
    simpa using h 3 (by decide)
  · rintro h3 n hn
    fin_cases n
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · simpa using h3

theorem mem_flagVec_redGt_one (k : Fin (labels.card + redGt.z + 1)) (hk : k.val = 1)
    (v : Fin 4 → ℂ) :
    v ∈ flagVec redGt k ↔ -2 * v 0 - 3 * v 1 - v 2 + v 3 = 0 ∧
      2 * v 0 + 2 * v 1 + v 2 + 2 * v 3 = 0 ∧ v 3 = 0 := by
  rw [mem_flagVec_redGt, hk, toC_gtInt_mulVec]
  constructor
  · intro h
    exact ⟨by simpa using h 1 (by decide), by simpa using h 2 (by decide),
      by simpa using h 3 (by decide)⟩
  · rintro ⟨h1, h2, h3⟩ n hn
    fin_cases n
    · exact absurd hn (by decide)
    · simpa using h1
    · simpa using h2
    · simpa using h3

theorem mem_flagVec_redGt_two (k : Fin (labels.card + redGt.z + 1)) (hk : k.val = 2)
    (v : Fin 4 → ℂ) :
    v ∈ flagVec redGt k ↔ 2 * v 0 + 2 * v 1 + v 2 + 2 * v 3 = 0 ∧ v 3 = 0 := by
  rw [mem_flagVec_redGt, hk, toC_gtInt_mulVec]
  constructor
  · intro h
    exact ⟨by simpa using h 2 (by decide), by simpa using h 3 (by decide)⟩
  · rintro ⟨h2, h3⟩ n hn
    fin_cases n
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · simpa using h2
    · simpa using h3

/-- The matching of the two reductions. -/
noncomputable abbrev positionMatching : Fin (labels.card + redG.z) ≃ Fin (labels.card + redGt.z) :=
  redG.matching redGt isNormal_blocks dims_pos isNormal_blocks' dims_pos

theorem positionMatching_ord_slotC1 :
    positionMatching (redG.ord (Sum.inl slotC1)) = redGt.ord (Sum.inl slotC1) := by
  refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨![1, 0, -1, 0], ?_, ?_, ?_⟩ ?_
  · rw [mem_flagVec_redG_one _ rfl]; norm_num
  · rw [flagVec_eq_top _ _ rfl]; exact Submodule.mem_top
  · rw [flagVec_eq_bot _ _ rfl, Submodule.mem_bot]
    intro h; have := congrFun h 0; simp at this
  · intro j hj v hv1 hv2
    have hj : j.val = 0 ∨ j.val = 1 := by
      have := Fin.lt_def.1 hj
      have h2 : (redGt.ord (Sum.inl slotC1)).val = 2 := rfl
      omega
    rw [mem_flagVec_redG_one _ rfl] at hv1
    have hv2' : 2 * v 0 + 2 * v 1 + v 2 + 2 * v 3 = 0 ∧ v 3 = 0 := by
      rcases hj with hj | hj
      · exact ((mem_flagVec_redGt_one _ (by rw [Fin.val_succ, hj]) v).1 hv2).2
      · exact (mem_flagVec_redGt_two _ (by rw [Fin.val_succ, hj]) v).1 hv2
    have hv : v = 0 := by
      obtain ⟨a, b⟩ := hv1
      obtain ⟨c, e⟩ := hv2'
      ext i; fin_cases i
      · simp; linear_combination -a + b + c - 2 * e
      · simp; linear_combination -b + e
      · simp; linear_combination 2 * a - c
      · simp; linear_combination e
    rw [hv]
    exact Submodule.zero_mem _

theorem positionMatching_ord_zeroSlot :
    positionMatching (redG.ord zeroSlot) = redGt.ord zeroSlot := by
  refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨![-1, 0, 2, 0], ?_, ?_, ?_⟩ ?_
  · rw [mem_flagVec_redG_two _ rfl]; norm_num
  · rw [mem_flagVec_redGt_one _ rfl]; norm_num
  · rw [mem_flagVec_redG_one _ rfl]; norm_num
  · intro j hj
    exfalso
    have := Fin.lt_def.1 hj
    have h0 : (redGt.ord zeroSlot).val = 0 := rfl
    omega

theorem positionMatching_ord_slotC2 :
    positionMatching (redG.ord (Sum.inl slotC2)) = redGt.ord (Sum.inl slotC2) := by
  refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨![2, -1, -2, 0], ?_, ?_, ?_⟩ ?_
  · rw [flagVec_eq_top _ _ rfl]; exact Submodule.mem_top
  · rw [mem_flagVec_redGt_two _ rfl]; norm_num
  · rw [mem_flagVec_redG_two _ rfl]; norm_num
  · intro j hj v _ hv2
    have hj0 : j.val = 0 := by
      have := Fin.lt_def.1 hj
      have h1 : (redGt.ord (Sum.inl slotC2)).val = 1 := rfl
      omega
    rw [mem_flagVec_redGt_one _ (by rw [Fin.val_succ, hj0])] at hv2
    rw [mem_flagVec_redG_two _ rfl]
    obtain ⟨a, b, c⟩ := hv2
    linear_combination a + b - 2 * c

/-- **The flags and the matching** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.16): the flags `M₁ = span{(1, 0, -1, 0), (-1, 1, -1, 1)}`, `M₂ = M₁ + ℂ(-1, 0, 2, 0)`,
`M_tilde₁ = ℂ(-1, 0, 2, 0)`, `M_tilde₂ = M_tilde₁ + ℂ(2, -1, -2, 0)` (as solution sets of the
printed rows of `g₀` and `g_tilde`), and the matching `π(1) = 3`, `π(2) = 1`, `π(3) = 2`. -/
theorem flagVec_redG_redGt_and_matching :
    (∀ k : Fin (labels.card + redG.z + 1), k.val = 1 →
      flagVec redG k = Submodule.span ℂ {![1, 0, -1, 0], ![-1, 1, -1, 1]}) ∧
    (∀ k : Fin (labels.card + redG.z + 1), k.val = 2 →
      flagVec redG k = Submodule.span ℂ {![1, 0, -1, 0], ![-1, 1, -1, 1], ![-1, 0, 2, 0]}) ∧
    (∀ k : Fin (labels.card + redGt.z + 1), k.val = 1 →
      flagVec redGt k = Submodule.span ℂ {![-1, 0, 2, 0]}) ∧
    (∀ k : Fin (labels.card + redGt.z + 1), k.val = 2 →
      flagVec redGt k = Submodule.span ℂ {![-1, 0, 2, 0], ![2, -1, -2, 0]}) ∧
    (positionMatching (redG.ord (Sum.inl slotC1))).val = 2 ∧
    (positionMatching (redG.ord zeroSlot)).val = 0 ∧
    (positionMatching (redG.ord (Sum.inl slotC2))).val = 1 ∧
    (redG.ord (Sum.inl slotC1)).val = 0 ∧ (redG.ord zeroSlot).val = 1 ∧
    (redG.ord (Sum.inl slotC2)).val = 2 := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
    by rw [positionMatching_ord_slotC1]; rfl, by rw [positionMatching_ord_zeroSlot]; rfl,
    by rw [positionMatching_ord_slotC2]; rfl, rfl, rfl, rfl⟩
  · ext v
    rw [mem_flagVec_redG_one k hk, Submodule.mem_span_pair]
    constructor
    · rintro ⟨h2, h3⟩
      have e3 : v 3 = v 1 := by linear_combination h3
      have e2 : v 2 = -v 0 - 2 * v 1 := by linear_combination h2 - h3
      refine ⟨2 * v 0 + 2 * v 1 + v 2 + v 3, v 3, ?_⟩
      ext i; fin_cases i <;> simp [e2, e3] <;> ring
    · rintro ⟨a, b, rfl⟩
      constructor <;> simp
  · ext v
    rw [mem_flagVec_redG_two k hk, Submodule.mem_span_insert]
    simp_rw [Submodule.mem_span_pair]
    constructor
    · intro h3
      have e3 : v 3 = v 1 := by linear_combination h3
      refine ⟨2 * v 0 + 2 * v 1 + v 2 + v 3, _, ⟨v 3, v 0 + v 1 + v 2 + v 3, rfl⟩, ?_⟩
      ext i; fin_cases i <;> simp [e3] <;> ring
    · rintro ⟨a, z, ⟨b, c, rfl⟩, rfl⟩
      simp
  · ext v
    rw [mem_flagVec_redGt_one k hk, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have e3 : v 3 = 0 := h3
      have e1 : v 1 = 0 := by linear_combination -h1 - h2 + 3 * h3
      have e2 : v 2 = -2 * v 0 := by linear_combination h2 - 2 * e1 - 2 * h3
      refine ⟨-v 0, ?_⟩
      ext i; fin_cases i <;> simp [e1, e2, e3]
      ring
    · rintro ⟨a, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring
  · ext v
    rw [mem_flagVec_redGt_two k hk, Submodule.mem_span_pair]
    constructor
    · rintro ⟨h2, h3⟩
      have e3 : v 3 = 0 := h3
      have e2 : v 2 = -2 * v 0 - 2 * v 1 := by linear_combination h2 - 2 * h3
      refine ⟨3 * v 0 + 2 * v 1 + 2 * v 2 + 3 * v 3, -2 * v 0 - 3 * v 1 - v 2 + v 3, ?_⟩
      ext i; fin_cases i <;> simp [e2, e3] <;> ring
    · rintro ⟨a, b, rfl⟩
      constructor <;> simp
      ring

/-! ### Two compressions with different flags, on the three pairs -/

/-- The subspace `U = M_k ∩ M_tilde_{π(k)}` of the pair at the position `k` of `g`. -/
noncomputable abbrev subspaceU (k : Fin (labels.card + redG.z)) : Submodule ℂ (Fin 4 → ℂ) :=
  ((redG.flag k.succ ⊓ redGt.flag (positionMatching k).succ).restrictScalars ℂ).map
    (WordModule.toVec tensorB).toLinearMap

/-- The subspace `K = M_{k-1} ∩ M_tilde_{π(k)}`. -/
noncomputable abbrev subspaceK (k : Fin (labels.card + redG.z)) : Submodule ℂ (Fin 4 → ℂ) :=
  ((redG.flag k.castSucc ⊓ redGt.flag (positionMatching k).succ).restrictScalars ℂ).map
    (WordModule.toVec tensorB).toLinearMap

/-- The subspace `N = M_{k-1} + M_tilde_{π(k)-1}`. -/
noncomputable abbrev subspaceN (k : Fin (labels.card + redG.z)) : Submodule ℂ (Fin 4 → ℂ) :=
  ((redG.flag k.castSucc ⊔ redGt.flag (positionMatching k).castSucc).restrictScalars ℂ).map
    (WordModule.toVec tensorB).toLinearMap

/-- **The three matched pairs** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.16): for the `C₁` pair, `U = span{(1, 0, -1, 0), (-2, 1, 0, 1)}`, `K = 0`,
`N = span{(-1, 0, 2, 0), (2, -1, -2, 0)}`; the intertwiner is `X = Y`, that is
`W_tilde_{C₁'} = Y W_{C₁}` on `U` and `Y C₁^i = C₁'^i Y`; and `V_tilde_{C₁'} - V_{C₁} Y⁻¹` is the
printed `4 × 2` matrix, with columns in `N`. For the zero block and for `C₂` the intertwiners are
`1` (`W_tilde = W` on `U`), with `dim K = 0` and `dim K = 1`. -/
theorem inf_sup_intertwiner_redG_redGt :
    subspaceU (redG.ord (Sum.inl slotC1)) = Submodule.span ℂ {![1, 0, -1, 0], ![-2, 1, 0, 1]} ∧
    subspaceK (redG.ord (Sum.inl slotC1)) = ⊥ ∧
    subspaceN (redG.ord (Sum.inl slotC1)) = Submodule.span ℂ {![-1, 0, 2, 0], ![2, -1, -2, 0]} ∧
    (∀ v ∈ subspaceU (redG.ord (Sum.inl slotC1)),
      redGt.left slotC1 *ᵥ v = matY *ᵥ (redG.left slotC1 *ᵥ v)) ∧
    (∀ i, matY * tensorC₁ i = tensorC₁' i * matY) ∧
    @id (Matrix (Fin 4) (Fin 2) ℂ) (redGt.right slotC1) -
        @id (Matrix (Fin 4) (Fin 2) ℂ) (redG.right slotC1) * !![(1 : ℂ), -1; 0, 1] =
      toC !![3, -5; -1, 2; -4, 6; 0, 0] ∧
    (∀ j, (fun i => (toC !![(3 : ℤ), -5; -1, 2; -4, 6; 0, 0]) i j) ∈
      subspaceN (redG.ord (Sum.inl slotC1))) ∧
    (∀ v ∈ subspaceU (redG.ord zeroSlot),
      redGt.leftRow zeroSlot *ᵥ v = redG.leftRow zeroSlot *ᵥ v) ∧
    Module.finrank ℂ (subspaceK (redG.ord zeroSlot)) = 0 ∧
    (∀ v ∈ subspaceU (redG.ord (Sum.inl slotC2)),
      redGt.left slotC2 *ᵥ v = redG.left slotC2 *ᵥ v) ∧
    Module.finrank ℂ (subspaceK (redG.ord (Sum.inl slotC2))) = 1 := by
  have hU1 : subspaceU (redG.ord (Sum.inl slotC1)) = flagVec redG ⟨1, by decide⟩ := by
    rw [subspaceU, positionMatching_ord_slotC1, map_toVec_inf]
    change flagVec redG _ ⊓ flagVec redGt _ = _
    rw [flagVec_eq_top redGt _ rfl, inf_top_eq]
    rfl
  have hK1 : subspaceK (redG.ord (Sum.inl slotC1)) = ⊥ := by
    rw [subspaceK, positionMatching_ord_slotC1, map_toVec_inf]
    change flagVec redG _ ⊓ flagVec redGt _ = _
    rw [flagVec_eq_bot redG _ rfl, bot_inf_eq]
  have hN1 : subspaceN (redG.ord (Sum.inl slotC1)) = flagVec redGt ⟨2, by decide⟩ := by
    rw [subspaceN, positionMatching_ord_slotC1, map_toVec_sup]
    change flagVec redG _ ⊔ flagVec redGt _ = _
    rw [flagVec_eq_bot redG _ rfl, bot_sup_eq]
    rfl
  have hU0 : subspaceU (redG.ord zeroSlot) =
      flagVec redGt ⟨1, by decide⟩ ⊓ flagVec redG ⟨2, by decide⟩ := by
    rw [subspaceU, positionMatching_ord_zeroSlot, map_toVec_inf, inf_comm]
    rfl
  have hK0 : subspaceK (redG.ord zeroSlot) =
      flagVec redG ⟨1, by decide⟩ ⊓ flagVec redGt ⟨1, by decide⟩ := by
    rw [subspaceK, positionMatching_ord_zeroSlot, map_toVec_inf]
    rfl
  have hU2 : subspaceU (redG.ord (Sum.inl slotC2)) = flagVec redGt ⟨2, by decide⟩ := by
    rw [subspaceU, positionMatching_ord_slotC2, map_toVec_inf]
    change flagVec redG _ ⊓ flagVec redGt _ = _
    rw [flagVec_eq_top redG _ rfl, top_inf_eq]
    rfl
  have hK2 : subspaceK (redG.ord (Sum.inl slotC2)) =
      flagVec redG ⟨2, by decide⟩ ⊓ flagVec redGt ⟨2, by decide⟩ := by
    rw [subspaceK, positionMatching_ord_slotC2, map_toVec_inf]
    rfl
  have hWG1 : redG.left slotC1 = toC !![2, 2, 1, 1; 0, 0, 0, 1] := redG_spec.2.2.2.2.2.2.1
  have hWGt1 : redGt.left slotC1 = toC !![2, 2, 1, 2; 0, 0, 0, 1] :=
    redGt_spec.2.2.2.2.2.2.2.2.2.1
  have hVG1 : redG.right slotC1 = toC !![1, -1; 0, 1; -1, -1; 0, 1] :=
    redG_spec.2.2.2.2.2.2.2.2.2.1
  have hVGt1 : redGt.right slotC1 = toC !![4, -7; -1, 3; -5, 6; 0, 1] :=
    redGt_spec.2.2.2.2.2.2.2.2.2.2.2.2
  have hWG0 : redG.leftRow zeroSlot = toC !![1, 1, 1, 1] := redG_spec.2.2.2.2.2.2.2.1
  have hWGt0 : redGt.leftRow zeroSlot = toC !![3, 2, 2, 3] := redGt_spec.2.2.2.2.2.2.2.1
  have hWG2 : redG.left slotC2 = toC !![0, -1, 0, 1] := redG_spec.2.2.2.2.2.2.2.2.1
  have hWGt2 : redGt.left slotC2 = toC !![-2, -3, -1, 1] := redGt_spec.2.2.2.2.2.2.2.2.1
  refine ⟨?_, hK1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hU1]
    ext v
    rw [mem_flagVec_redG_one _ rfl, Submodule.mem_span_pair]
    constructor
    · rintro ⟨h2, h3⟩
      have e3 : v 3 = v 1 := by linear_combination h3
      have e2 : v 2 = -v 0 - 2 * v 1 := by linear_combination h2 - h3
      refine ⟨v 0 + 2 * v 1, v 1, ?_⟩
      ext i; fin_cases i <;> simp [e2, e3] <;> ring
    · rintro ⟨a, b, rfl⟩
      constructor <;> simp
      ring
  · rw [hN1]
    exact (flagVec_redG_redGt_and_matching.2.2.2.1 _ rfl)
  · intro v _
    rw [hWGt1, hWG1]
    ext i; fin_cases i <;>
      simp [toC, complexOfRing_apply, matY, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · intro i
    have hYi : !![(1 : ℂ), -1; 0, 1] * matY = 1 := by
      ext a b; fin_cases a <;> fin_cases b <;> simp [matY, Matrix.mul_apply, Fin.sum_univ_two]
    rw [tensorC₁'_eq, Matrix.mul_assoc, hYi, Matrix.mul_one]
  · rw [hVGt1, hVG1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toC, complexOfRing_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · intro j
    rw [hN1, mem_flagVec_redGt_two _ rfl]
    fin_cases j <;> simp [toC, complexOfRing_apply] <;> norm_num
  · intro v hv
    rw [hU0] at hv
    obtain ⟨hv1, -⟩ := Submodule.mem_inf.1 hv
    rw [mem_flagVec_redGt_one _ rfl] at hv1
    obtain ⟨h1, h2, h3⟩ := hv1
    have e1 : v 1 = 0 := by linear_combination -h1 - h2 + 3 * h3
    have e2 : v 2 = -2 * v 0 := by linear_combination h2 - 2 * e1 - 2 * h3
    rw [hWGt0, hWG0]
    ext i; fin_cases i
    simp [toC, complexOfRing_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e1, e2, h3]
    ring
  · rw [hK0]
    have : flagVec redG ⟨1, by decide⟩ ⊓ flagVec redGt ⟨1, by decide⟩ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
      rw [mem_flagVec_redG_one _ rfl] at hv1
      rw [mem_flagVec_redGt_one _ rfl] at hv2
      obtain ⟨a, b⟩ := hv1
      obtain ⟨c1, c, e⟩ := hv2
      rw [Submodule.mem_bot]
      ext i; fin_cases i
      · simp; linear_combination -a + b + c - 2 * e
      · simp; linear_combination -b + e
      · simp; linear_combination 2 * a - c
      · simp; linear_combination e
    rw [this, finrank_bot]
  · intro v hv
    rw [hU2, mem_flagVec_redGt_two _ rfl] at hv
    obtain ⟨h2, h3⟩ := hv
    have e2 : v 2 = -2 * v 0 - 2 * v 1 := by linear_combination h2 - 2 * h3
    rw [hWGt2, hWG2]
    ext i; fin_cases i
    simp [toC, complexOfRing_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e2, h3]
    ring
  · rw [hK2]
    have : flagVec redG ⟨2, by decide⟩ ⊓ flagVec redGt ⟨2, by decide⟩ =
        Submodule.span ℂ {![-1, 0, 2, 0]} := by
      ext v
      rw [Submodule.mem_inf, mem_flagVec_redG_two _ rfl, mem_flagVec_redGt_two _ rfl,
        Submodule.mem_span_singleton]
      constructor
      · rintro ⟨h3', h2, h3⟩
        have e1 : v 1 = 0 := by linear_combination -h3' + h3
        have e2 : v 2 = -2 * v 0 := by linear_combination h2 - 2 * e1 - 2 * h3
        refine ⟨-v 0, ?_⟩
        ext i; fin_cases i <;> simp [e1, e2, h3]
        ring
      · rintro ⟨a, rfl⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp
        ring
    rw [this, finrank_span_singleton]
    intro h
    have := congrFun h 0
    simp at this

end Worked

end MultiBlockExamples
