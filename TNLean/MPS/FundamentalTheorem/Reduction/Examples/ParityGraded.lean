/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Basis
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# A concrete parity-weighted tensor example

The bond-two tensor `A^0 = [[1,0],[0,0]]`, `A^1 = [[0,1],[1,0]]` is normal at word
length two. Its copies with weights `+1` and `-1` have total periodic coefficient
`tr(A^w) + tr((-A)^w) = (1 + (-1)^L) tr(A^w)` for a word of length `L > 0`.
This factor selects even chain lengths: it is `2` for even `L` and `0` for odd `L`.
It is not a proof of a physical occupation-parity projection. No Kitaev Hamiltonian,
canonical anticommutation relations, or fermion-parity boundary condition is defined here.

The explicit construction is recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §4.
The five-dimensional source `parB` is given directly as two integer matrices, not as
a stacked MPO product. A change of bond coordinates puts its diagonal blocks in the
form `A, -A, 0`. The residual has zero products at length three but a nonzero product
at length two. The weight-`-1` target has no nonzero sitewise intertwiner in either
direction, despite the word-level compression.

The compression theorem cited below is Theorem 7.7 of
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`.

## Main definitions

* `ParityGraded.parA`: the bond-two normal tensor of the note.
* `ParityGraded.parB`: the five-dimensional mixed-basis source.
* `ParityGraded.parityGraded_compression`: the multi-block compression datum of Theorem 7.7.

## Main results

* `ParityGraded.parA_isNormal`: `parA` is normal at word length two.
* `ParityGraded.parityGraded_trace_evalWord`: the word-trace identity
  `tr(B^w) = (1 + (-1)^|w|) tr(A^w)`.
* `ParityGraded.parityGraded_dim_eq`: the dimension count `5 = 2 + 2 + 1`.
* `ParityGraded.parityGraded_evalWord_remainder_eq_zero`: nilpotency of the remainder at length
  three.
* `ParityGraded.parityGraded_remainder_sq_ne_zero`: the bound of the theorem is attained: the
  residual does not already vanish at length two.
* `ParityGraded.parNeg_right_intertwiner_eq_zero`, `ParityGraded.parNeg_left_intertwiner_eq_zero`:
  the weight `-1` block has no nonzero sitewise intertwiner in either direction, so the
  word-level compression of the theorem is the strongest local relation available for that
  block.
-/

noncomputable section

open scoped Matrix

namespace ParityGraded

open MPSTensor

/-! ### The bond-two tensor and its sign-weighted targets -/

/-- The integer matrices of the bond-two tensor of Example PAR (construction note, §4). -/
def parAInt : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 1; 1, 0]

/-- **The bond-two tensor of Example PAR.** Normal at word length two (construction note, §4). -/
def parA : MPSTensor 2 2 := fun i => complexOfInt (parAInt i)

theorem parA_eq (i : Fin 2) : parA i = complexOfInt (parAInt i) := rfl

/-- The bond dimensions of the two target slots of Example PAR: both blocks have bond
dimension two. -/
abbrev parDim : Fin 2 → ℕ := fun _ => 2

/-- The integer matrices of the two target blocks: `parA` with weight `+1` and with weight
`-1`. -/
def parTargetsInt : (s : Fin 2) → Fin 2 → Matrix (Fin (parDim s)) (Fin (parDim s)) ℤ
  | 0 => parAInt
  | 1 => fun i => -(parAInt i)

/-- **The two target blocks of Example PAR**: `parA` with weight `+1`, and `parA` with weight
`-1` (construction note, §4). These are inequivalent simple modules, since `tr(A^0) = 1 ≠ -1 = tr((-A)^0)`,
so no gauge can relate them. -/
def parTargets : (s : Fin 2) → MPSTensor 2 (parDim s)
  | 0 => parA
  | 1 => (-1 : ℂ) • parA

theorem parTargets_eq (s i : Fin 2) : parTargets s i = complexOfInt (parTargetsInt s i) := by
  fin_cases s
  · rfl
  · change ((-1 : ℂ) • parA) i = complexOfInt (-(parAInt i))
    rw [Pi.smul_apply, neg_one_smul, parA_eq, complexOfInt_neg]

/-! ### Normality of `parA` at word length two -/

private theorem parA_mul_00_int : parAInt 0 * parAInt 0 = !![1, 0; 0, 0] := by decide

private theorem parA_mul_01_int : parAInt 0 * parAInt 1 = !![0, 1; 0, 0] := by decide

private theorem parA_mul_10_int : parAInt 1 * parAInt 0 = !![0, 0; 1, 0] := by decide

private theorem parA_mul_11_int : parAInt 1 * parAInt 1 = !![1, 0; 0, 1] := by decide

private theorem parA_mul_00 : parA 0 * parA 0 = complexOfInt !![1, 0; 0, 0] := by
  simp only [parA_eq]; rw [← complexOfInt_mul, parA_mul_00_int]

private theorem parA_mul_01 : parA 0 * parA 1 = complexOfInt !![0, 1; 0, 0] := by
  simp only [parA_eq]; rw [← complexOfInt_mul, parA_mul_01_int]

private theorem parA_mul_10 : parA 1 * parA 0 = complexOfInt !![0, 0; 1, 0] := by
  simp only [parA_eq]; rw [← complexOfInt_mul, parA_mul_10_int]

private theorem parA_mul_11 : parA 1 * parA 1 = complexOfInt !![1, 0; 0, 1] := by
  simp only [parA_eq]; rw [← complexOfInt_mul, parA_mul_11_int]

/-- Each matrix unit of `M₂` is a length-two word of `parA`, or a difference of two. -/
private theorem parA_single_00 :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) = parA 0 * parA 0 := by
  rw [parA_mul_00]; ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply, complexOfInt]

private theorem parA_single_01 :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) = parA 0 * parA 1 := by
  rw [parA_mul_01]; ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply, complexOfInt]

private theorem parA_single_10 :
    Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) = parA 1 * parA 0 := by
  rw [parA_mul_10]; ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply, complexOfInt]

private theorem parA_single_11 :
    Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = parA 1 * parA 1 - parA 0 * parA 0 := by
  rw [parA_mul_11, parA_mul_00]; ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply, complexOfInt]

/-- **`parA` is normal at word length two** (construction note, §4): its length-two words span the full
two-by-two matrix algebra. -/
theorem parA_isNormal : Kraus.IsNormal parA := by
  refine ⟨2, two_pos, ?_⟩
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  set T := Submodule.span ℂ
    (Set.range fun σ : Fin 2 → Fin 2 => Kraus.evalWord parA (List.ofFn σ)) with hT
  have hword : ∀ a b : Fin 2, parA a * parA b ∈ T := by
    intro a b
    refine Submodule.subset_span ⟨![a, b], ?_⟩
    simp [Kraus.evalWord, List.ofFn_succ]
  have m00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ T := by
    rw [parA_single_00]; exact hword 0 0
  have m01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ T := by
    rw [parA_single_01]; exact hword 0 1
  have m10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ T := by
    rw [parA_single_10]; exact hword 1 0
  have m11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ T := by
    rw [parA_single_11]; exact T.sub_mem (hword 1 1) (hword 0 0)
  have hunit : ∀ i j : Fin 2, Matrix.single i j (1 : ℂ) ∈ T := by
    intro i j
    fin_cases i <;> fin_cases j
    exacts [m00, m01, m10, m11]
  exact T.eq_top_of_forall_single_mem hunit

/-! ### The five-dimensional mixed-basis source -/

/-- The integer matrices of the five-dimensional mixed-basis source of Example PAR, presented
in an integer basis in which neither letter has a zero row or column, so the flag produced by
the theorem is invisible on the nose (construction note, §4). -/
def parBInt : Fin 2 → Matrix (Fin 5) (Fin 5) ℤ
  | 0 => !![-1, 1, -1, 1, 3;
             2, 2, -2, -1, 0;
             1, 2, -2, 0, 2;
             1, 3, -3, -1, 2;
             -1, 0, 0, 1, 2]
  | 1 => !![3, 1, 0, -2, -3;
            -3, 1, -1, 2, 5;
            -1, 2, -1, 1, 3;
            0, 1, -1, -1, 1;
            2, 1, 0, -1, -2]

/-- **The five-dimensional mixed-basis source of Example PAR** (construction note, §4). -/
def parB : MPSTensor 2 5 := fun i => complexOfInt (parBInt i)

theorem parB_eq (i : Fin 2) : parB i = complexOfInt (parBInt i) := rfl

/-! ### The gauge and the flag -/

/-- The change of bond coordinates of Example PAR, recorded as `G = S⁻¹` for the mixing
integer matrix `S` of the note (construction note, §4). -/
def parGaugeInt : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, -1, 1, 0, 0;
     1, 1, 0, -1, -1;
     -1, 0, 0, 1, 1;
     1, 0, 0, 0, -1;
     0, 1, -1, 0, 1]

/-- The inverse change of bond coordinates of Example PAR: the mixing integer matrix `S` of the
note. -/
def parGaugeInvInt : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 0, 0, 1, 1;
     0, 1, 1, 0, 0;
     1, 1, 1, 0, 0;
     0, 0, 1, 1, 0;
     1, 0, 0, 0, 1]

theorem parGauge_mul_inv : parGaugeInt * parGaugeInvInt = 1 := by decide

theorem parGaugeInv_mul : parGaugeInvInt * parGaugeInt = 1 := by decide

theorem parGaugeComplex_mul_inv :
    complexOfInt parGaugeInt * complexOfInt parGaugeInvInt = 1 := by
  rw [← complexOfInt_mul, parGauge_mul_inv, complexOfInt_one]

theorem parGaugeComplex_inv_mul :
    complexOfInt parGaugeInvInt * complexOfInt parGaugeInt = 1 := by
  rw [← complexOfInt_mul, parGaugeInv_mul, complexOfInt_one]

/-- The slots of Example PAR: the weight `+1` and weight `-1` copies of `parA`. -/
abbrev parSlots : Finset (Fin 2) := Finset.univ

/-- The block ordering of Example PAR: the weight `+1` block first, the weight `-1` block
second, and the single zero slot last. -/
def parOrd : BlockIndex parSlots 1 ≃ Fin 3 where
  toFun := Sum.elim (fun s => ![(0 : Fin 3), 1] s.1) ![2]
  invFun
    | 0 => Sum.inl ⟨0, Finset.mem_univ 0⟩
    | 1 => Sum.inl ⟨1, Finset.mem_univ 1⟩
    | 2 => Sum.inr 0
  left_inv := by decide
  right_inv := by decide

/-- The position in the flag of the first coordinate of each block of Example PAR. -/
def parOffset : BlockIndex parSlots 1 → ℕ := Sum.elim (fun s => ![0, 2] s.1) ![4]

/-- The bond coordinate attached to a graded coordinate of Example PAR. -/
def parCoordNat (x : BlockSpace parDim parSlots 1) : ℕ := parOffset x.1 + (x.2 : ℕ)

theorem parCoordNat_lt (x : BlockSpace parDim parSlots 1) : parCoordNat x < 5 := by
  revert x; decide

/-- The labelling of the five bond coordinates of Example PAR by the graded block space. -/
def parTau : BlockSpace parDim parSlots 1 ≃ Fin 5 where
  toFun x := ⟨parCoordNat x, parCoordNat_lt x⟩
  invFun
    | 0 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, ⟨1, by decide⟩⟩
    | 2 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, ⟨0, by decide⟩⟩
    | 3 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, ⟨1, by decide⟩⟩
    | 4 => ⟨Sum.inr 0, ⟨0, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

/-- The gauge of Example PAR. -/
def parGauge : (Fin 5 → ℂ) ≃ₗ[ℂ] (BlockSpace parDim parSlots 1 → ℂ) :=
  gaugeOfMatrix parTau (complexOfInt parGaugeInt) (complexOfInt parGaugeInvInt)
    parGaugeComplex_mul_inv parGaugeComplex_inv_mul

/-- The letters of Example PAR in the block coordinates: block upper triangular, with `parA`
carried at weight `+1` on the first diagonal block, at weight `-1` on the second, and zero on
the third (construction note, §4). -/
def parConjInt : Fin 2 → Matrix (Fin 5) (Fin 5) ℤ
  | 0 => !![1, 0, 1, 0, 1;
            0, 0, 0, 1, 0;
            0, 0, -1, 0, 2;
            0, 0, 0, 0, 1;
            0, 0, 0, 0, 0]
  | 1 => !![0, 1, 0, 1, 0;
            1, 0, 2, 0, 1;
            0, 0, 0, -1, 1;
            0, 0, -1, 0, 0;
            0, 0, 0, 0, 0]

theorem parB_conj_int (i : Fin 2) :
    parGaugeInt * parBInt i * parGaugeInvInt = parConjInt i := by
  revert i; decide

theorem parB_conjMatrix (i : Fin 2) :
    conjMatrix parGauge (parB i) = (complexOfInt (parConjInt i)).submatrix parTau parTau := by
  rw [parGauge, conjMatrix_gaugeOfMatrix, parB_eq, ← complexOfInt_mul, ← complexOfInt_mul,
    parB_conj_int]

/-! ### The compression datum -/

private theorem parB_triangular_int (i : Fin 2)
    (x y : BlockSpace parDim parSlots 1) (h : parOrd y.1 < parOrd x.1) :
    parConjInt i (parTau x) (parTau y) = 0 := by
  revert i x y; decide

private theorem parB_matched_int (i : Fin 2) (s : Fin 2) (p q : Fin (parDim s)) :
    parConjInt i (parTau ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, p⟩)
        (parTau ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, q⟩) = parTargetsInt s i p q := by
  revert i; fin_cases s <;> revert p q <;> decide

private theorem parB_unmatched_int (i : Fin 2) (t : Fin 1) (p q : Fin 1) :
    parConjInt i (parTau ⟨Sum.inr t, p⟩) (parTau ⟨Sum.inr t, q⟩) = 0 := by
  revert i t p q; decide

/-- **The multi-block asymmetric compression datum of Example PAR** (construction note, Theorem 7.7,
clauses (i)–(iii), §4). -/
def parityGraded_compression : MultiBlockCompression parB parSlots parTargets where
  z := 1
  ord := parOrd
  gauge := parGauge
  triangular i x y h := by
    rw [parB_conjMatrix, Matrix.submatrix_apply, complexOfInt_apply, Int.cast_eq_zero]
    exact parB_triangular_int i x y h
  matched i s := by
    obtain ⟨s, hs⟩ := s
    ext p q
    rw [Matrix.blockDiag'_apply, parB_conjMatrix, Matrix.submatrix_apply, complexOfInt_apply,
      parTargets_eq, complexOfInt_apply, Int.cast_inj]
    exact parB_matched_int i s p q
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, parB_conjMatrix, Matrix.submatrix_apply, complexOfInt_apply,
      Matrix.zero_apply, Int.cast_eq_zero]
    exact parB_unmatched_int i t p q

/-! ### Consequences -/

/-- At positive word length `L`, the trace of the source word is
`(1 + (-1)^L) tr(A^w)`. The coefficient is the power sum of the weights `{+1, -1}`,
not a per-letter rescaling by `1 + (-1)^L` (data note, §4). -/
theorem parityGraded_trace_evalWord (w : List (Fin 2)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord parB w) =
      (1 + (-1 : ℂ) ^ w.length) * Matrix.trace (Kraus.evalWord parA w) := by
  have h := parityGraded_compression.trace_evalWord_eq_sum w hw
  rw [show parSlots = Finset.univ from rfl, Fin.sum_univ_two] at h
  have h0 : Matrix.trace (Kraus.evalWord (parTargets 0) w) =
      Matrix.trace (Kraus.evalWord parA w) := rfl
  have h1 : Matrix.trace (Kraus.evalWord (parTargets 1) w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord parA w) := by
    change Matrix.trace (Kraus.evalWord (fun i => (-1 : ℂ) • parA i) w) = _
    rw [Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h, h0, h1]; ring

/-- **Biorthogonal compression onto each of the two slots of Example PAR** (construction note,
Theorem 7.7(iv)–(v)). -/
theorem parityGraded_isReduction (s : {s // s ∈ parSlots}) :
    IsReduction parB (parTargets s.1) (parityGraded_compression.left s)
      (parityGraded_compression.right s) :=
  parityGraded_compression.isReduction s

/-- Two distinct slots of Example PAR are biorthogonal (construction note, Theorem 7.7(iv)). -/
theorem parityGraded_left_mul_right_of_ne {s t : {s // s ∈ parSlots}} (h : s ≠ t) :
    parityGraded_compression.left s * parityGraded_compression.right t = 0 :=
  parityGraded_compression.left_mul_right_of_ne h

/-- **The dimension count of Example PAR**: `5 = 2 + 2 + 1` (construction note, Theorem 7.7(vii)). -/
theorem parityGraded_dim_eq : (5 : ℕ) = ∑ s ∈ parSlots, parDim s + 1 :=
  parityGraded_compression.dim_eq

/-- **Nilpotency of the remainder of Example PAR** (construction note, Theorem 7.7(vi)): the bound
`r = |S| + z = 3` of the theorem. -/
theorem parityGraded_evalWord_remainder_eq_zero (w : List (Fin 2)) (hw : 3 ≤ w.length) :
    Kraus.evalWord parityGraded_compression.remainder w = 0 := by
  refine parityGraded_compression.evalWord_remainder_eq_zero w ?_
  change (2 : ℕ) + 1 ≤ w.length
  omega

/-! ### Sharpness: the nilpotency bound of the theorem is attained -/

/-- The compression map into the bond space from the weight `+1` slot (the note's `V_+`). -/
def parRight0Int : Matrix (Fin 5) (Fin 2) ℤ := !![1, 0; 0, 1; 1, 1; 0, 0; 1, 0]

/-- The compression map into the bond space from the weight `-1` slot (the note's `V_-`). -/
def parRight1Int : Matrix (Fin 5) (Fin 2) ℤ := !![0, 1; 1, 0; 1, 0; 1, 1; 0, 0]

/-- The compression map out of the bond space onto the weight `+1` slot (the note's `W_+`). -/
def parLeft0Int : Matrix (Fin 2) (Fin 5) ℤ := !![0, -1, 1, 0, 0; 1, 1, 0, -1, -1]

/-- The compression map out of the bond space onto the weight `-1` slot (the note's `W_-`). -/
def parLeft1Int : Matrix (Fin 2) (Fin 5) ℤ := !![-1, 0, 0, 1, 1; 1, 0, 0, 0, -1]

private theorem parRight0_eq :
    parityGraded_compression.right ⟨0, Finset.mem_univ 0⟩ = complexOfInt parRight0Int := by
  rw [MultiBlockCompression.right_gaugeOfMatrix parityGraded_compression
    (hG := parGaugeComplex_mul_inv) (hG' := parGaugeComplex_inv_mul) rfl]
  ext x j
  fin_cases j <;>
    · simp only [Matrix.submatrix_apply, id_eq, complexOfInt_apply, Int.cast_inj]
      revert x
      decide

private theorem parRight1_eq :
    parityGraded_compression.right ⟨1, Finset.mem_univ 1⟩ = complexOfInt parRight1Int := by
  rw [MultiBlockCompression.right_gaugeOfMatrix parityGraded_compression
    (hG := parGaugeComplex_mul_inv) (hG' := parGaugeComplex_inv_mul) rfl]
  ext x j
  fin_cases j <;>
    · simp only [Matrix.submatrix_apply, id_eq, complexOfInt_apply, Int.cast_inj]
      revert x
      decide

private theorem parLeft0_eq :
    parityGraded_compression.left ⟨0, Finset.mem_univ 0⟩ = complexOfInt parLeft0Int := by
  rw [MultiBlockCompression.left_gaugeOfMatrix parityGraded_compression
    (hG := parGaugeComplex_mul_inv) (hG' := parGaugeComplex_inv_mul) rfl]
  ext i y
  fin_cases i <;>
    · simp only [Matrix.submatrix_apply, id_eq, complexOfInt_apply, Int.cast_inj]
      revert y
      decide

private theorem parLeft1_eq :
    parityGraded_compression.left ⟨1, Finset.mem_univ 1⟩ = complexOfInt parLeft1Int := by
  rw [MultiBlockCompression.left_gaugeOfMatrix parityGraded_compression
    (hG := parGaugeComplex_mul_inv) (hG' := parGaugeComplex_inv_mul) rfl]
  ext i y
  fin_cases i <;>
    · simp only [Matrix.submatrix_apply, id_eq, complexOfInt_apply, Int.cast_inj]
      revert y
      decide

/-- The integer matrices of the residual `R^i = B^i - V₊ A^i W₊ - V₋ (-A^i) W₋` of Example
PAR. -/
def parRemainderInt : Fin 2 → Matrix (Fin 5) (Fin 5) ℤ
  | 0 => !![-1, 2, -2, 1, 3;
            1, 2, -2, 0, 1;
            0, 3, -3, 1, 3;
            0, 3, -3, 0, 3;
            -1, 1, -1, 1, 2]
  | 1 => !![1, 0, 0, 0, -1;
            -2, 2, -2, 2, 4;
            -1, 2, -2, 2, 3;
            0, 1, -1, 0, 1;
            1, 0, 0, 0, -1]

private theorem parSlots_univ_eq :
    (Finset.univ : Finset {s // s ∈ parSlots}) =
      {(⟨0, Finset.mem_univ 0⟩ : {s // s ∈ parSlots}), ⟨1, Finset.mem_univ 1⟩} := by
  decide

private theorem parSlots_ne :
    (⟨0, Finset.mem_univ 0⟩ : {s // s ∈ parSlots}) ≠ ⟨1, Finset.mem_univ 1⟩ := by decide

theorem parityGraded_remainder_eq (i : Fin 2) :
    parityGraded_compression.remainder i = complexOfInt (parRemainderInt i) := by
  rw [MultiBlockCompression.remainder, parSlots_univ_eq, Finset.sum_pair parSlots_ne,
    parRight0_eq, parRight1_eq, parLeft0_eq, parLeft1_eq, parTargets_eq, parTargets_eq, parB_eq]
  fin_cases i <;>
    · ext p q
      fin_cases p <;> fin_cases q <;>
        norm_num [parRight0Int, parRight1Int, parLeft0Int, parLeft1Int, parTargetsInt, parAInt,
          parBInt, parRemainderInt, complexOfInt, Matrix.map_apply, Matrix.mul_apply,
          Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_two, Fin.sum_univ_five]

/-- **Sharpness of the nilpotency bound of Example PAR**: the residual is already nonzero at
word length two, so the bound `r = |S| + z = 3` of the theorem is attained (construction note, §4). -/
theorem parityGraded_remainder_sq_ne_zero :
    Kraus.evalWord parityGraded_compression.remainder [0, 0] ≠ 0 := by
  simp only [Kraus.evalWord, mul_one]
  rw [parityGraded_remainder_eq, ← complexOfInt_mul]
  intro hzero
  have h01 : ((parRemainderInt 0 * parRemainderInt 0) 0 1 : ℤ) = 0 := by
    have h01' := congrFun (congrFun hzero 0) 1
    simp only [complexOfInt_apply, Matrix.zero_apply] at h01'
    exact_mod_cast h01'
  revert h01; decide

/-! ### Absence of sitewise intertwiners for the weight `-1` block -/

private theorem parTargets1_apply0 : parTargets 1 0 = !![(-1 : ℂ), 0; 0, 0] := by
  rw [parTargets_eq]; ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [parTargetsInt, parAInt, complexOfInt, Matrix.map_apply]

private theorem parTargets1_apply1 : parTargets 1 1 = !![(0 : ℂ), -1; -1, 0] := by
  rw [parTargets_eq]; ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [parTargetsInt, parAInt, complexOfInt, Matrix.map_apply]

private theorem parB_apply0 :
    parB 0 = !![(-1 : ℂ), 1, -1, 1, 3;
                2, 2, -2, -1, 0;
                1, 2, -2, 0, 2;
                1, 3, -3, -1, 2;
                -1, 0, 0, 1, 2] := by
  rw [parB_eq]; ext a b; fin_cases a <;> fin_cases b <;> norm_num [parBInt, complexOfInt]

private theorem parB_apply1 :
    parB 1 = !![(3 : ℂ), 1, 0, -2, -3;
                -3, 1, -1, 2, 5;
                -1, 2, -1, 1, 3;
                0, 1, -1, -1, 1;
                2, 1, 0, -1, -2] := by
  rw [parB_eq]; ext a b; fin_cases a <;> fin_cases b <;> norm_num [parBInt, complexOfInt]

/-- **No nonzero right sitewise intertwiner for the weight `-1` block of Example PAR**
(construction note, §4): the sitewise compression of the theorem is the strongest local relation
available for this block. -/
theorem parNeg_right_intertwiner_eq_zero (V : Matrix (Fin 5) (Fin 2) ℂ)
    (h : ∀ i, parB i * V = V * parTargets 1 i) : V = 0 := by
  have h0 := h 0
  have h1 := h 1
  rw [parB_apply0, parTargets1_apply0] at h0
  rw [parB_apply1, parTargets1_apply1] at h1
  have e030 := congrFun (congrFun h0 3) 0
  have e040 := congrFun (congrFun h0 4) 0
  have e021 := congrFun (congrFun h0 2) 1
  have e031 := congrFun (congrFun h0 3) 1
  have e041 := congrFun (congrFun h0 4) 1
  have e100 := congrFun (congrFun h1 0) 0
  have e110 := congrFun (congrFun h1 1) 0
  have e120 := congrFun (congrFun h1 2) 0
  have e130 := congrFun (congrFun h1 3) 0
  have e140 := congrFun (congrFun h1 4) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at *
  have hx0 : V 0 0 = 0 := by
    linear_combination (1/4 : ℂ) * e030 + (1/2 : ℂ) * e040 + (-1/2 : ℂ) * e021 +
      (-1/4 : ℂ) * e031 + (1/2 : ℂ) * e041 + (5/4 : ℂ) * e100 + (7/4 : ℂ) * e110 +
      (-7/4 : ℂ) * e120 + (-3/4 : ℂ) * e130 + (1/2 : ℂ) * e140
  have hx1 : V 1 0 = 0 := by
    linear_combination (-1/4 : ℂ) * e030 + (1 : ℂ) * e021 + (-5/4 : ℂ) * e031 +
      (-2 : ℂ) * e041 + (-7/4 : ℂ) * e100 + (7/4 : ℂ) * e110 + (-7/4 : ℂ) * e120 +
      (3/4 : ℂ) * e130 + (9/2 : ℂ) * e140
  have hx2 : V 2 0 = 0 := by
    linear_combination (-1/2 : ℂ) * e030 + (1/2 : ℂ) * e040 + (1/2 : ℂ) * e021 +
      (-1 : ℂ) * e031 + (-3/2 : ℂ) * e041 + (-1 : ℂ) * e100 + (2 : ℂ) * e110 +
      (-2 : ℂ) * e120 + (1/2 : ℂ) * e130 + (4 : ℂ) * e140
  have hx3 : V 3 0 = 0 := by
    linear_combination (1/4 : ℂ) * e030 + (1 : ℂ) * e021 + (-7/4 : ℂ) * e031 +
      (-1 : ℂ) * e041 + (-1/4 : ℂ) * e100 + (13/4 : ℂ) * e110 + (-13/4 : ℂ) * e120 +
      (-3/4 : ℂ) * e130 + (7/2 : ℂ) * e140
  have hx4 : V 4 0 = 0 := by
    linear_combination (1/2 : ℂ) * e040 + (-1/2 : ℂ) * e021 + (1/2 : ℂ) * e031 +
      (1/2 : ℂ) * e041 + (1/2 : ℂ) * e100 + (-1/2 : ℂ) * e110 + (1/2 : ℂ) * e120 +
      (-1 : ℂ) * e140
  have hy0 : V 0 1 = 0 := by
    linear_combination e100 - 3 * hx0 - hx1 + 2 * hx3 + 3 * hx4
  have hy1 : V 1 1 = 0 := by
    linear_combination e110 + 3 * hx0 - hx1 + hx2 - 2 * hx3 - 5 * hx4
  have hy2 : V 2 1 = 0 := by
    linear_combination e120 + hx0 - 2 * hx1 + hx2 - hx3 - 3 * hx4
  have hy3 : V 3 1 = 0 := by
    linear_combination e130 - hx1 + hx2 + hx3 - hx4
  have hy4 : V 4 1 = 0 := by
    linear_combination e140 - 2 * hx0 - hx1 + hx3 + 2 * hx4
  ext r c
  fin_cases r <;> fin_cases c
  exacts [hx0, hy0, hx1, hy1, hx2, hy2, hx3, hy3, hx4, hy4]

/-- **No nonzero left sitewise intertwiner for the weight `-1` block of Example PAR**
(construction note, §4). -/
theorem parNeg_left_intertwiner_eq_zero (W : Matrix (Fin 2) (Fin 5) ℂ)
    (h : ∀ i, W * parB i = parTargets 1 i * W) : W = 0 := by
  have h0 := h 0
  have h1 := h 1
  rw [parB_apply0, parTargets1_apply0] at h0
  rw [parB_apply1, parTargets1_apply1] at h1
  have f004 := congrFun (congrFun h0 0) 4
  have f010 := congrFun (congrFun h0 1) 0
  have f012 := congrFun (congrFun h0 1) 2
  have f013 := congrFun (congrFun h0 1) 3
  have f014 := congrFun (congrFun h0 1) 4
  have f100 := congrFun (congrFun h1 0) 0
  have f110 := congrFun (congrFun h1 0) 1
  have f120 := congrFun (congrFun h1 0) 2
  have f130 := congrFun (congrFun h1 0) 3
  have f140 := congrFun (congrFun h1 0) 4
  simp only [Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at *
  have hu0 : W 0 0 = 0 := by
    linear_combination f010 + f012 + (-2 : ℂ) * f013 + 4 * f100 + (-2 : ℂ) * f110 + f120 +
      3 * f140
  have hu1 : W 0 1 = 0 := by
    linear_combination f004 + 6 * f010 + 3 * f012 + f013 + f014 + 5 * f100 + (-5 : ℂ) * f110 +
      (-2 : ℂ) * f120 + 2 * f130 + 3 * f140
  have hu2 : W 0 2 = 0 := by
    linear_combination (-1 : ℂ) * f004 + (-7 : ℂ) * f010 + (-4 : ℂ) * f012 +
      (-1 : ℂ) * f013 + (-2 : ℂ) * f014 + (-4 : ℂ) * f100 + 5 * f110 + 3 * f120 +
      (-2 : ℂ) * f130 + (-2 : ℂ) * f140
  have hu3 : W 0 3 = 0 := by
    linear_combination (-2 : ℂ) * f010 + (-2 : ℂ) * f012 + f013 + (-1 : ℂ) * f014 +
      (-2 : ℂ) * f100 + f110 + (-1 : ℂ) * f130 + (-1 : ℂ) * f140
  have hu4 : W 0 4 = 0 := by
    linear_combination f004 + 5 * f010 + 3 * f012 + 2 * f013 + 2 * f014 + (-2 : ℂ) * f110 +
      (-3 : ℂ) * f120 + 2 * f130 + (-1 : ℂ) * f140
  have hv0 : W 1 0 = 0 := by
    linear_combination f100 - 3 * hu0 + 3 * hu1 + hu2 - 2 * hu4
  have hv1 : W 1 1 = 0 := by
    linear_combination f110 - hu0 - hu1 - 2 * hu2 - hu3 - hu4
  have hv2 : W 1 2 = 0 := by
    linear_combination f120 + hu1 + hu2 + hu3
  have hv3 : W 1 3 = 0 := by
    linear_combination f130 + 2 * hu0 - 2 * hu1 - hu2 + hu3 + hu4
  have hv4 : W 1 4 = 0 := by
    linear_combination f140 + 3 * hu0 - 5 * hu1 - 3 * hu2 - hu3 + 2 * hu4
  ext r c
  fin_cases r <;> fin_cases c
  exacts [hu0, hu1, hu2, hu3, hu4, hv0, hv1, hv2, hv3, hv4]

end ParityGraded
