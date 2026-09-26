/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Basis
import TNLean.MPS.Core.NormalityFromTwoWords
import TNLean.MPS.FundamentalTheorem.Reduction.AssemblyLemmas
import TNLean.MPS.FundamentalTheorem.Reduction.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# A concrete parity-weighted tensor example

**Source.** None: this is a construction of this development, not a model from a paper. No
Kitaev Hamiltonian, canonical anticommutation relations, or fermion-parity boundary condition is
defined here.

**Formalized here.** The bond-two tensor `A^0 = [[1,0],[0,0]]`, `A^1 = [[0,1],[1,0]]` is normal
at word length two. Its copies with weights `+1` and `-1` have total periodic coefficient
`tr(A^w) + tr((-A)^w) = (1 + (-1)^L) tr(A^w)` for a word of length `L > 0`. This factor selects
even chain lengths: it is `2` for even `L` and `0` for odd `L`. It is not a proof of a physical
occupation-parity projection.

The five-dimensional source `parB` is given directly as two integer matrices, not as a stacked
MPO product. A change of bond coordinates puts its diagonal blocks in the form `A, -A, 0`. The
residual has zero products at length three but a nonzero product at length two. The weight-`-1`
target has no nonzero sitewise intertwiner in either direction, despite the word-level
compression.

## Main definitions

* `ParityGraded.parA`: the bond-two normal tensor.
* `ParityGraded.parB`: the five-dimensional mixed-basis source.
* `ParityGraded.parityGraded_compression`: the multi-block compression datum.

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

## Provenance

The explicit construction was first recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §4, lines 474–567, and the compression
datum instantiates Theorem 7.7 (`thm:p5-asymmetric-compression`) of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, lines 495–569 (the
"construction note" of the declaration docstrings); these are verification records, not a
source.
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

/-- Each matrix unit of `M₂` is the length-two word `A^i A^j`, corrected by `-A^0 A^0` for
`E_{11}`. -/
private theorem parAInt_single : ∀ i j : Fin 2, Matrix.single i j (1 : ℤ) =
    parAInt i * parAInt j + (if i = 1 ∧ j = 1 then -1 else 0 : ℤ) • (parAInt 0 * parAInt 0) := by
  decide

/-- **`parA` is normal at word length two** (construction note, §4): its length-two words span the full
two-by-two matrix algebra. -/
theorem parA_isNormal : Kraus.IsNormal parA :=
  isNormal_of_single_eq_two_words parA fun i j =>
    ⟨i, j, 0, 0, 1, Int.castRingHom ℂ (if i = 1 ∧ j = 1 then -1 else 0), by
      rw [one_smul, ← complexOfRing_single (Int.castRingHom ℂ), parAInt_single, complexOfRing_add,
        complexOfRing_smul, complexOfRing_mul, complexOfRing_mul]
      rfl⟩

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
    complexOfInt parGaugeInt * complexOfInt parGaugeInvInt = 1 :=
  complexOfRing_mul_eq_one _ parGauge_mul_inv

theorem parGaugeComplex_inv_mul :
    complexOfInt parGaugeInvInt * complexOfInt parGaugeInt = 1 :=
  complexOfRing_mul_eq_one _ parGaugeInv_mul

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

/-- **No nonzero right sitewise intertwiner for the weight `-1` block of Example PAR**
(construction note, §4): the sitewise compression of the theorem is the strongest local relation
available for this block. -/
theorem parNeg_right_intertwiner_eq_zero (V : Matrix (Fin 5) (Fin 2) ℂ)
    (h : ∀ i, parB i * V = V * parTargets 1 i) : V = 0 :=
  right_intertwiner_eq_zero_of_ringCertificate (Int.castRingHom ℂ) parBInt parB_eq
    (parTargetsInt 1) (parTargets_eq 1)
    ![(0, 0, 1), (0, 1, 1), (0, 3, 1), (0, 4, 0), (0, 4, 1), (1, 0, 1), (1, 1, 1), (1, 3, 0),
      (1, 4, 0), (1, 4, 1)]
    (Matrix.of fun x => ![![![9, -1, -2, 1, -9, 1, -1, 0, 1, -1], ![-4, 2, 0, 0, 6, 0, 0, 0, 0, 0]],
      ![![-6, 2, 0, 0, 4, 0, 2, 0, 0, 0], ![1, -1, 0, -1, -1, 1, 1, 0, -1, 1]],
      ![![5, 1, -2, 1, -7, -5, -1, -2, 3, 5], ![-7, -1, 2, -1, 9, 1, 1, 0, -1, 1]],
      ![![0, 2, -2, 0, 0, 4, 2, 0, -2, -4], ![8, 2, -4, 0, -8, 0, 0, 0, 0, 0]],
      ![![3, -1, 0, 1, -3, -1, -1, 0, 1, 1], ![-6, 0, 2, 0, 8, 0, 0, 0, 0, 0]]] x.1 x.2)
    (c := 2) (by norm_num) (by decide) V h

/-- **No nonzero left sitewise intertwiner for the weight `-1` block of Example PAR**
(construction note, §4). -/
theorem parNeg_left_intertwiner_eq_zero (W : Matrix (Fin 2) (Fin 5) ℂ)
    (h : ∀ i, W * parB i = parTargets 1 i * W) : W = 0 :=
  left_intertwiner_eq_zero_of_ringCertificate (Int.castRingHom ℂ) parBInt parB_eq
    (parTargetsInt 1) (parTargets_eq 1)
    ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (0, 2, 0), (1, 0, 0), (1, 0, 1), (1, 2, 0), (1, 3, 0),
      (1, 3, 1), (1, 4, 0)]
    (Matrix.of fun x => ![![![3, -3, -1, -3, 3, -6, 4, -5, -8, 4],
        ![-3, 2, 1, 2, -2, 10, -6, 11, 14, -6]],
      ![![3, -7, -2, -8, 6, -6, 5, -1, -7, 5], ![2, -5, -1, -5, 4, -3, 2, 0, -3, 3]],
      ![![-3, 8, 2, 9, -6, 6, -5, 1, 7, -5], ![-2, 4, 1, 4, -3, 4, -2, 2, 5, -3]],
      ![![-2, 3, 1, 3, -3, 4, -3, 2, 5, -3], ![1, 0, 0, 0, 0, -4, 2, -5, -6, 2]],
      ![![0, -3, -1, -4, 3, -2, 2, 1, -2, 2], ![5, -7, -2, -7, 6, -14, 9, -13, -19, 10]]] x.1 x.2)
    (c := 1) (by norm_num) (by decide) W h

end ParityGraded
