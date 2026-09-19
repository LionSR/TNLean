/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.StackedPairGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# The graded quantum-dimer twist at `x = 7/8`

A machine-checked instance of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) for
the two-sector graded quantum-dimer twist of the P6 work
(`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex`, the resolution
`thm:p6-round44-z2`; strategy note
`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`; exact data in
`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §1, verified by
`checks/round44_p6_z2_twisted_dimer.py` at the rational point `x = 7/8`, `y = 1/8`).

A horizontal bond index is a triple `(p, p', k)` of bits: the ket and bra of the left half-bond
and a sector label. The vertical site space is `ℂ² ⊗ ℂ²`, and every letter of the sector-`f`
tensor is a scaled matrix unit, the scale being `(1/2) C_k[p][p'] τ_k[f]` with
`C_0 = x P₊ + y P₋`, `C_1 = x P₊ - y P₋`, `τ_0 = (1, 1)` and `τ_1 = (1, -1)`. Letters whose two
bond indices carry different sector labels vanish.

Fusing two sectors produces *two* weighted sectors: the stacked product of the tensors of `f`
and `f'` compresses onto the tensor of `f + f'` with the weight `x/2 = 7/16` and onto the tensor
of `f + f' + 1` with the weight `y/2 = 1/16`, with eight zero slots left over. The weights are
the occupations of the two fusion channels, and the periodic coefficient
`c^{(L)} = (7/16)^L + (1/16)^L` is their length-`L` power sum. Both targets are normal at
blocking length one and are not gauge equivalent (their one-letter traces differ), so the length
dependence here comes from two genuinely different sectors rather than from a repeated one.

This file sets up the sector tensors, the compression datum of a fusion whose stacked letters
satisfy the integer letter identity, the pair-generic reduction of that identity to two
exhaustive checks over the sixty-four letters, and the two checks for the fusion of the zero
sector with itself. The remaining three pairs of sectors satisfy the same identity with the same
gauge and the same weights; their exhaustive checks live in the modules
`TwistedDimerPairZeroOne`, `TwistedDimerPairOneZero` and `TwistedDimerPairOneOne`, and
`TwistedDimerPairs` assembles the four cases into the fusion rule for every pair of sectors,
with its compression datum, its consequences and its word-trace identity.

## Main definitions

* `P6Compression.dimerM`: the sector-`f` tensor as a matrix product operator tensor.
* `P6Compression.dimerTarget`: its view on the sixty-four-letter pair alphabet.
* `P6Compression.dimerStacked`: the stacked product of two sectors, of bond dimension sixteen.

## Main results

* `P6Compression.dimerCompressionOfLetterIdentity`: the compression datum of Theorem 7.7 for
  the fusion of any two sectors whose stacked letters satisfy the integer letter identity, and
  `P6Compression.dimer_trace_evalWord_of_compression`, the word-trace identity it implies.
* `P6Compression.dimer_letter_int_of_halves`: the letter identity of a pair of sectors follows
  from its restrictions to the two sector labels, the two exhaustive checks.
* `P6Compression.dimer_letter_int`: the integer letter identity of the fusion of the zero sector
  with itself, its two exhaustive checks carried out.
* `P6Compression.dimerTarget_isNormal`: each sector is normal at blocking length one.
* `P6Compression.dimerTarget_not_gaugeEquiv`, `P6Compression.dimerBlocks_not_gaugeEquiv`: the two
  sectors, hence the two targets of every fusion, are not gauge equivalent.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor

/-! ### The sector tensors -/

/-- The ket bit `p` of the horizontal bond index `a = 4 p + 2 p' + k`
(`p6_examples_compression_data.md`, §1.1). -/
def dimerKet (a : Fin 8) : Fin 2 := ⟨a.val / 4, by omega⟩

/-- The bra bit `p'` of the horizontal bond index `a = 4 p + 2 p' + k`. -/
def dimerBra (a : Fin 8) : Fin 2 := ⟨a.val / 2 % 2, by omega⟩

/-- The sector label `k` of the horizontal bond index `a = 4 p + 2 p' + k`. -/
def dimerFlag (a : Fin 8) : Fin 2 := ⟨a.val % 2, by omega⟩

/-- The row `(p, q)` of the vertical site space `ℂ² ⊗ ℂ²` carried by a letter. -/
def dimerRow (a b : Fin 8) : Fin 4 := ⟨2 * (dimerKet a).val + (dimerKet b).val, by omega⟩

/-- The column `(p', q')` of the vertical site space `ℂ² ⊗ ℂ²` carried by a letter. -/
def dimerCol (a b : Fin 8) : Fin 4 := ⟨2 * (dimerBra a).val + (dimerBra b).val, by omega⟩

/-- Sixteen times the scale `(1/2) C_k[p][p'] τ_k[f]` of a letter of the sector-`f` tensor at
`x = 7/8`, `y = 1/8` (`p6_examples_compression_data.md`, §1.1). -/
def dimerScalarInt (f : Fin 2) (a : Fin 8) : ℤ :=
  (if dimerFlag a = 0 then (if dimerKet a = dimerBra a then 4 else 3)
    else if dimerKet a = dimerBra a then 3 else 4) *
  (if dimerFlag a = 1 ∧ f = 1 then -1 else 1)

/-- Sixteen times the sector-`f` tensor: a scaled matrix unit at each letter, vanishing when the
two bond indices carry different sector labels. -/
def dimerMInt (f : Fin 2) (a b : Fin 8) : Matrix (Fin 4) (Fin 4) ℤ :=
  if dimerFlag a = dimerFlag b then
    dimerScalarInt f a • Matrix.single (dimerRow a b) (dimerCol a b) 1
  else 0

/-- The sector-`f` tensor as a matrix product operator tensor. -/
noncomputable def dimerM (f : Fin 2) : MPOTensor 8 4 :=
  fun a b => (16 : ℂ)⁻¹ • complexOfInt (dimerMInt f a b)

/-- The sector-`f` tensor on the sixty-four-letter pair alphabet. -/
noncomputable def dimerTarget (f : Fin 2) : MPSTensor 64 4 := (dimerM f).toMPSTensor

/-- The stacked product of the sector-`f` and sector-`f'` tensors, of bond dimension sixteen
(`p6_examples_compression_data.md`, §1.2). -/
noncomputable def dimerStacked (f f' : Fin 2) : MPSTensor 64 16 :=
  (MPOTensor.mulTensor (dimerM f) (dimerM f')).toMPSTensor

/-- Sixteen times the pair-alphabet sector-`f` tensor. -/
def dimerTargetInt (f : Fin 2) (a : Fin 64) : Matrix (Fin 4) (Fin 4) ℤ :=
  dimerMInt f (Fin.divNat (m := 8) (n := 8) a) (Fin.modNat (m := 8) (n := 8) a)

/-- Two hundred and fifty-six times the stacked product. -/
def dimerStackedInt (f f' : Fin 2) (a : Fin 64) : Matrix (Fin 16) (Fin 16) ℤ :=
  mulIntTensor (dimerMInt f) (dimerMInt f') (Fin.divNat (m := 8) (n := 8) a)
    (Fin.modNat (m := 8) (n := 8) a)

theorem dimerTarget_eq (f : Fin 2) (a : Fin 64) :
    dimerTarget f a = (16 : ℂ)⁻¹ • complexOfInt (dimerTargetInt f a) := rfl

theorem dimerStacked_eq (f f' : Fin 2) (a : Fin 64) :
    dimerStacked f f' a = ((16 : ℂ)⁻¹ * (16 : ℂ)⁻¹) • complexOfInt (dimerStackedInt f f' a) :=
  mulTensor_smul_complexOfInt (16 : ℂ)⁻¹ (dimerMInt f) (dimerMInt f') _ _

/-! ### The two fusion channels -/

/-- The two target blocks of the fusion of the sectors `f` and `f'`: the sectors `f + f'` and
`f + f' + 1` (`p6_examples_compression_data.md`, §1.2). -/
noncomputable def dimerBlocks (f f' : Fin 2) : Fin 2 → MPSTensor 64 4 :=
  fun s => dimerTarget (f + f' + s)

/-- Sixteen times the two target blocks. -/
def dimerBlockInt (f f' : Fin 2) : Fin 2 → Fin 64 → Matrix (Fin 4) (Fin 4) ℤ :=
  fun s => dimerTargetInt (f + f' + s)

/-- The two weights of the fusion, the channel occupations `x/2 = 7/16` and `y/2 = 1/16`
(`p6_examples_compression_data.md`, §1.2). -/
noncomputable def dimerWeights : Fin 2 → ℂ := ![7 / 16, 1 / 16]

/-- Sixteen times the two weights, the integer coefficients of the letter identity. -/
def dimerCoefInt : Fin 2 → ℤ := ![7, 1]

/-! ### The letter identity

The integer letter identity `2 B^a = 7 (Π₀ ⊗ M_{f+f'}^a) + 1 (Π₁ ⊗ M_{f+f'+1}^a)` is reduced
here, for an arbitrary pair of sectors, to two exhaustive checks: one over the letters whose two
bond indices carry the sector label zero and one over those carrying the sector label one. Letters
whose two bond indices carry different sector labels vanish on both sides. -/

private theorem dimerMInt_eq_zero (f : Fin 2) {a b : Fin 8} (h : dimerFlag a ≠ dimerFlag b) :
    dimerMInt f a b = 0 := by
  simp [dimerMInt, h]

private theorem dimerStackedInt_eq_zero (f f' : Fin 2) {i k : Fin 8}
    (h : dimerFlag i ≠ dimerFlag k) : mulIntTensor (dimerMInt f) (dimerMInt f') i k = 0 := by
  have hj : ∀ j : Fin 8, dimerMInt f i j ⊗ₖ dimerMInt f' j k = 0 := by
    intro j
    rcases eq_or_ne (dimerFlag i) (dimerFlag j) with hij | hij
    · rw [dimerMInt_eq_zero f' fun hjk => h (hij.trans hjk), Matrix.kronecker_zero]
    · rw [dimerMInt_eq_zero f hij, Matrix.zero_kronecker]
  simp [mulIntTensor, hj]

/-- The letter identity at a letter whose two bond indices carry different sector labels: both
sides vanish. -/
private theorem dimer_letter_int_of_flag_ne (f f' : Fin 2) (a : Fin 64)
    (h : dimerFlag (Fin.divNat (m := 8) (n := 8) a) ≠
      dimerFlag (Fin.modNat (m := 8) (n := 8) a)) :
    (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a := by
  rw [dimerStackedInt, dimerStackedInt_eq_zero f f' h, smul_zero]
  refine (Finset.sum_eq_zero fun s _ => ?_).symm
  rw [pairBlockInt, dimerBlockInt, dimerTargetInt, dimerMInt_eq_zero _ h]
  simp

/-- The stacked product restricted to the four intermediate bond indices of sector label zero;
the other four summands vanish when the outer bond indices carry the sector label zero. -/
def dimerStackEven (f f' : Fin 2) (i k : Fin 8) : Matrix (Fin 16) (Fin 16) ℤ :=
  (dimerMInt f i 0 ⊗ₖ dimerMInt f' 0 k + dimerMInt f i 2 ⊗ₖ dimerMInt f' 2 k
      + dimerMInt f i 4 ⊗ₖ dimerMInt f' 4 k + dimerMInt f i 6 ⊗ₖ dimerMInt f' 6 k).submatrix
    (finProdFinEquiv (m := 4) (n := 4)).symm (finProdFinEquiv (m := 4) (n := 4)).symm

/-- The stacked product restricted to the four intermediate bond indices of sector label one;
the other four summands vanish when the outer bond indices carry the sector label one. -/
def dimerStackOdd (f f' : Fin 2) (i k : Fin 8) : Matrix (Fin 16) (Fin 16) ℤ :=
  (dimerMInt f i 1 ⊗ₖ dimerMInt f' 1 k + dimerMInt f i 3 ⊗ₖ dimerMInt f' 3 k
      + dimerMInt f i 5 ⊗ₖ dimerMInt f' 5 k + dimerMInt f i 7 ⊗ₖ dimerMInt f' 7 k).submatrix
    (finProdFinEquiv (m := 4) (n := 4)).symm (finProdFinEquiv (m := 4) (n := 4)).symm

/-- On a left bond index of sector label zero the stacked product is its even restriction. -/
private theorem dimerStackedInt_even (f f' : Fin 2) {i : Fin 8} (hi : dimerFlag i = 0)
    (k : Fin 8) : mulIntTensor (dimerMInt f) (dimerMInt f') i k = dimerStackEven f f' i k := by
  have hz : ∀ j : Fin 8, dimerFlag j = 1 → dimerMInt f i j ⊗ₖ dimerMInt f' j k = 0 := by
    intro j hj
    rw [dimerMInt_eq_zero f (by rw [hi, hj]; decide), Matrix.zero_kronecker]
  rw [mulIntTensor, Fin.sum_univ_eight, hz 1 (by decide), hz 3 (by decide), hz 5 (by decide),
    hz 7 (by decide)]
  simp only [add_zero, dimerStackEven]

/-- On a left bond index of sector label one the stacked product is its odd restriction. -/
private theorem dimerStackedInt_odd (f f' : Fin 2) {i : Fin 8} (hi : dimerFlag i = 1)
    (k : Fin 8) : mulIntTensor (dimerMInt f) (dimerMInt f') i k = dimerStackOdd f f' i k := by
  have hz : ∀ j : Fin 8, dimerFlag j = 0 → dimerMInt f i j ⊗ₖ dimerMInt f' j k = 0 := by
    intro j hj
    rw [dimerMInt_eq_zero f (by rw [hi, hj]; decide), Matrix.zero_kronecker]
  rw [mulIntTensor, Fin.sum_univ_eight, hz 0 (by decide), hz 2 (by decide), hz 4 (by decide),
    hz 6 (by decide)]
  simp only [zero_add, add_zero, dimerStackOdd]

/-- **The letter identity from its two halves.** The integer letter identity of the fusion of
the sectors `f` and `f'` follows from its restrictions to the letters of sector label zero and
of sector label one, the two exhaustive checks carried out per pair of sectors
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimer_letter_int_of_halves (f f' : Fin 2)
    (heven : ∀ a : Fin 64,
      dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 0 →
        dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 0 →
          (2 : ℤ) • dimerStackEven f f' (Fin.divNat (m := 8) (n := 8) a)
              (Fin.modNat (m := 8) (n := 8) a) =
            ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a)
    (hodd : ∀ a : Fin 64,
      dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 1 →
        dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 1 →
          (2 : ℤ) • dimerStackOdd f f' (Fin.divNat (m := 8) (n := 8) a)
              (Fin.modNat (m := 8) (n := 8) a) =
            ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a)
    (a : Fin 64) :
    (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a := by
  have htwo : ∀ u : Fin 2, u = 0 ∨ u = 1 := by decide
  rcases eq_or_ne (dimerFlag (Fin.divNat (m := 8) (n := 8) a))
    (dimerFlag (Fin.modNat (m := 8) (n := 8) a)) with h | h
  · rcases htwo (dimerFlag (Fin.divNat (m := 8) (n := 8) a)) with hi | hi
    · rw [dimerStackedInt, dimerStackedInt_even f f' hi]
      exact heven a hi (h.symm.trans hi)
    · rw [dimerStackedInt, dimerStackedInt_odd f f' hi]
      exact hodd a hi (h.symm.trans hi)
  · exact dimer_letter_int_of_flag_ne f f' a h

private theorem dimer_scalar (s : Fin 2) :
    (((2 : ℤ) : ℂ)) * (dimerWeights s * ((2 : ℂ)⁻¹ * (16 : ℂ)⁻¹)) =
      ((dimerCoefInt s : ℤ) : ℂ) * ((16 : ℂ)⁻¹ * (16 : ℂ)⁻¹) := by
  fin_cases s <;> norm_num [dimerWeights, dimerCoefInt]

/-- **The projector-weighted decomposition of a stacked pair of sectors** from the integer letter
identity (`p6_examples_compression_data.md`, §1.3). -/
private theorem dimer_hB_of_letter_int (f f' : Fin 2)
    (hint : ∀ a, (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a) (a : Fin 64) :
    dimerStacked f f' a = (∑ s ∈ pairSlots, dimerWeights s •
      (basisProj pairU pairUinv (pairJ s) ⊗ₖ dimerBlocks f f' s a)).submatrix
        pairReorder.symm pairReorder.symm :=
  stackedPair_letter_identity (by norm_num) (dimerStacked_eq f f')
    (fun s a => dimerTarget_eq (f + f' + s) a) dimer_scalar hint a

/-! ### The compression datum of a pair of sectors -/

/-- **The multi-block asymmetric compression datum of a fusion of two sectors** (P5 note,
Theorem 7.7(i)–(iii)), from the integer letter identity of the pair: the two normal sectors
`f + f'` and `f + f' + 1` (not gauge equivalent by `dimerBlocks_not_gaugeEquiv`) with the weights
`7/16` and `1/16`, and eight zero slots (`p6_examples_compression_data.md`, §1.2–1.3). -/
noncomputable def dimerCompressionOfLetterIdentity (f f' : Fin 2)
    (hint : ∀ a, (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a) :
    MultiBlockCompression (D := fun _ : Fin 2 => 4) (dimerStacked f f') pairSlots
      fun s => dimerWeights s • dimerBlocks f f' s :=
  MultiBlockCompression.ofProjectorSum (zz := 2) pairU_mul_pairUinv pairUinv_mul_pairU
    pairRho pairReorder pairRho_inl (dimer_hB_of_letter_int f f' hint)

/-- **The remainder of a dimer compression vanishes** (P5 note, Theorem 7.7(vi)): the conjugated
tensor is block diagonal, so the extension splits. -/
theorem remainder_dimerCompressionOfLetterIdentity (f f' : Fin 2)
    (hint : ∀ a, (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a) :
    (dimerCompressionOfLetterIdentity f f' hint).remainder = 0 :=
  MultiBlockCompression.remainder_ofProjectorSum (zz := 2) pairU_mul_pairUinv pairUinv_mul_pairU
    pairRho pairReorder pairRho_inl (dimer_hB_of_letter_int f f' hint)

/-- **The word-trace identity of a compressed pair of sectors**: any compression of the stacked
product of the sectors `f` and `f'` onto the weighted sectors `f + f'` and `f + f' + 1` gives
`tr(B^w) = (7/16)^{|w|} tr(M_{f+f'}^w) + (1/16)^{|w|} tr(M_{f+f'+1}^w)`, the periodic coefficient
`c^{(L)} = (7/16)^L + (1/16)^L` (`p6_examples_compression_data.md`, §1.4). This is the fusion
rule `M_f M_{f'} = (x/2) M_{f+f'} ⊕ (y/2) M_{f+f'+1} ⊕ 0` of the strategy note
(`p6_round44_graded_dimer_twist.tex`, `thm:p6-r44-z2`(v), `eq:p6-r44-z2-fusion`) read on word
traces; the P6 resolution (`p6_rfp_structure_constant_l_dependence.tex`, `thm:p6-round44-z2`)
states it in the normalized form with the coefficients `α^L`, `β^L`. -/
theorem dimer_trace_evalWord_of_compression (f f' : Fin 2)
    (P : MultiBlockCompression (D := fun _ : Fin 2 => 4) (dimerStacked f f') pairSlots
      fun s => dimerWeights s • dimerBlocks f f' s)
    (w : List (Fin 64)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord (dimerStacked f f') w) =
      (7 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget (f + f')) w) +
        (1 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget (f + f' + 1)) w) := by
  have h := P.trace_evalWord_eq_sum w hw
  have hs : ∀ s : Fin 2,
      Matrix.trace (Kraus.evalWord (dimerWeights s • dimerBlocks f f' s) w) =
        dimerWeights s ^ w.length * Matrix.trace (Kraus.evalWord (dimerBlocks f f' s) w) := by
    intro s
    rw [show dimerWeights s • dimerBlocks f f' s =
        fun i => dimerWeights s • dimerBlocks f f' s i from rfl,
      Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h, show pairSlots = Finset.univ from rfl, Fin.sum_univ_two, hs 0, hs 1]
  simp only [dimerWeights, dimerBlocks, add_zero]
  rfl

/-! ### The letter identity of the fusion of the zero sector with itself -/

private theorem dimer_letter_int_even : ∀ a : Fin 64,
    dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 0 →
      dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 0 →
        (2 : ℤ) • dimerStackEven 0 0 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 0) s a := by
  decide +kernel

private theorem dimer_letter_int_odd : ∀ a : Fin 64,
    dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 1 →
      dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 1 →
        (2 : ℤ) • dimerStackOdd 0 0 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 0) s a := by
  decide +kernel

/-- **The integer letter identity of the fusion of the zero sector with itself**
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimer_letter_int (a : Fin 64) :
    (2 : ℤ) • dimerStackedInt 0 0 a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 0) s a :=
  dimer_letter_int_of_halves 0 0 dimer_letter_int_even dimer_letter_int_odd a

/-! ### Normality and inequivalence of the sectors -/

/-- The letter realising each matrix unit of the bond algebra of a sector. -/
def dimerUnitLetter : Fin 4 → Fin 4 → Fin 64 :=
  ![![0, 2, 16, 18], ![4, 6, 20, 22], ![32, 34, 48, 50], ![36, 38, 52, 54]]

/-- The nonzero integer factor relating that letter to its matrix unit; the letters chosen all
lie in the sector label zero, where the scale does not depend on `f`. -/
def dimerUnitCoef : Fin 4 → Fin 4 → ℤ :=
  ![![4, 4, 3, 3], ![4, 4, 3, 3], ![3, 3, 4, 4], ![3, 3, 4, 4]]

private theorem dimerTargetInt_unit (f : Fin 2) (x y : Fin 4) :
    dimerTargetInt f (dimerUnitLetter x y) = dimerUnitCoef x y • Matrix.single x y 1 := by
  revert f x y
  decide +kernel

/-- **Each sector is normal at blocking length one**: its thirty-two nonzero letters are scaled
matrix units covering every position, so they span the four-by-four matrix algebra
(`p6_examples_compression_data.md`, §1.4). -/
theorem dimerTarget_isNormal (f : Fin 2) : Kraus.IsNormal (dimerTarget f) :=
  isNormal_of_single_eq_smul (dimerTargetInt f) (by norm_num) (dimerTarget_eq f)
    dimerUnitLetter dimerUnitCoef (by decide) (dimerTargetInt_unit f)

private theorem trace_complexOfInt {n : Type*} [Fintype n] (X : Matrix n n ℤ) :
    (complexOfInt X).trace = (X.trace : ℂ) := by
  simp [Matrix.trace, complexOfInt]

/-- The one-letter traces of the two sectors differ at the letter `9 = (1, 1)`, whose two bond
indices carry the sector label one: the sign twist `τ_1` flips the trace. -/
private theorem dimerTargetInt_trace_nine (f : Fin 2) :
    (dimerTargetInt f 9).trace ≠ (dimerTargetInt (f + 1) 9).trace := by
  revert f
  decide +kernel

/-- **The two sectors are not gauge equivalent**: no invertible gauge conjugates the sector `f`
into the sector `f + 1`, since a gauge preserves one-letter traces and the sign twist `τ_1[f]`
flips the trace of the letter `9` (`p6_examples_compression_data.md`, §1.2 and Notes for Lean). -/
theorem dimerTarget_not_gaugeEquiv (f : Fin 2) :
    ¬ GaugeEquiv (dimerTarget f) (dimerTarget (f + 1)) := by
  rintro ⟨X, hX⟩
  have h := congrArg Matrix.trace (hX 9)
  rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, dimerTarget_eq, dimerTarget_eq,
    Matrix.trace_smul, Matrix.trace_smul, trace_complexOfInt, trace_complexOfInt] at h
  exact dimerTargetInt_trace_nine f
    (by exact_mod_cast (smul_right_injective ℂ (by norm_num) h).symm)

/-- **The two targets of every fusion are not gauge equivalent**: the sectors `f + f'` and
`f + f' + 1` are the two distinct sectors, in some order. -/
theorem dimerBlocks_not_gaugeEquiv (f f' : Fin 2) :
    ¬ GaugeEquiv (dimerBlocks f f' 0) (dimerBlocks f f' 1) := by
  simpa [dimerBlocks] using dimerTarget_not_gaugeEquiv (f + f')

end P6Compression
