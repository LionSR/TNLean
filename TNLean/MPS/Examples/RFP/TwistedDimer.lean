/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.GeneralizeDecide
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Examples.MultiBlock.StackedPairGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.MPDO.TwistedDimerVerticalCF

/-!
# The graded quantum-dimer twist at `x = 7/8`

A machine-checked instance of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) for
the two-sector graded quantum-dimer twist at the rational point `x = 7/8`, `y = 1/8`.

**Source.** Project construction; the sector tensors are not printed in Cirac,
Pérez-García, Schuch, Verstraete 2017 (arXiv:1606.00608). The construction
addresses the open question at `Papers/1606.00608/MPDO-22-12-17-2.tex` line 995:
whether there are renormalization fixed points whose structure coefficients
$c^{(L)}_{\alpha,\beta,\gamma}=\operatorname{tr}(\chi^L_{\alpha,\beta,\gamma})$ in the
algebra relation of Theorem 4.14 (lines 972--993) depend on $L$. The word-trace
identity of the fusion (`P6Compression.dimerFusion_trace_evalWord` in
`TwistedDimerPairs`) carries the length-dependent weights $(7/16)^{|w|}$ and
$(1/16)^{|w|}$. These are the fusion weights of the sector tensors as normalized
here, not the coefficients $c^{(L)}$ of Theorem 4.14: the sector tensors are not
put in the canonical form of that theorem. The coefficients of the same-length
product law of Theorem 4.14(ii) for the flag-sector operators, $\alpha^L$ and
$\beta^L$ with $\alpha=7/10$ and $\beta=1/10$, are proved in
`TNLean.MPS.MPDO.TwistedDimerProductLaw`, which does not assert that the two
sectors form the canonical basis of normal tensors. These
modules prove the compression and its word-trace identity only; the fixed-point
property of the twisted dimer is proved separately for the operator of
`TNLean.MPS.MPDO.TwistedDimer`
(`MPOTensor.TwistedDimer.isRFPViaTS_T`), and no formal identification of that
operator's tensor with the sector tensors here is asserted.

A horizontal bond index is a triple `(p, p', k)` of bits: the ket and bra of the left half-bond
and a sector label. The vertical site space is `ℂ² ⊗ ℂ²`, and every letter of the sector-`f`
tensor is a scaled matrix unit, the scale being `(1/2) C_k[p][p'] τ_k[f]` with
`C_0 = x P₊ + y P₋`, `C_1 = x P₊ - y P₋`, `τ_0 = (1, 1)` and `τ_1 = (1, -1)`. Letters whose two
bond indices carry different sector labels vanish.

Fusing two sectors produces *two* weighted sectors: the stacked product of the tensors of `f`
and `f'` compresses onto the tensor of `f + f'` with the weight `x/2 = 7/16` and onto the tensor
of `f + f' + 1` with the weight `y/2 = 1/16`, with eight zero slots left over. The weights are
the occupations of the two fusion channels, and
`(7/16)^L + (1/16)^L` is their length-`L` power sum. Both targets are normal at
blocking length one and are not gauge equivalent (their one-letter traces differ), so the length
dependence here comes from two genuinely different sectors rather than from a repeated one.

This file sets up the sector tensors, the compression datum of a fusion whose stacked letters
satisfy the integer letter identity, the pair-generic reduction of that identity to two
exhaustive checks over the sixty-four letters, and the two checks for the fusion of the zero
sector with itself. By the sign rule `dimerStackedInt_eq_add` the stacked product of the sectors
`f` and `f'` is that of the sectors `0` and `f + f'`, so only one further pair needs its own
checks; they live in `TwistedDimerPairZeroOne`, and `TwistedDimerPairs` assembles the fusion rule
for every pair of sectors, with its compression datum, its consequences and its word-trace
identity.

The sector letters are indexed by the bits `MPOTensor.TwistedDimer.bitL`, `bitR`, `bitF` of the
twisted dimer, and `dimerM_eq_smul_flagMPO` identifies the sector-`f` tensor with `5/8` times its
flag sector `MPOTensor.TwistedDimer.flagMPO f`.

## Main definitions

* `P6Compression.dimerM`: the sector-`f` tensor as a matrix product operator tensor.
* `P6Compression.dimerTarget`: its view on the sixty-four-letter pair alphabet.
* `P6Compression.dimerStacked`: the stacked product of two sectors, of bond dimension sixteen.

## Main results

* `P6Compression.dimerCompressionOfLetterIdentity`: the compression datum of Theorem 7.7 for
  the fusion of any two sectors whose stacked letters satisfy the integer letter identity, and
  `P6Compression.dimer_trace_evalWord_of_compression`, the word-trace identity it implies.
* `P6Compression.dimerM_eq_smul_flagMPO`: the sector-`f` tensor is `5/8` times the flag sector of
  the twisted dimer.
* `P6Compression.dimerStackedInt_eq_add`: the sign rule, the stacked product of the sectors `f`
  and `f'` is that of the sectors `0` and `f + f'`.
* `P6Compression.dimer_letter_int_of_halves`: the letter identity of a pair of sectors follows
  from its restrictions to the two sector labels, the two exhaustive checks.
* `P6Compression.dimer_letter_int`: the integer letter identity of the fusion of the zero sector
  with itself, its two exhaustive checks carried out.
* `P6Compression.dimerTarget_isNormal`: each sector is normal at blocking length one.
* `P6Compression.dimerTarget_not_gaugeEquiv`, `P6Compression.dimerBlocks_not_gaugeEquiv`: the two
  sectors, hence the two targets of every fusion, are not gauge equivalent.

## Provenance

The construction and its exact data were first recorded in
`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex` (the resolution
`thm:p6-round44-z2`), the strategy note
`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`, and
`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §1, with the exact-arithmetic
check `checks/round44_p6_z2_twisted_dimer.py`; they are verification records, not the source.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor
open MPOTensor.TwistedDimer (bitL bitR bitF exists_eq_physIdx flagMPO flagFamily flagWeight
  flagWeight_physIdx flagFamily_isNormal)

/-! ### The sector tensors -/

/-- Sixteen times the scale `(1/2) C_k[p][p'] τ_k[f]` of a letter of the sector-`f` tensor at
`x = 7/8`, `y = 1/8` (`p6_examples_compression_data.md`, §1.1). -/
def dimerScalarInt (f : Fin 2) (a : Fin 8) : ℤ :=
  (if bitF a = 0 then (if bitL a = bitR a then 4 else 3)
    else if bitL a = bitR a then 3 else 4) *
  (if bitF a = 1 ∧ f = 1 then -1 else 1)

/-- Sixteen times the sector-`f` tensor: a scaled matrix unit at each letter, vanishing when the
two bond indices carry different sector labels. -/
def dimerMInt (f : Fin 2) (a b : Fin 8) : Matrix (Fin 4) (Fin 4) ℤ :=
  if bitF a = bitF b then
    dimerScalarInt f a •
      Matrix.single (finProdFinEquiv (bitL a, bitL b)) (finProdFinEquiv (bitR a, bitR b)) 1
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
  mulTensor_smul_complexOfRing _ (16 : ℂ)⁻¹ (dimerMInt f) (dimerMInt f') _ _

/-- **The sector tensors are the flag sectors of the twisted dimer**: the sector-`f` tensor is
`μ = 5/8` times the normalized flag sector `MPOTensor.TwistedDimer.flagMPO f`
(`p6_examples_compression_data.md`, §1.1). -/
theorem dimerM_eq_smul_flagMPO (f : Fin 2) : dimerM f = (5 / 8 : ℂ) • flagMPO f := by
  have hc : ∀ a, (16 : ℂ)⁻¹ * (dimerScalarInt f a : ℂ) = 5 / 8 * flagWeight f a := by
    intro a
    obtain ⟨p, p', k, rfl⟩ := exists_eq_physIdx a
    rw [flagWeight_physIdx]
    fin_cases f <;> fin_cases p <;> fin_cases p' <;> fin_cases k <;>
      norm_num [dimerScalarInt, MPOTensor.TwistedDimer.Cmat, MPOTensor.TwistedDimer.cDiag_eq,
        MPOTensor.TwistedDimer.cOff_eq, MPOTensor.TwistedDimer.tau, MPOTensor.TwistedDimer.mu]
  funext a b
  ext i j
  simp only [dimerM, dimerMInt, Pi.smul_apply, Matrix.smul_apply, flagMPO,
    MPOTensor.TwistedDimer.unitTensor, MPOTensor.TwistedDimer.flagCoef]
  split_ifs with h
  · simp only [complexOfInt_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs
    · push_cast
      rw [mul_one, hc]
    · simp
  · simp

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

private theorem dimerMInt_eq_zero (f : Fin 2) {a b : Fin 8} (h : bitF a ≠ bitF b) :
    dimerMInt f a b = 0 := by
  simp [dimerMInt, h]

private theorem dimerStackedInt_eq_zero (f f' : Fin 2) {i k : Fin 8}
    (h : bitF i ≠ bitF k) : mulIntTensor (dimerMInt f) (dimerMInt f') i k = 0 := by
  have hj : ∀ j : Fin 8, dimerMInt f i j ⊗ₖ dimerMInt f' j k = 0 := by
    intro j
    rcases eq_or_ne (bitF i) (bitF j) with hij | hij
    · rw [dimerMInt_eq_zero f' fun hjk => h (hij.trans hjk), Matrix.kronecker_zero]
    · rw [dimerMInt_eq_zero f hij, Matrix.zero_kronecker]
  simp [mulIntTensor, mulTensorR, hj]

/-- The sector-`f` tensor is the sector-`0` tensor with the sign `τ_k[f]` of its sector label. -/
private theorem dimerMInt_eq_sign_smul (f : Fin 2) (a b : Fin 8) :
    dimerMInt f a b = (if bitF a = 1 ∧ f = 1 then -1 else 1 : ℤ) • dimerMInt 0 a b := by
  have hs : dimerScalarInt f a =
      (if bitF a = 1 ∧ f = 1 then -1 else 1) * dimerScalarInt 0 a := by
    unfold dimerScalarInt
    generalize bitF a = c
    fin_cases c <;> fin_cases f <;> simp
    split_ifs <;> rfl
  unfold dimerMInt
  by_cases h : bitF a = bitF b
  · rw [ite_eq_left h, ite_eq_left h, hs, mul_smul]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

/-- **The sign rule of the stacked product**: the signs of two sectors on a common sector label
multiply, so the stacked product of the sectors `f` and `f'` is that of `0` and `f + f'`. -/
theorem dimerStackedInt_eq_add (f f' : Fin 2) :
    dimerStackedInt f f' = dimerStackedInt 0 (f + f') := by
  have hkron : ∀ i j k : Fin 8,
      dimerMInt f i j ⊗ₖ dimerMInt f' j k = dimerMInt 0 i j ⊗ₖ dimerMInt (f + f') j k := by
    intro i j k
    by_cases h : bitF i = bitF j
    · rw [dimerMInt_eq_sign_smul f, dimerMInt_eq_sign_smul f', dimerMInt_eq_sign_smul (f + f') j,
        Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.kronecker_smul, smul_smul, ← h]
      congr 1
      generalize_decide bitF i, f, f'
    · rw [dimerMInt_eq_zero f h, dimerMInt_eq_zero 0 h, Matrix.zero_kronecker,
        Matrix.zero_kronecker]
  funext a
  simp only [dimerStackedInt, mulIntTensor, mulTensorR, hkron]

/-- The two target blocks of the fusion of `f` and `f'` are those of the fusion of `0` and
`f + f'`. -/
theorem dimerBlockInt_eq_add (f f' : Fin 2) : dimerBlockInt f f' = dimerBlockInt 0 (f + f') := by
  funext s
  simp only [dimerBlockInt, zero_add]

/-- The letter identity at a letter whose two bond indices carry different sector labels: both
sides vanish. -/
private theorem dimer_letter_int_of_flag_ne (f f' : Fin 2) (a : Fin 64)
    (h : bitF (Fin.divNat (m := 8) (n := 8) a) ≠
      bitF (Fin.modNat (m := 8) (n := 8) a)) :
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
private theorem dimerStackedInt_even (f f' : Fin 2) {i : Fin 8} (hi : bitF i = 0)
    (k : Fin 8) : mulIntTensor (dimerMInt f) (dimerMInt f') i k = dimerStackEven f f' i k := by
  have hz : ∀ j : Fin 8, bitF j = 1 → dimerMInt f i j ⊗ₖ dimerMInt f' j k = 0 := by
    intro j hj
    rw [dimerMInt_eq_zero f (by rw [hi, hj]; decide), Matrix.zero_kronecker]
  rw [mulIntTensor, mulTensorR, Fin.sum_univ_eight, hz 1 (by decide), hz 3 (by decide),
    hz 5 (by decide), hz 7 (by decide)]
  simp only [add_zero, dimerStackEven]

/-- On a left bond index of sector label one the stacked product is its odd restriction. -/
private theorem dimerStackedInt_odd (f f' : Fin 2) {i : Fin 8} (hi : bitF i = 1)
    (k : Fin 8) : mulIntTensor (dimerMInt f) (dimerMInt f') i k = dimerStackOdd f f' i k := by
  have hz : ∀ j : Fin 8, bitF j = 0 → dimerMInt f i j ⊗ₖ dimerMInt f' j k = 0 := by
    intro j hj
    rw [dimerMInt_eq_zero f (by rw [hi, hj]; decide), Matrix.zero_kronecker]
  rw [mulIntTensor, mulTensorR, Fin.sum_univ_eight, hz 0 (by decide), hz 2 (by decide),
    hz 4 (by decide), hz 6 (by decide)]
  simp only [zero_add, add_zero, dimerStackOdd]

/-- **The letter identity from its two halves.** The integer letter identity of the fusion of
the sectors `f` and `f'` follows from its restrictions to the letters of sector label zero and
of sector label one, the two exhaustive checks carried out per pair of sectors
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimer_letter_int_of_halves (f f' : Fin 2)
    (heven : ∀ a : Fin 64,
      bitF (Fin.divNat (m := 8) (n := 8) a) = 0 →
        bitF (Fin.modNat (m := 8) (n := 8) a) = 0 →
          (2 : ℤ) • dimerStackEven f f' (Fin.divNat (m := 8) (n := 8) a)
              (Fin.modNat (m := 8) (n := 8) a) =
            ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a)
    (hodd : ∀ a : Fin 64,
      bitF (Fin.divNat (m := 8) (n := 8) a) = 1 →
        bitF (Fin.modNat (m := 8) (n := 8) a) = 1 →
          (2 : ℤ) • dimerStackOdd f f' (Fin.divNat (m := 8) (n := 8) a)
              (Fin.modNat (m := 8) (n := 8) a) =
            ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a)
    (a : Fin 64) :
    (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a := by
  have htwo : ∀ u : Fin 2, u = 0 ∨ u = 1 := by decide
  rcases eq_or_ne (bitF (Fin.divNat (m := 8) (n := 8) a))
    (bitF (Fin.modNat (m := 8) (n := 8) a)) with h | h
  · rcases htwo (bitF (Fin.divNat (m := 8) (n := 8) a)) with hi | hi
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
`tr(B^w) = (7/16)^{|w|} tr(M_{f+f'}^w) + (1/16)^{|w|} tr(M_{f+f'+1}^w)`, the periodic power sum
`(7/16)^L + (1/16)^L` (`p6_examples_compression_data.md`, §1.4). This is the fusion
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
  rw [P.trace_evalWord_eq_sum_smul w hw, show pairSlots = Finset.univ from rfl, Fin.sum_univ_two]
  simp only [dimerWeights, dimerBlocks, add_zero]
  rfl

/-! ### The letter identity of the fusion of the zero sector with itself -/

private theorem dimer_letter_int_even : ∀ a : Fin 64,
    bitF (Fin.divNat (m := 8) (n := 8) a) = 0 →
      bitF (Fin.modNat (m := 8) (n := 8) a) = 0 →
        (2 : ℤ) • dimerStackEven 0 0 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 0) s a := by
  decide +kernel

private theorem dimer_letter_int_odd : ∀ a : Fin 64,
    bitF (Fin.divNat (m := 8) (n := 8) a) = 1 →
      bitF (Fin.modNat (m := 8) (n := 8) a) = 1 →
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

/-- **Each sector is normal at blocking length one**: it is `5/8` times the flag sector of the
twisted dimer, whose letters span the four-by-four matrix algebra
(`p6_examples_compression_data.md`, §1.4). -/
theorem dimerTarget_isNormal (f : Fin 2) : Kraus.IsNormal (dimerTarget f) := by
  rw [dimerTarget, dimerM_eq_smul_flagMPO]
  exact (isNormal_smul_iff (by norm_num) (flagFamily f)).2 (flagFamily_isNormal f)

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
