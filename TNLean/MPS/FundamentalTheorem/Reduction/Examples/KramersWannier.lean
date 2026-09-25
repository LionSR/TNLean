/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Basis
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Examples.KramersWannierTensor
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Kramers–Wannier fusion `D~² = 2^L (1 + η) T` on the periodic Ising chain

**Source.** Aasen, Mong, Fendley 2016 (arXiv:1601.07185), §"The duality defect",
`References/1601.07185/source/Ising-Defects.tex` lines 994–1000: the duality-defect kernel
`⟨ĥ| D_σ |h⟩ = 2^{-L/2} (-1)^{∑_j (h_{j-1} + h_j) ĥ_{j-1/2}}` from the lattice to the dual
lattice; lines 1033–1039 and 1051–1056 (Eq. `fusionalgebra`): its square is
`D_σ² = 1 + D_ψ`, with `D_ψ` the spin flip. Seiberg, Shao 2023 (arXiv:2307.02534),
§"Non-invertible lattice translation of the transverse-field Ising model",
`References/2307.02534/source/Majoranadraft.tex` lines 2431–2437 (Eq. `noninvexplicit`): a
translation-invariant Kramers–Wannier operator `D` on one lattice;
lines 2468–2474 (Eq. `noninvfusion`): `D² = (1 + η) T / 2`, with `T` the lattice translation.

**Formalized here.** The unnormalized duality kernel on a periodic chain of `L` qubits,
`⟨s'| D~ |s⟩ = ∏_j (-1)^{s'_j (s_j + s_{j+1})}`, is the periodic trace of a bond-dimension-two
matrix product operator `W` (`kwTensor`); this is the source kernel with the factor `2^{-L/2}`
dropped and the dual site `j + 1/2` identified with the site `j`. Squaring gives, at the level of
the periodic operator, `D~² = 2^L (1 + η) T` where `η = ∏_j X_j` is the global spin flip and `T`
is the one-site left translation. Both `T` and `η T` are bond-dimension-two matrix product
operators whose four letters are literally the four matrix units of `M_2(ℂ)` (`shiftTensor`,
`flipShiftTensor`), hence normal already at word length one.

The stacked tensor `kwSquare` (bond dimension four, generating `D~²`) compresses, after an
explicit change of bond coordinates with a half-integer gauge matrix, onto the direct sum of
`2 · shiftTensor` and `2 · flipShiftTensor`: the conjugated letters are block *diagonal*, so
there are no left-over zero slots (`z = 0`) and the compression is genuinely split, with a
biorthogonal sitewise intertwiner pair for each of the two blocks.

For `L > 0`, the raw square acts as `2^{L+1} T` on the spin-flip-even subspace and
as zero on the spin-flip-odd subspace. The two virtual targets are translation and
flipped translation, not the physical even and odd subspaces.

Normalizations. Aasen–Mong–Fendley keep the factor `2^{-L/2}` and retain the primal and dual
lattices, so their square is `1 + D_ψ` with no translation. With the single-lattice convention
here, rescaling the raw kernel by `2^{-L/2}` gives square `(1 + η) T`. Seiberg–Shao instead use
the partial-isometry normalization `D² = (1 + η) T / 2`, corresponding at the level of this
square relation to rescaling the raw kernel by `2^{-(L+1)/2}`; their Pauli labels are exchanged
relative to ours, so their `η = ∏_j Z_j` is the spin flip written here as `∏_j X_j`.
Their underlying Majorana translations are invertible; the non-invertible operator in that
equation acts on the bosonic Ising chain.

## Main definitions

* `KWExample.kwTensor`: the bond-two duality kernel `W` (defined in
  `TNLean.MPS.Examples.KramersWannierTensor`).
* `KWExample.shiftTensor`, `KWExample.flipShiftTensor`: the bond-two matrix-unit tensors
  generating the translation `T` and the flipped translation `η T` (defined in
  `TNLean.MPS.Examples.KramersWannierTensor`).
* `KWExample.kwSquare`: the stacked product tensor `B^{s's} = ∑_m W^{s'm} ⊗ W^{ms}` of bond
  dimension four.
* `KWExample.kwSquareTargets`: the two weighted targets `2 · T` and `2 · η T`.

## Main results

* `KWExample.shiftMPS_isNormal`, `KWExample.flipShiftMPS_isNormal`: the two target blocks are
  normal already at word length one.
* `KWExample.kwSquare_compression`: the multi-block asymmetric compression datum, with `z = 0`.
* `KWExample.kwSquare_trace_evalWord`: the word-trace identity
  `tr(D~²)^w = 2^{|w|} (tr(T^w) + tr((η T)^w))`.
* `KWExample.kwSquare_isReduction`: biorthogonal compression onto each of the two slots.
* `KWExample.kwSquare_dim_eq`: the dimension count `4 = 2 + 2 + 0`.
* `KWExample.kwSquare_remainder_eq_zero`: the remainder of the compression vanishes identically
  (the extension splits).
* `KWExample.kwSquare_mul_right0_eq`, `KWExample.kwSquare_mul_right1_eq`,
  `KWExample.left0_mul_kwSquare_eq`, `KWExample.left1_mul_kwSquare_eq`: the four explicit
  sitewise intertwiner identities of the split case.

## References

- [arXiv:1601.07185](https://arxiv.org/abs/1601.07185) -- D. Aasen, R. S. K. Mong, P. Fendley,
  *Topological defects on the lattice I: The Ising model*
- [arXiv:2307.02534](https://arxiv.org/abs/2307.02534) -- N. Seiberg, S.-H. Shao,
  *Majorana chain and Ising model -- (non-invertible) translations, anomalies, and emanant
  symmetries*

## Provenance

The explicit tensor, gauge, and compression data were first recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §1, lines 39–150, and the compression
datum instantiates Theorem 7.7 (`thm:p5-asymmetric-compression`) of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, lines 495–569 (the
"construction note" of the declaration docstrings); these are verification records, not the
source.
-/

noncomputable section

open scoped Matrix Kronecker

namespace KWExample

open MPSTensor

/-! ### Normality of the two target blocks -/

/-- If every matrix unit occurs in the range of a length-four family, that family is
algebraically injective. -/
private theorem isInjective_of_forall_mem_range_single
    {A : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ p q : Fin 2, Matrix.single p q (1 : ℂ) ∈ Set.range A) :
    Kraus.IsInjective A := by
  exact Submodule.eq_top_of_forall_single_mem _ fun i j => Submodule.subset_span (h i j)

private theorem shiftMPS_single_mem (p q : Fin 2) :
    Matrix.single p q (1 : ℂ) ∈ Set.range shiftTensor.toMPSTensor := by
  fin_cases p <;> fin_cases q
  · exact ⟨0, by rw [shiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [shiftIntMPS, complexOfInt, Matrix.single_apply]⟩
  · exact ⟨2, by rw [shiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [shiftIntMPS, complexOfInt, Matrix.single_apply]⟩
  · exact ⟨1, by rw [shiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [shiftIntMPS, complexOfInt, Matrix.single_apply]⟩
  · exact ⟨3, by rw [shiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [shiftIntMPS, complexOfInt, Matrix.single_apply]⟩

private theorem flipShiftMPS_single_mem (p q : Fin 2) :
    Matrix.single p q (1 : ℂ) ∈ Set.range flipShiftTensor.toMPSTensor := by
  fin_cases p <;> fin_cases q
  · exact ⟨2, by rw [flipShiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [flipShiftIntMPS, complexOfInt, Matrix.single_apply]⟩
  · exact ⟨0, by rw [flipShiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [flipShiftIntMPS, complexOfInt, Matrix.single_apply]⟩
  · exact ⟨3, by rw [flipShiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [flipShiftIntMPS, complexOfInt, Matrix.single_apply]⟩
  · exact ⟨1, by rw [flipShiftMPS_eq]; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [flipShiftIntMPS, complexOfInt, Matrix.single_apply]⟩

/-- **The translation tensor is normal.** Its four letters are already the four matrix units of
`M_2(ℂ)` (construction note, §1.2). -/
theorem shiftMPS_isNormal : Kraus.IsNormal shiftTensor.toMPSTensor :=
  Kraus.IsInjective.isNormal (isInjective_of_forall_mem_range_single shiftMPS_single_mem)

/-- **The flipped-translation tensor is normal.** Its four letters are already the four matrix
units of `M_2(ℂ)` (construction note, §1.2). -/
theorem flipShiftMPS_isNormal : Kraus.IsNormal flipShiftTensor.toMPSTensor :=
  Kraus.IsInjective.isNormal (isInjective_of_forall_mem_range_single flipShiftMPS_single_mem)

/-! ### The stacked tensor of the square of the duality -/

/-- The integer entries of the stacked product tensor `B^{s's} = ∑_m W^{s'm} ⊗ W^{ms}` of bond
dimension four (construction note, §1.3). -/
def kwSquareInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![1, 1, 1, 1; 0, 0, 0, 0; 1, -1, 1, -1; 0, 0, 0, 0]
  | 1 => !![0, 0, 0, 0; 1, 1, 1, 1; 0, 0, 0, 0; -1, 1, -1, 1]
  | 2 => !![1, 1, -1, -1; 0, 0, 0, 0; -1, 1, 1, -1; 0, 0, 0, 0]
  | 3 => !![0, 0, 0, 0; 1, 1, -1, -1; 0, 0, 0, 0; 1, -1, -1, 1]

/-- The stacked product tensor of `Dtilde^2`, of bond dimension four (construction note, §1.3). -/
def kwSquare : MPSTensor 4 4 := (MPOTensor.mulTensor kwTensor kwTensor).toMPSTensor

theorem kwSquare_eq (a : Fin 4) : kwSquare a = complexOfInt (kwSquareInt a) := by
  have h : kwSquare a = complexOfInt (mulIntTensor kwIntTensor kwIntTensor
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfRing _ kwIntTensor kwIntTensor _ _
  have hint : ∀ b : Fin 4, mulIntTensor kwIntTensor kwIntTensor
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) = kwSquareInt b := by
    decide
  rw [h, hint]

/-! ### The two target blocks and the flag -/

/-- The slots of the compression: the translation and flipped-translation targets. -/
abbrev kwSquareSlots : Finset (Fin 2) := Finset.univ

/-- The bond dimension of each of the two slots. -/
abbrev kwSquareBlockDim : Fin 2 → ℕ := fun _ => 2

/-- The two target blocks: twice the translation tensor, and twice the flipped-translation
tensor (construction note, §1.3: `C_1 = 2T`, `C_2 = 2ηT`). -/
def kwSquareTargets : (s : Fin 2) → MPSTensor 4 (kwSquareBlockDim s)
  | 0 => (2 : ℂ) • shiftTensor.toMPSTensor
  | 1 => (2 : ℂ) • flipShiftTensor.toMPSTensor

private theorem complexOfInt_two_smul {m n : Type*} (M : Matrix m n ℤ) :
    complexOfInt ((2 : ℤ) • M) = (2 : ℂ) • complexOfInt M := by
  ext i j
  simp only [complexOfInt_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The integer entries of the two target blocks. -/
def kwSquareTargetsInt :
    (s : Fin 2) → Fin 4 → Matrix (Fin (kwSquareBlockDim s)) (Fin (kwSquareBlockDim s)) ℤ
  | 0 => fun a => (2 : ℤ) • shiftIntMPS a
  | 1 => fun a => (2 : ℤ) • flipShiftIntMPS a

theorem kwSquareTargets_eq (s : Fin 2) (a : Fin 4) :
    kwSquareTargets s a = complexOfInt (kwSquareTargetsInt s a) := by
  fin_cases s
  · change (2 : ℂ) • shiftTensor.toMPSTensor a = _
    rw [shiftMPS_eq]
    exact (complexOfInt_two_smul _).symm
  · change (2 : ℂ) • flipShiftTensor.toMPSTensor a = _
    rw [flipShiftMPS_eq]
    exact (complexOfInt_two_smul _).symm

/-- The change of bond coordinates of the note: `2G` is integral and `G^{-1}` is integral
(construction note, §1.3). This is the numerator `2G`. -/
def kwSquareGaugeInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 1, 0; 0, 1, 0, -1; 1, 0, -1, 0; 0, 1, 0, 1]

/-- The inverse change of bond coordinates, which is integral (construction note, §1.3). -/
def kwSquareGaugeInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, -1, 0, 1]

theorem kwSquareGauge_mul_inv_int :
    kwSquareGaugeInt * kwSquareGaugeInvInt =
      !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2] := by decide

theorem kwSquareGaugeInv_mul_int :
    kwSquareGaugeInvInt * kwSquareGaugeInt =
      !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2] := by decide

/-- The gauge matrix `G = (1/2)[[1,0,1,0],[0,1,0,-1],[1,0,-1,0],[0,1,0,1]]` of the note
(construction note, §1.3). -/
def kwSquareGaugeMat : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • complexOfInt kwSquareGaugeInt

/-- The inverse gauge matrix `G^{-1}` of the note, which is integral. -/
def kwSquareGaugeInvMat : Matrix (Fin 4) (Fin 4) ℂ := complexOfInt kwSquareGaugeInvInt

theorem kwSquareGaugeMat_mul_inv : kwSquareGaugeMat * kwSquareGaugeInvMat = 1 := by
  rw [kwSquareGaugeMat, kwSquareGaugeInvMat, smul_mul_assoc, ← complexOfInt_mul,
    kwSquareGauge_mul_inv_int]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [complexOfInt_apply, Matrix.one_apply]

theorem kwSquareGaugeInvMat_mul : kwSquareGaugeInvMat * kwSquareGaugeMat = 1 := by
  rw [kwSquareGaugeMat, kwSquareGaugeInvMat, mul_smul_comm, ← complexOfInt_mul,
    kwSquareGaugeInv_mul_int]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [complexOfInt_apply, Matrix.one_apply]

/-- The block ordering of the compression: no zero slots, both blocks are targets. -/
def kwSquareOrd : BlockIndex kwSquareSlots 0 ≃ Fin 2 where
  toFun := Sum.elim (fun s => s.1) fun t => t.elim0
  invFun s := Sum.inl ⟨s, Finset.mem_univ s⟩
  left_inv := by
    rintro (s | t)
    · rfl
    · exact t.elim0
  right_inv _ := rfl

/-- The position in the flag of the first coordinate of each block. -/
def kwSquareOffset : BlockIndex kwSquareSlots 0 → ℕ :=
  Sum.elim (fun s => ![0, 2] s.1) fun t => t.elim0

/-- The bond coordinate attached to a graded coordinate. -/
def kwSquareCoordNat (x : BlockSpace kwSquareBlockDim kwSquareSlots 0) : ℕ :=
  kwSquareOffset x.1 + (x.2 : ℕ)

theorem kwSquareCoordNat_lt (x : BlockSpace kwSquareBlockDim kwSquareSlots 0) :
    kwSquareCoordNat x < 4 := by
  revert x
  decide

/-- The labelling of the four bond coordinates by the graded block space. -/
def kwSquareTau : BlockSpace kwSquareBlockDim kwSquareSlots 0 ≃ Fin 4 where
  toFun x := ⟨kwSquareCoordNat x, kwSquareCoordNat_lt x⟩
  invFun
    | 0 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, 0⟩
    | 1 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, 1⟩
    | 2 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, 0⟩
    | 3 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, 1⟩
  left_inv := by decide
  right_inv := by decide

/-- The gauge of the compression, following the note's `G`. -/
def kwSquareGauge : (Fin 4 → ℂ) ≃ₗ[ℂ] (BlockSpace kwSquareBlockDim kwSquareSlots 0 → ℂ) :=
  gaugeOfMatrix kwSquareTau kwSquareGaugeMat kwSquareGaugeInvMat kwSquareGaugeMat_mul_inv
    kwSquareGaugeInvMat_mul

/-- The raw conjugated letters `2G B^{s's} G^{-1}` before the factor `1/2` built into the gauge
is divided out (construction note, §1.3: `G B G^{-1} = diag(2T, 2ηT)`, doubled here since `kwSquareGaugeInt`
is `2G`). -/
def kwSquareConjRawInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![4, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 4; 0, 0, 0, 0]
  | 1 => !![0, 0, 0, 0; 4, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 4]
  | 2 => !![0, 4, 0, 0; 0, 0, 0, 0; 0, 0, 4, 0; 0, 0, 0, 0]
  | 3 => !![0, 0, 0, 0; 0, 4, 0, 0; 0, 0, 0, 0; 0, 0, 4, 0]

theorem kwSquareConj_raw_int (a : Fin 4) :
    kwSquareGaugeInt * kwSquareInt a * kwSquareGaugeInvInt = kwSquareConjRawInt a := by
  revert a
  decide

/-- The letters of the compression in the block coordinates: block diagonal, with the two
target blocks `2T` and `2ηT` (construction note, §1.3). -/
def kwSquareConjInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2; 0, 0, 0, 0]
  | 1 => !![0, 0, 0, 0; 2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2]
  | 2 => !![0, 2, 0, 0; 0, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 0]
  | 3 => !![0, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 0; 0, 0, 2, 0]

theorem kwSquareConjRawInt_eq_two_smul (a : Fin 4) :
    kwSquareConjRawInt a = (2 : ℤ) • kwSquareConjInt a := by
  revert a
  decide

theorem kwSquare_conjTarget (a : Fin 4) :
    kwSquareGaugeMat * complexOfInt (kwSquareInt a) * kwSquareGaugeInvMat =
      complexOfInt (kwSquareConjInt a) := by
  have hraw : kwSquareGaugeMat * complexOfInt (kwSquareInt a) * kwSquareGaugeInvMat =
      (1 / 2 : ℂ) • complexOfInt (kwSquareConjRawInt a) := by
    rw [kwSquareGaugeMat, kwSquareGaugeInvMat, Matrix.smul_mul, Matrix.smul_mul,
      ← complexOfInt_mul, ← complexOfInt_mul, kwSquareConj_raw_int]
  rw [hraw, kwSquareConjRawInt_eq_two_smul, complexOfInt_two_smul, smul_smul,
    show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]

theorem kwSquare_conjMatrix (a : Fin 4) :
    conjMatrix kwSquareGauge (kwSquare a) =
      (complexOfInt (kwSquareConjInt a)).submatrix kwSquareTau kwSquareTau := by
  rw [kwSquareGauge, conjMatrix_gaugeOfMatrix, kwSquare_eq, kwSquare_conjTarget]

/-! ### The compression datum -/

private theorem kwSquare_triangular_int (a : Fin 4)
    (x y : BlockSpace kwSquareBlockDim kwSquareSlots 0) (h : kwSquareOrd y.1 < kwSquareOrd x.1) :
    kwSquareConjInt a (kwSquareTau x) (kwSquareTau y) = 0 := by
  revert a x y
  decide

private theorem kwSquare_matched_int (a : Fin 4) (s : Fin 2) (p q : Fin (kwSquareBlockDim s)) :
    kwSquareConjInt a (kwSquareTau ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, p⟩)
        (kwSquareTau ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, q⟩) = kwSquareTargetsInt s a p q := by
  revert a
  fin_cases s <;> revert p q <;> decide

/-- **The multi-block asymmetric compression datum of the Kramers–Wannier square** (construction note,
Theorem 7.7, clauses (i)–(iii)). There are no zero slots: `D~²` is fully split into `2T` and
`2ηT`. -/
def kwSquare_compression : MultiBlockCompression kwSquare kwSquareSlots kwSquareTargets where
  z := 0
  ord := kwSquareOrd
  gauge := kwSquareGauge
  triangular a x y h := by
    rw [kwSquare_conjMatrix, Matrix.submatrix_apply, complexOfInt_apply, Int.cast_eq_zero]
    exact kwSquare_triangular_int a x y h
  matched a s := by
    obtain ⟨s, hs⟩ := s
    ext p q
    rw [Matrix.blockDiag'_apply, kwSquare_conjMatrix, Matrix.submatrix_apply,
      complexOfInt_apply, kwSquareTargets_eq, complexOfInt_apply, Int.cast_inj]
    exact kwSquare_matched_int a s p q
  unmatched _ t := t.elim0

/-! ### Consequences -/

/-- **The word-trace identity `D~² = 2^L (1 + η) T`** at the level of traces (construction note, §1.3). -/
theorem kwSquare_trace_evalWord (w : List (Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord kwSquare w) =
      (2 : ℂ) ^ w.length * (Matrix.trace (Kraus.evalWord shiftTensor.toMPSTensor w) +
        Matrix.trace (Kraus.evalWord flipShiftTensor.toMPSTensor w)) := by
  have h := kwSquare_compression.trace_evalWord_eq_sum w hw
  rw [show kwSquareSlots = Finset.univ from rfl, Fin.sum_univ_two] at h
  have hweighted : ∀ T : MPSTensor 4 2,
      Matrix.trace (Kraus.evalWord (fun i => (2 : ℂ) • T i) w) =
        (2 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord T w) := by
    intro T
    rw [Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  have h0 : Matrix.trace (Kraus.evalWord (kwSquareTargets 0) w) =
      (2 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord shiftTensor.toMPSTensor w) :=
    hweighted shiftTensor.toMPSTensor
  have h1 : Matrix.trace (Kraus.evalWord (kwSquareTargets 1) w) =
      (2 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord flipShiftTensor.toMPSTensor w) :=
    hweighted flipShiftTensor.toMPSTensor
  rw [h, h0, h1]
  ring

/-- **Biorthogonal compression onto each of the two slots** (construction note, Theorem 7.7(iv)–(v)). -/
theorem kwSquare_isReduction (s : {s // s ∈ kwSquareSlots}) :
    IsReduction kwSquare (kwSquareTargets s.1) (kwSquare_compression.left s)
      (kwSquare_compression.right s) :=
  kwSquare_compression.isReduction s

/-- Two distinct slots are biorthogonal (construction note, Theorem 7.7(iv)). -/
theorem kwSquare_left_mul_right_of_ne {s t : {s // s ∈ kwSquareSlots}} (h : s ≠ t) :
    kwSquare_compression.left s * kwSquare_compression.right t = 0 :=
  kwSquare_compression.left_mul_right_of_ne h

/-- **The dimension count**: `4 = 2 + 2 + 0` (construction note, Theorem 7.7(vii)). -/
theorem kwSquare_dim_eq : (4 : ℕ) = ∑ s ∈ kwSquareSlots, kwSquareBlockDim s + 0 :=
  kwSquare_compression.dim_eq

/-! ### The explicit compression pair and the vanishing remainder -/

/-- The left compression witness `W_1 = (1/2)[[1,0,1,0],[0,1,0,-1]]` of the note (construction note,
§1.3). -/
def kwSquareLeft0Int : Matrix (Fin 2) (Fin 4) ℤ := !![1, 0, 1, 0; 0, 1, 0, -1]

/-- The left compression witness `W_2 = (1/2)[[1,0,-1,0],[0,1,0,1]]` of the note (construction note,
§1.3). -/
def kwSquareLeft1Int : Matrix (Fin 2) (Fin 4) ℤ := !![1, 0, -1, 0; 0, 1, 0, 1]

/-- The right compression witness `V_1 = [[1,0],[0,1],[1,0],[0,-1]]` of the note (construction note,
§1.3). -/
def kwSquareRight0Int : Matrix (Fin 4) (Fin 2) ℤ := !![1, 0; 0, 1; 1, 0; 0, -1]

/-- The right compression witness `V_2 = [[1,0],[0,1],[-1,0],[0,1]]` of the note (construction note,
§1.3). -/
def kwSquareRight1Int : Matrix (Fin 4) (Fin 2) ℤ := !![1, 0; 0, 1; -1, 0; 0, 1]

/-- The left compression witness `W_1`. -/
def kwSquareLeft0 : Matrix (Fin 2) (Fin 4) ℂ := (1 / 2 : ℂ) • complexOfInt kwSquareLeft0Int

/-- The left compression witness `W_2`. -/
def kwSquareLeft1 : Matrix (Fin 2) (Fin 4) ℂ := (1 / 2 : ℂ) • complexOfInt kwSquareLeft1Int

/-- The right compression witness `V_1`. -/
def kwSquareRight0 : Matrix (Fin 4) (Fin 2) ℂ := complexOfInt kwSquareRight0Int

/-- The right compression witness `V_2`. -/
def kwSquareRight1 : Matrix (Fin 4) (Fin 2) ℂ := complexOfInt kwSquareRight1Int

theorem kwSquareLeft0_eq :
    kwSquare_compression.left ⟨0, Finset.mem_univ 0⟩ = kwSquareLeft0 := by
  rw [MultiBlockCompression.left_gaugeOfMatrix kwSquare_compression
    (hG := kwSquareGaugeMat_mul_inv) (hG' := kwSquareGaugeInvMat_mul) rfl]
  ext i y
  simp only [Matrix.submatrix_apply, id_eq, kwSquareGaugeMat, kwSquareLeft0, Matrix.smul_apply,
    complexOfInt_apply, smul_eq_mul]
  fin_cases i <;> fin_cases y <;> congr 1

theorem kwSquareLeft1_eq :
    kwSquare_compression.left ⟨1, Finset.mem_univ 1⟩ = kwSquareLeft1 := by
  rw [MultiBlockCompression.left_gaugeOfMatrix kwSquare_compression
    (hG := kwSquareGaugeMat_mul_inv) (hG' := kwSquareGaugeInvMat_mul) rfl]
  ext i y
  simp only [Matrix.submatrix_apply, id_eq, kwSquareGaugeMat, kwSquareLeft1, Matrix.smul_apply,
    complexOfInt_apply, smul_eq_mul]
  fin_cases i <;> fin_cases y <;> congr 1

theorem kwSquareRight0_eq :
    kwSquare_compression.right ⟨0, Finset.mem_univ 0⟩ = kwSquareRight0 := by
  rw [MultiBlockCompression.right_gaugeOfMatrix kwSquare_compression
    (hG := kwSquareGaugeMat_mul_inv) (hG' := kwSquareGaugeInvMat_mul) rfl]
  ext x j
  simp only [Matrix.submatrix_apply, id_eq, kwSquareGaugeInvMat, kwSquareRight0,
    complexOfInt_apply]
  fin_cases j <;> fin_cases x <;>
    exact_mod_cast (by decide)

theorem kwSquareRight1_eq :
    kwSquare_compression.right ⟨1, Finset.mem_univ 1⟩ = kwSquareRight1 := by
  rw [MultiBlockCompression.right_gaugeOfMatrix kwSquare_compression
    (hG := kwSquareGaugeMat_mul_inv) (hG' := kwSquareGaugeInvMat_mul) rfl]
  ext x j
  simp only [Matrix.submatrix_apply, id_eq, kwSquareGaugeInvMat, kwSquareRight1,
    complexOfInt_apply]
  fin_cases j <;> fin_cases x <;>
    exact_mod_cast (by decide)

private theorem kwSquare_remainder_int (a : Fin 4) :
    (2 : ℤ) • kwSquareInt a =
      kwSquareRight0Int * kwSquareTargetsInt 0 a * kwSquareLeft0Int +
        kwSquareRight1Int * kwSquareTargetsInt 1 a * kwSquareLeft1Int := by
  revert a
  decide

/-- The subtype `{s // s ∈ kwSquareSlots}` of the two slots is equivalent to `Fin 2` via its
underlying value. -/
private def kwSquareSlotEquiv : Fin 2 ≃ {s // s ∈ kwSquareSlots} where
  toFun s := ⟨s, Finset.mem_univ s⟩
  invFun s := s.1
  left_inv _ := rfl
  right_inv _s := Subtype.ext rfl

/-- Expanding the compression's slot-indexed sum into its two explicit summands. -/
private theorem kwSquareSlots_sum {M : Type*} [AddCommMonoid M]
    (f : {s // s ∈ kwSquareSlots} → M) :
    ∑ s, f s = f ⟨0, Finset.mem_univ 0⟩ + f ⟨1, Finset.mem_univ 1⟩ := by
  rw [← Equiv.sum_comp kwSquareSlotEquiv f, Fin.sum_univ_two]
  rfl

/-- **The remainder of the compression vanishes identically.** The extension is fully split:
the stacked tensor is gauge equivalent to the direct sum of `2T` and `2ηT` (construction note, §1.3). -/
theorem kwSquare_remainder_eq_zero (a : Fin 4) : kwSquare_compression.remainder a = 0 := by
  have hsum : kwSquare_compression.remainder a =
      kwSquare a - (kwSquareRight0 * kwSquareTargets 0 a * kwSquareLeft0 +
        kwSquareRight1 * kwSquareTargets 1 a * kwSquareLeft1) := by
    rw [MultiBlockCompression.remainder, kwSquareSlots_sum, kwSquareRight0_eq, kwSquareLeft0_eq,
      kwSquareRight1_eq, kwSquareLeft1_eq]
  rw [hsum, sub_eq_zero, kwSquareRight0, kwSquareRight1, kwSquareLeft0, kwSquareLeft1,
    kwSquareTargets_eq, kwSquareTargets_eq, kwSquare_eq]
  simp only [Matrix.mul_smul, ← complexOfInt_mul, ← smul_add, ← complexOfInt_add]
  rw [← kwSquare_remainder_int, complexOfInt_two_smul, smul_smul,
    show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]

/-! ### The sitewise intertwiners (the split case) -/

private theorem kwSquare_mul_right0_int (a : Fin 4) :
    kwSquareInt a * kwSquareRight0Int = kwSquareRight0Int * kwSquareTargetsInt 0 a := by
  revert a
  decide

private theorem kwSquare_mul_right1_int (a : Fin 4) :
    kwSquareInt a * kwSquareRight1Int = kwSquareRight1Int * kwSquareTargetsInt 1 a := by
  revert a
  decide

private theorem left0_mul_kwSquare_int (a : Fin 4) :
    kwSquareLeft0Int * kwSquareInt a = kwSquareTargetsInt 0 a * kwSquareLeft0Int := by
  revert a
  decide

private theorem left1_mul_kwSquare_int (a : Fin 4) :
    kwSquareLeft1Int * kwSquareInt a = kwSquareTargetsInt 1 a * kwSquareLeft1Int := by
  revert a
  decide

/-- **The right sitewise intertwiner for the translation block** (construction note, §1.3):
`B^{s's} V_1 = V_1 (2T)^{s's}`. -/
theorem kwSquare_mul_right0_eq (a : Fin 4) :
    kwSquare a * kwSquareRight0 = kwSquareRight0 * kwSquareTargets 0 a := by
  rw [kwSquareTargets_eq, kwSquareRight0, kwSquare_eq, ← complexOfInt_mul, ← complexOfInt_mul,
    kwSquare_mul_right0_int]

/-- **The right sitewise intertwiner for the flipped-translation block** (construction note, §1.3):
`B^{s's} V_2 = V_2 (2ηT)^{s's}`. -/
theorem kwSquare_mul_right1_eq (a : Fin 4) :
    kwSquare a * kwSquareRight1 = kwSquareRight1 * kwSquareTargets 1 a := by
  rw [kwSquareTargets_eq, kwSquareRight1, kwSquare_eq, ← complexOfInt_mul, ← complexOfInt_mul,
    kwSquare_mul_right1_int]

/-- **The left sitewise intertwiner for the translation block** (construction note, §1.3):
`W_1 B^{s's} = (2T)^{s's} W_1`. -/
theorem left0_mul_kwSquare_eq (a : Fin 4) :
    kwSquareLeft0 * kwSquare a = kwSquareTargets 0 a * kwSquareLeft0 := by
  rw [kwSquareTargets_eq, kwSquareLeft0, kwSquare_eq, Matrix.smul_mul, Matrix.mul_smul,
    ← complexOfInt_mul, ← complexOfInt_mul, left0_mul_kwSquare_int]

/-- **The left sitewise intertwiner for the flipped-translation block** (construction note, §1.3):
`W_2 B^{s's} = (2ηT)^{s's} W_2`. -/
theorem left1_mul_kwSquare_eq (a : Fin 4) :
    kwSquareLeft1 * kwSquare a = kwSquareTargets 1 a * kwSquareLeft1 := by
  rw [kwSquareTargets_eq, kwSquareLeft1, kwSquare_eq, Matrix.smul_mul, Matrix.mul_smul,
    ← complexOfInt_mul, ← complexOfInt_mul, left1_mul_kwSquare_int]

/-- `W_1 V_1 = 1`: the biorthogonal normalisation of the translation sitewise intertwiner
pair. -/
theorem kwSquareLeft0_mul_right0 : kwSquareLeft0 * kwSquareRight0 = 1 :=
  kwSquareLeft0_eq ▸ kwSquareRight0_eq ▸ kwSquare_compression.left_mul_right_self
    ⟨0, Finset.mem_univ 0⟩

/-- `W_2 V_2 = 1`: the biorthogonal normalisation of the flipped-translation sitewise intertwiner
pair. -/
theorem kwSquareLeft1_mul_right1 : kwSquareLeft1 * kwSquareRight1 = 1 :=
  kwSquareLeft1_eq ▸ kwSquareRight1_eq ▸ kwSquare_compression.left_mul_right_self
    ⟨1, Finset.mem_univ 1⟩

end KWExample
