/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousTensor

/-!
# The group-law fusion blocks of the anomalous `ℤ/3` symmetry

Machine-checked instances of the multi-block asymmetric compression theorem (P5 note,
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) for the
stacked products `U ⊗ U` and `U† ⊗ U†` of the anomalous `ℤ/3` representation `{1, U, U†}` of
`Z3AnomalousTensor.lean`; the two remaining products `U ⊗ U†` and `U† ⊗ U`, which fuse to the
identity, are treated in `Z3AnomalousInverseFusion.lean`. The exact data are recorded in
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, §2.1 and §2.4, and verified in exact
arithmetic over `ℤ[ω]` by `Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`.

The representation is exact, so each stacked product of bond dimension four has the word traces of a
single block of the representation: `U ⊗ U → U†` and `U† ⊗ U† → U`, each with two zero slots and a
unimodular gauge over `ℤ[ω]`. Both compressions are genuinely asymmetric: the remainder is nilpotent
of order exactly three, which attains the bound `|S| + z = 3` of Theorem 7.7(vi), and both sitewise
intertwiner spaces vanish, so neither block admits a sitewise fusion pair. For the anomalous `ℤ/2`
symmetry of Example D the absence of sitewise intertwiners is the algebraic trace of the anomaly
(`Splitting.lean`); the non-anomalous `ℤ/3` clock symmetry of the data file (§3) has, by contrast, a
biorthogonal sitewise fusion pair on its `U ⊗ U → U²` block.

Unitarity of `U`, which identifies `U†` with the adjoint of `U`, is not formalized here; `U†`
denotes the inverse `U² = U⁻¹` of the representation.

## Main definitions

* `Z3Anomalous.uu_compression`, `Z3Anomalous.dd_compression`: the compression data of the two
  blocks.

## Main results

* `Z3Anomalous.uu_trace_evalWord`, `Z3Anomalous.dd_trace_evalWord`: the word-trace form of the
  fusion rules `U U = U†` and `U† U† = U`.
* `Z3Anomalous.uu_isReduction`, `Z3Anomalous.uu_left_eq`, `Z3Anomalous.uu_right_eq` and their
  `dd` siblings: the explicit biorthogonal compression pairs.
* `Z3Anomalous.uu_evalWord_remainder_eq_zero`, `Z3Anomalous.uu_remainder_mul_ne_zero` and their
  `dd` siblings: the remainders are nilpotent of order exactly three.
* `Z3Anomalous.uu_right_intertwiner_eq_zero`, `Z3Anomalous.uu_left_intertwiner_eq_zero` and
  their `dd` siblings: no sitewise intertwiner in either direction.
* `Z3Anomalous.mpo_uu`, `Z3Anomalous.mpo_dd`: the fusion rules as identities of periodic
  operators.
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open EisensteinInt MPSTensor

/-! ### The flag shape of a two-dimensional target -/

/-- The single slot of a fusion block. -/
abbrev singleSlot : Finset Unit := Finset.univ

/-- The single slot as an element of the slot subtype. -/
abbrev theSlot : {s // s ∈ singleSlot} := ⟨(), Finset.mem_univ ()⟩

/-- The bond dimension of a two-dimensional target. -/
abbrev pairDim : Unit → ℕ := fun _ => 2

/-- The block ordering of the blocks with a two-dimensional target: a zero slot, the target, a
zero slot (data file §2.1 and §2.4). -/
def pairOrd : BlockIndex singleSlot 2 ≃ Fin 3 where
  toFun
    | Sum.inl _ => 1
    | Sum.inr t => ![0, 2] t
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inl theSlot
    | 2 => Sum.inr 1
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinate attached to a graded coordinate of a block with a two-dimensional
target. -/
def pairCoordNat (x : BlockSpace pairDim singleSlot 2) : ℕ :=
  Sum.elim (fun _ => 1) ![0, 3] x.1 + (x.2 : ℕ)

theorem pairCoordNat_lt (x : BlockSpace pairDim singleSlot 2) : pairCoordNat x < 4 := by
  revert x
  decide

/-- The labelling of the four bond coordinates of a block with a two-dimensional target by the
graded block space. -/
def pairCoord : BlockSpace pairDim singleSlot 2 ≃ Fin 4 where
  toFun x := ⟨pairCoordNat x, pairCoordNat_lt x⟩
  invFun
    | 0 => ⟨Sum.inr 0, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inl theSlot, ⟨0, by decide⟩⟩
    | 2 => ⟨Sum.inl theSlot, ⟨1, by decide⟩⟩
    | 3 => ⟨Sum.inr 1, ⟨0, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

/-! ### The block `U ⊗ U → U†` (data file §2.1)

The stacked tensor of `U ⊗ U` compresses onto `U†` with `z = 2` zero slots, in the flag order a zero
slot, the target, a zero slot. The remainder is nilpotent of order exactly three, and both sitewise
intertwiner spaces vanish.
-/

/-- The change of bond coordinates of the block `U ⊗ U → U†` (data file §2.1); its inverse
`uuGaugeInvEis` has the adapted basis as columns and unit determinant. -/
def uuGaugeEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]

/-- The inverse change of bond coordinates of the block `U ⊗ U → U†` (data file §2.1). -/
def uuGaugeInvEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem uuGauge_mul_inv : uuGaugeEis * uuGaugeInvEis = 1 := by decide +kernel

theorem uuGaugeInv_mul : uuGaugeInvEis * uuGaugeEis = 1 := by decide +kernel

/-- The letters of the stacked tensor of `U ⊗ U` in the block coordinates: block upper triangular,
with the letters of `U†` on the diagonal block of the target and zero on the zero slots (data file
§2.1). -/
def uuConjEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 => 0
  | 1 =>
    !![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 6 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 7 => 0
  | 8 => 0

theorem uu_conj_eq (i : Fin 9) :
    uuGaugeEis * uuStackEis i * uuGaugeInvEis = uuConjEis i := by
  revert i
  decide +kernel

/-- The single target of the block `U ⊗ U → U†`. -/
def uuTarget : (s : Unit) → MPSTensor 9 (pairDim s) := fun _ => uDagMPS

theorem uuTarget_eq (s : Unit) (a : Fin 9) :
    uuTarget s a = complexOfEisenstein (uDagEisMPS a) :=
  uDagMPS_eq a

private theorem uu_triangular (i : Fin 9) (x y : BlockSpace pairDim singleSlot 2)
    (h : pairOrd y.1 < pairOrd x.1) :
    (uuGaugeEis * uuStackEis i * uuGaugeInvEis) (pairCoord x) (pairCoord y) = 0 := by
  rw [uu_conj_eq]
  revert i x y h
  decide +kernel

private theorem uu_matched (i : Fin 9) :
    (Matrix.of fun p q : Fin 2 =>
      uuConjEis i (pairCoord ⟨Sum.inl theSlot, p⟩) (pairCoord ⟨Sum.inl theSlot, q⟩)) =
      uDagEisMPS i := by
  revert i
  decide +kernel

private theorem uu_unmatched (i : Fin 9) (t : Fin 2) :
    (Matrix.of fun p q : Fin 1 =>
      uuConjEis i (pairCoord ⟨Sum.inr t, p⟩) (pairCoord ⟨Sum.inr t, q⟩)) = 0 := by
  revert i t
  decide +kernel

/-- **The multi-block asymmetric compression datum of the block `U ⊗ U → U†`** (P5 note, Theorem
7.7, clauses (i)–(iii); data file §2.1): the stacked tensor of `U ⊗ U` compresses onto `U†` with `2`
zero slots. -/
def uu_compression : MultiBlockCompression uuStack singleSlot uuTarget :=
  MultiBlockCompression.ofEisenstein uuStackEis uuStack_eq (fun _ => uDagEisMPS)
    uuTarget_eq 2 pairOrd pairCoord uuGaugeEis uuGaugeInvEis uuGauge_mul_inv uuGaugeInv_mul
    uu_triangular
    (fun i s p q => by
      rw [uu_conj_eq]
      obtain ⟨⟨⟩, _⟩ := s
      exact congrFun (congrFun (uu_matched i) p) q)
    (fun i t p q => by
      rw [uu_conj_eq]
      exact congrFun (congrFun (uu_unmatched i t) p) q)

/-- **The word-trace form of `U ⊗ U → U†`** (data file §2.1): at every positive length the stacked
tensor of `U ⊗ U` has the word traces of `U†`. -/
theorem uu_trace_evalWord (w : List (Fin 9)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord uuStack w) =
      Matrix.trace (Kraus.evalWord uDagMPS w) := by
  have h := uu_compression.trace_evalWord_eq_sum w hw
  rwa [Fintype.sum_unique] at h

/-- **Biorthogonal compression of `U ⊗ U → U†`** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem uu_isReduction :
    IsReduction uuStack uDagMPS (uu_compression.left theSlot)
      (uu_compression.right theSlot) :=
  uu_compression.isReduction theSlot

/-- The compression pair of `U ⊗ U → U†` is the recorded one (data file §2.1): `V` is the column
block of the inverse gauge carrying the target and `W` the row block of the gauge. -/
theorem uu_right_eq :
    uu_compression.right theSlot =
      complexOfEisenstein !![⟨0, 0⟩, ⟨0, 0⟩;
           ⟨0, 0⟩, ⟨0, -1⟩;
           ⟨0, 0⟩, ⟨1, 1⟩;
           ⟨-1, 0⟩, ⟨0, 0⟩] := by
  rw [uu_compression.right_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one uuGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one uuGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

theorem uu_left_eq :
    uu_compression.left theSlot =
      complexOfEisenstein !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩;
           ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩] := by
  rw [uu_compression.left_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one uuGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one uuGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

/-- **The dimension count of `U ⊗ U → U†`**: `4 = 2 + 2` (P5 note, Theorem 7.7(vii)). -/
theorem uu_dim_eq : (4 : ℕ) = ∑ s ∈ singleSlot, pairDim s + 2 :=
  uu_compression.dim_eq

/-- The remainder letters `R^i = B^i - V C^i W` of the block `U ⊗ U → U†` (data file §2.1). -/
def uuRemainderEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 => 0
  | 1 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 =>
    !![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]
  | 6 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 7 => 0
  | 8 => 0

theorem uu_remainder_eq (i : Fin 9) :
    uu_compression.remainder i = complexOfEisenstein (uuRemainderEis i) := by
  rw [MultiBlockCompression.remainder,
    Finset.sum_eq_single_of_mem theSlot (Finset.mem_univ theSlot)
      fun b _ hb => absurd (Subtype.ext (Subsingleton.elim b.1 theSlot.1)) hb,
    uu_left_eq, uu_right_eq, uuStack_eq, uuTarget_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, ← complexOfEisenstein_sub]
  congr 1
  revert i
  decide +kernel

/-- The three letters carrying the nonzero remainder matrices of `U ⊗ U → U†`. -/
def uuRemainderSupport : Fin 3 → Fin 9 := ![1, 5, 6]

private theorem uuRemainder_support (a : Fin 9) :
    uuRemainderEis a = 0 ∨ ∃ j, uuRemainderSupport j = a := by
  revert a
  decide +kernel

private theorem uuRemainder_triple_support (i j l : Fin 3) :
    uuRemainderEis (uuRemainderSupport i) * uuRemainderEis (uuRemainderSupport j) *
      uuRemainderEis (uuRemainderSupport l) = 0 := by
  revert i j l
  decide +kernel

private theorem uuRemainder_triple (a b c : Fin 9) :
    uuRemainderEis a * uuRemainderEis b * uuRemainderEis c = 0 :=
  triple_mul_eq_zero_of_support _ uuRemainderSupport uuRemainder_support
    uuRemainder_triple_support a b c

/-- **Nilpotency of the remainder of `U ⊗ U → U†`** (data file §2.1): every word of length three in
the remainder vanishes, so the nilpotency order is at most three, the bound of Theorem 7.7(vi) is
attained. -/
theorem uu_evalWord_remainder_eq_zero (w : List (Fin 9)) (hw : 3 ≤ w.length) :
    Kraus.evalWord uu_compression.remainder w = 0 := by
  refine evalWord_eq_zero_of_triple_mul_eq_zero _ (fun a b c => ?_) w hw
  rw [uu_remainder_eq, uu_remainder_eq, uu_remainder_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, uuRemainder_triple, complexOfEisenstein_zero]

/-- The nilpotency order of the remainder of `U ⊗ U → U†` is exactly three, as recorded in the data
file (§2.1): the product of the remainder letters `1` and `5` does not vanish. -/
theorem uu_remainder_mul_ne_zero :
    uu_compression.remainder 1 * uu_compression.remainder 5 ≠ 0 := by
  rw [uu_remainder_eq, uu_remainder_eq, ← complexOfEisenstein_mul]
  exact complexOfEisenstein_ne_zero (by decide)

/-- The selected sitewise intertwining equations of the right certificate of `U ⊗ U → U†`. -/
def uuRightRows : Fin 8 → Fin 9 × Fin 4 × Fin 2 :=
  ![(1, 0, 1), (5, 0, 0), (6, 0, 0), (1, 0, 0), (1, 1, 0), (1, 2, 0), (5, 0, 1), (6, 0, 1)]

/-- The left inverse, up to the scalar `⟨3, 6⟩`, of the coefficient matrix of the selected equations
of the right certificate of `U ⊗ U → U†`. -/
def uuRightCert : Matrix (Fin 8) (Fin 8) EisensteinInt :=
  !![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩;
     ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨-1, 1⟩;
     ⟨0, 0⟩, ⟨3, 6⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-2, -4⟩, ⟨1, -1⟩, ⟨-2, -1⟩, ⟨-2, -4⟩, ⟨1, -1⟩, ⟨1, 2⟩, ⟨1, -1⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 6⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-2, -1⟩, ⟨-2, -4⟩, ⟨1, -1⟩, ⟨-2, -1⟩, ⟨-2, -4⟩, ⟨-2, -1⟩, ⟨1, 2⟩;
     ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩, ⟨1, 2⟩, ⟨1, -1⟩, ⟨-2, -1⟩, ⟨1, -1⟩, ⟨-2, -1⟩;
     ⟨3, 6⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

private theorem uuRight_certificate :
    (Matrix.of fun rs j => uuRightCert (finProdFinEquiv (m := 4) (n := 2) rs) j) *
        (sitewiseEqMatrix uuStackEis uDagEisMPS).submatrix uuRightRows id =
      (⟨3, 6⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero right sitewise intertwiner for `U ⊗ U → U†`** (data file §2.1): the compression
exists at the level of words but not site by site. -/
theorem uu_right_intertwiner_eq_zero (X : Matrix (Fin 4) (Fin 2) ℂ)
    (hX : ∀ i, uuStack i * X = X * uDagMPS i) : X = 0 :=
  right_intertwiner_eq_zero_of_eisenstein uuStackEis uuStack_eq uDagEisMPS uDagMPS_eq
    uuRightRows _ (by decide) uuRight_certificate X hX

/-- The selected sitewise intertwining equations of the left certificate of `U ⊗ U → U†`. -/
def uuLeftRows : Fin 8 → Fin 9 × Fin 4 × Fin 2 :=
  ![(1, 0, 0), (1, 1, 0), (1, 2, 0), (5, 0, 0), (5, 2, 0), (5, 3, 0), (6, 1, 0), (1, 3, 1)]

/-- The left inverse, up to the scalar `⟨1, 0⟩`, of the coefficient matrix of the selected equations
of the left certificate of `U ⊗ U → U†`. -/
def uuLeftCert : Matrix (Fin 8) (Fin 8) EisensteinInt :=
  !![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

private theorem uuLeft_certificate :
    (Matrix.of fun rs j => uuLeftCert (finProdFinEquiv (m := 4) (n := 2) rs) j) *
        (sitewiseEqMatrix (fun i => (uuStackEis i)ᵀ)
          fun i => (uDagEisMPS i)ᵀ).submatrix uuLeftRows id =
      (⟨1, 0⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero left sitewise intertwiner for `U ⊗ U → U†`** (data file §2.1). -/
theorem uu_left_intertwiner_eq_zero (Y : Matrix (Fin 2) (Fin 4) ℂ)
    (hY : ∀ i, Y * uuStack i = uDagMPS i * Y) : Y = 0 :=
  left_intertwiner_eq_zero_of_eisenstein uuStackEis uuStack_eq uDagEisMPS uDagMPS_eq
    uuLeftRows _ (by decide) uuLeft_certificate Y hY

/-- **The fusion rule `U ⊗ U → U†` as an identity of periodic operators** at every positive length
(data file §2.1). -/
theorem mpo_uu (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uTensor L * MPOTensor.mpo uTensor L = MPOTensor.mpo uDagTensor L :=
  MPOTensor.mpo_mul_eq_of_trace_evalWord uTensor uTensor uDagTensor uu_trace_evalWord L hL

/-! ### The block `U† ⊗ U† → U` (data file §2.4)

The stacked tensor of `U† ⊗ U†` compresses onto `U` with `z = 2` zero slots, in the flag order a
zero slot, the target, a zero slot. The remainder is nilpotent of order exactly three, and both
sitewise intertwiner spaces vanish.
-/

/-- The change of bond coordinates of the block `U† ⊗ U† → U` (data file §2.4); its inverse
`ddGaugeInvEis` has the adapted basis as columns and unit determinant. -/
def ddGaugeEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]

/-- The inverse change of bond coordinates of the block `U† ⊗ U† → U` (data file §2.4). -/
def ddGaugeInvEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem ddGauge_mul_inv : ddGaugeEis * ddGaugeInvEis = 1 := by decide +kernel

theorem ddGaugeInv_mul : ddGaugeInvEis * ddGaugeEis = 1 := by decide +kernel

/-- The letters of the stacked tensor of `U† ⊗ U†` in the block coordinates: block upper triangular,
with the letters of `U` on the diagonal block of the target and zero on the zero slots (data file
§2.4). -/
def ddConjEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 => 0
  | 1 => 0
  | 2 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 3 =>
    !![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 8 => 0

theorem dd_conj_eq (i : Fin 9) :
    ddGaugeEis * ddStackEis i * ddGaugeInvEis = ddConjEis i := by
  revert i
  decide +kernel

/-- The single target of the block `U† ⊗ U† → U`. -/
def ddTarget : (s : Unit) → MPSTensor 9 (pairDim s) := fun _ => uMPS

theorem ddTarget_eq (s : Unit) (a : Fin 9) :
    ddTarget s a = complexOfEisenstein (uEisMPS a) :=
  uMPS_eq a

private theorem dd_triangular (i : Fin 9) (x y : BlockSpace pairDim singleSlot 2)
    (h : pairOrd y.1 < pairOrd x.1) :
    (ddGaugeEis * ddStackEis i * ddGaugeInvEis) (pairCoord x) (pairCoord y) = 0 := by
  rw [dd_conj_eq]
  revert i x y h
  decide +kernel

private theorem dd_matched (i : Fin 9) :
    (Matrix.of fun p q : Fin 2 =>
      ddConjEis i (pairCoord ⟨Sum.inl theSlot, p⟩) (pairCoord ⟨Sum.inl theSlot, q⟩)) =
      uEisMPS i := by
  revert i
  decide +kernel

private theorem dd_unmatched (i : Fin 9) (t : Fin 2) :
    (Matrix.of fun p q : Fin 1 =>
      ddConjEis i (pairCoord ⟨Sum.inr t, p⟩) (pairCoord ⟨Sum.inr t, q⟩)) = 0 := by
  revert i t
  decide +kernel

/-- **The multi-block asymmetric compression datum of the block `U† ⊗ U† → U`** (P5 note, Theorem
7.7, clauses (i)–(iii); data file §2.4): the stacked tensor of `U† ⊗ U†` compresses onto `U` with
`2` zero slots. -/
def dd_compression : MultiBlockCompression ddStack singleSlot ddTarget :=
  MultiBlockCompression.ofEisenstein ddStackEis ddStack_eq (fun _ => uEisMPS)
    ddTarget_eq 2 pairOrd pairCoord ddGaugeEis ddGaugeInvEis ddGauge_mul_inv ddGaugeInv_mul
    dd_triangular
    (fun i s p q => by
      rw [dd_conj_eq]
      obtain ⟨⟨⟩, _⟩ := s
      exact congrFun (congrFun (dd_matched i) p) q)
    (fun i t p q => by
      rw [dd_conj_eq]
      exact congrFun (congrFun (dd_unmatched i t) p) q)

/-- **The word-trace form of `U† ⊗ U† → U`** (data file §2.4): at every positive length the stacked
tensor of `U† ⊗ U†` has the word traces of `U`. -/
theorem dd_trace_evalWord (w : List (Fin 9)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord ddStack w) =
      Matrix.trace (Kraus.evalWord uMPS w) := by
  have h := dd_compression.trace_evalWord_eq_sum w hw
  rwa [Fintype.sum_unique] at h

/-- **Biorthogonal compression of `U† ⊗ U† → U`** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem dd_isReduction :
    IsReduction ddStack uMPS (dd_compression.left theSlot)
      (dd_compression.right theSlot) :=
  dd_compression.isReduction theSlot

/-- The compression pair of `U† ⊗ U† → U` is the recorded one (data file §2.4): `V` is the column
block of the inverse gauge carrying the target and `W` the row block of the gauge. -/
theorem dd_right_eq :
    dd_compression.right theSlot =
      complexOfEisenstein !![⟨0, 0⟩, ⟨0, 0⟩;
           ⟨0, 0⟩, ⟨-1, 0⟩;
           ⟨0, 0⟩, ⟨0, -1⟩;
           ⟨1, 1⟩, ⟨0, 0⟩] := by
  rw [dd_compression.right_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one ddGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one ddGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

theorem dd_left_eq :
    dd_compression.left theSlot =
      complexOfEisenstein !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩;
           ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] := by
  rw [dd_compression.left_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one ddGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one ddGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

/-- **The dimension count of `U† ⊗ U† → U`**: `4 = 2 + 2` (P5 note, Theorem 7.7(vii)). -/
theorem dd_dim_eq : (4 : ℕ) = ∑ s ∈ singleSlot, pairDim s + 2 :=
  dd_compression.dim_eq

/-- The remainder letters `R^i = B^i - V C^i W` of the block `U† ⊗ U† → U` (data file §2.4). -/
def ddRemainderEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 => 0
  | 1 => 0
  | 2 =>
    !![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]
  | 3 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 8 => 0

theorem dd_remainder_eq (i : Fin 9) :
    dd_compression.remainder i = complexOfEisenstein (ddRemainderEis i) := by
  rw [MultiBlockCompression.remainder,
    Finset.sum_eq_single_of_mem theSlot (Finset.mem_univ theSlot)
      fun b _ hb => absurd (Subtype.ext (Subsingleton.elim b.1 theSlot.1)) hb,
    dd_left_eq, dd_right_eq, ddStack_eq, ddTarget_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, ← complexOfEisenstein_sub]
  congr 1
  revert i
  decide +kernel

/-- The three letters carrying the nonzero remainder matrices of `U† ⊗ U† → U`. -/
def ddRemainderSupport : Fin 3 → Fin 9 := ![2, 3, 7]

private theorem ddRemainder_support (a : Fin 9) :
    ddRemainderEis a = 0 ∨ ∃ j, ddRemainderSupport j = a := by
  revert a
  decide +kernel

private theorem ddRemainder_triple_support (i j l : Fin 3) :
    ddRemainderEis (ddRemainderSupport i) * ddRemainderEis (ddRemainderSupport j) *
      ddRemainderEis (ddRemainderSupport l) = 0 := by
  revert i j l
  decide +kernel

private theorem ddRemainder_triple (a b c : Fin 9) :
    ddRemainderEis a * ddRemainderEis b * ddRemainderEis c = 0 :=
  triple_mul_eq_zero_of_support _ ddRemainderSupport ddRemainder_support
    ddRemainder_triple_support a b c

/-- **Nilpotency of the remainder of `U† ⊗ U† → U`** (data file §2.4): every word of length three in
the remainder vanishes, so the nilpotency order is at most three, the bound of Theorem 7.7(vi) is
attained. -/
theorem dd_evalWord_remainder_eq_zero (w : List (Fin 9)) (hw : 3 ≤ w.length) :
    Kraus.evalWord dd_compression.remainder w = 0 := by
  refine evalWord_eq_zero_of_triple_mul_eq_zero _ (fun a b c => ?_) w hw
  rw [dd_remainder_eq, dd_remainder_eq, dd_remainder_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, ddRemainder_triple, complexOfEisenstein_zero]

/-- The nilpotency order of the remainder of `U† ⊗ U† → U` is exactly three, as recorded in the data
file (§2.4): the product of the remainder letters `2` and `2` does not vanish. -/
theorem dd_remainder_mul_ne_zero :
    dd_compression.remainder 2 * dd_compression.remainder 2 ≠ 0 := by
  rw [dd_remainder_eq, ← complexOfEisenstein_mul]
  exact complexOfEisenstein_ne_zero (by decide)

/-- The selected sitewise intertwining equations of the right certificate of `U† ⊗ U† → U`. -/
def ddRightRows : Fin 8 → Fin 9 × Fin 4 × Fin 2 :=
  ![(2, 0, 0), (3, 0, 1), (7, 0, 0), (2, 0, 1), (2, 2, 1), (2, 3, 1), (3, 0, 0), (7, 0, 1)]

/-- The left inverse, up to the scalar `⟨-6, -3⟩`, of the coefficient matrix of the selected
equations of the right certificate of `U† ⊗ U† → U`. -/
def ddRightCert : Matrix (Fin 8) (Fin 8) EisensteinInt :=
  !![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩;
     ⟨0, 0⟩, ⟨-1, -2⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨-1, -2⟩;
     ⟨-6, -3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-6, -3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, 2⟩, ⟨1, -1⟩, ⟨-2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-2, -1⟩;
     ⟨0, 0⟩, ⟨-2, -4⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨4, 2⟩, ⟨-2, -1⟩, ⟨1, -1⟩;
     ⟨0, 0⟩, ⟨-6, -3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

private theorem ddRight_certificate :
    (Matrix.of fun rs j => ddRightCert (finProdFinEquiv (m := 4) (n := 2) rs) j) *
        (sitewiseEqMatrix ddStackEis uEisMPS).submatrix ddRightRows id =
      (⟨-6, -3⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero right sitewise intertwiner for `U† ⊗ U† → U`** (data file §2.4): the compression
exists at the level of words but not site by site. -/
theorem dd_right_intertwiner_eq_zero (X : Matrix (Fin 4) (Fin 2) ℂ)
    (hX : ∀ i, ddStack i * X = X * uMPS i) : X = 0 :=
  right_intertwiner_eq_zero_of_eisenstein ddStackEis ddStack_eq uEisMPS uMPS_eq
    ddRightRows _ (by decide) ddRight_certificate X hX

/-- The selected sitewise intertwining equations of the left certificate of `U† ⊗ U† → U`. -/
def ddLeftRows : Fin 8 → Fin 9 × Fin 4 × Fin 2 :=
  ![(2, 0, 0), (2, 2, 0), (2, 3, 0), (3, 0, 0), (3, 1, 0), (3, 2, 0), (7, 1, 0), (2, 1, 0)]

/-- The left inverse, up to the scalar `⟨-1, -1⟩`, of the coefficient matrix of the selected
equations of the left certificate of `U† ⊗ U† → U`. -/
def ddLeftCert : Matrix (Fin 8) (Fin 8) EisensteinInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

private theorem ddLeft_certificate :
    (Matrix.of fun rs j => ddLeftCert (finProdFinEquiv (m := 4) (n := 2) rs) j) *
        (sitewiseEqMatrix (fun i => (ddStackEis i)ᵀ)
          fun i => (uEisMPS i)ᵀ).submatrix ddLeftRows id =
      (⟨-1, -1⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero left sitewise intertwiner for `U† ⊗ U† → U`** (data file §2.4). -/
theorem dd_left_intertwiner_eq_zero (Y : Matrix (Fin 2) (Fin 4) ℂ)
    (hY : ∀ i, Y * ddStack i = uMPS i * Y) : Y = 0 :=
  left_intertwiner_eq_zero_of_eisenstein ddStackEis ddStack_eq uEisMPS uMPS_eq
    ddLeftRows _ (by decide) ddLeft_certificate Y hY

/-- **The fusion rule `U† ⊗ U† → U` as an identity of periodic operators** at every positive length
(data file §2.4). -/
theorem mpo_dd (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uDagTensor L * MPOTensor.mpo uDagTensor L = MPOTensor.mpo uTensor L :=
  MPOTensor.mpo_mul_eq_of_trace_evalWord uDagTensor uDagTensor uTensor dd_trace_evalWord L hL

end Z3Anomalous
