/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousFusion

/-!
# Anomalous `ℤ/3` example: the inverse fusion blocks `U ⊗ U†` and `U† ⊗ U`

**Source.** Construction of this development: no source prints the `ℤ/3` tensors of
`Z3AnomalousTensor.lean` or the compression data below. Garre-Rubio and Schuch
(arXiv:2405.00439), subsection "Example: `G = ℤ_n` with fully symmetry breaking",
`Papers/2405.00439/MPU-DW.tex` lines 2038–2040, print the cyclic `3`-cocycles
`ω_j(a, b, c) = exp(2πi j a (b + c - [b + c]) / n²)` of `ℤ/n`; the representative used here has
class `j = 1` for `n = 3`, a fact checked only in the verification script and not formalized.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563), subsubsection "Periodic boundary condition
case", `Papers/2203.12563/REsubmission.tex` lines 2202–2224, construct periodic matrix product
operator representations of a finite group with a `3`-cocycle and print the `ℤ/2` instance
`∏ CZ_{i,i+1} Z_i ∏ X_i` (line 2222); the phase-decorated shift used here is a `ℤ/3` operator of
the same kind, not the operator of that construction.

**Formalized here.** Instances of the multi-block asymmetric compression theorem of this
development (P5 note, `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`,
theorem `thm:p5-asymmetric-compression`, lines 495–569) for the stacked products `U ⊗ U†` and
`U† ⊗ U` of the representation `{1, U, U†}`, which fuse to the identity tensor `δ`. Each stacked
product of bond dimension four compresses onto the bond-one identity tensor with three zero
slots and a unimodular gauge over `ℤ[ω]`. The remainder is nilpotent of order exactly three, one
less than the bound `|S| + z = 4` of clause (vi) of that theorem, and both sitewise intertwiner
spaces vanish: even the fusion of a symmetry with its inverse to the identity exists only at the
level of words. As the data file notes (§0), this non-splitness of `U ⊗ U⁻¹ → δ` occurs for the
non-anomalous clock symmetry as well, so it is not by itself a signature of the anomaly.

Together with the blocks of `Z3AnomalousFusion.lean`, the compression data give the operator
identities of the representation at every positive length: `U U† = U† U = 1` and, with
`U U = U†`, the exact relation `U³ = 1`.

## Main definitions

* `Z3Anomalous.ud_compression`, `Z3Anomalous.du_compression`: the compression data of the two
  blocks.

## Main results

* `Z3Anomalous.ud_trace_evalWord`, `Z3Anomalous.du_trace_evalWord`: the word-trace form of the
  fusion rules `U U† = 1` and `U† U = 1`.
* `Z3Anomalous.ud_isReduction`, `Z3Anomalous.ud_left_eq`, `Z3Anomalous.ud_right_eq` and their
  `du` siblings: the explicit biorthogonal compression pairs.
* `Z3Anomalous.ud_evalWord_remainder_eq_zero`, `Z3Anomalous.ud_remainder_mul_ne_zero` and their
  `du` siblings: the remainders are nilpotent of order exactly three.
* `Z3Anomalous.ud_right_intertwiner_eq_zero`, `Z3Anomalous.ud_left_intertwiner_eq_zero` and
  their `du` siblings: no sitewise intertwiner in either direction.
* `Z3Anomalous.mpo_u_mul_uDag`, `Z3Anomalous.mpo_uDag_mul_u`, `Z3Anomalous.mpo_u_pow_three`:
  `U U† = U† U = 1` and `U³ = 1` as identities of periodic operators.

## References

- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*

## Provenance

The compression data and the exact-arithmetic certificates were first recorded in
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, §2.2 and §2.3, and checked over `ℤ[ω]`
by `Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`; they are verification records, not
the source.
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open EisensteinInt MPSTensor

/-! ### The flag shape of a one-dimensional target -/

/-- The bond dimension of a one-dimensional target. -/
abbrev scalarDim : Unit → ℕ := fun _ => 1

/-- The block ordering of the blocks with a one-dimensional target: two zero slots, the target,
a zero slot (data file §2.2 and §2.3). -/
def scalarOrd : BlockIndex singleSlot 3 ≃ Fin 4 where
  toFun
    | Sum.inl _ => 2
    | Sum.inr t => ![0, 1, 3] t
  invFun
    | 0 => Sum.inr 0
    | 1 => Sum.inr 1
    | 2 => Sum.inl theSlot
    | 3 => Sum.inr 2
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinate attached to a graded coordinate of a block with a one-dimensional
target. -/
def scalarCoordNat (x : BlockSpace scalarDim singleSlot 3) : ℕ :=
  Sum.elim (fun _ => 2) ![0, 1, 3] x.1 + (x.2 : ℕ)

theorem scalarCoordNat_lt (x : BlockSpace scalarDim singleSlot 3) : scalarCoordNat x < 4 := by
  revert x
  decide

/-- The labelling of the four bond coordinates of a block with a one-dimensional target by the
graded block space. -/
def scalarCoord : BlockSpace scalarDim singleSlot 3 ≃ Fin 4 where
  toFun x := ⟨scalarCoordNat x, scalarCoordNat_lt x⟩
  invFun
    | 0 => ⟨Sum.inr 0, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inr 1, ⟨0, by decide⟩⟩
    | 2 => ⟨Sum.inl theSlot, ⟨0, by decide⟩⟩
    | 3 => ⟨Sum.inr 2, ⟨0, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

/-! ### The block `U ⊗ U† → δ` (data file §2.2)

The stacked tensor of `U ⊗ U†` compresses onto `δ` with `z = 3` zero slots, in the flag order two
zero slots, the target, a zero slot. The remainder is nilpotent of order exactly three, and both
sitewise intertwiner spaces vanish.
-/

/-- The change of bond coordinates of the block `U ⊗ U† → δ` (data file §2.2); its inverse
`udGaugeInvEis` has the adapted basis as columns and unit determinant. -/
def udGaugeEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
     ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]

/-- The inverse change of bond coordinates of the block `U ⊗ U† → δ` (data file §2.2). -/
def udGaugeInvEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩;
     ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]

theorem udGauge_mul_inv : udGaugeEis * udGaugeInvEis = 1 := by decide +kernel

theorem udGaugeInv_mul : udGaugeInvEis * udGaugeEis = 1 := by decide +kernel

/-- The letters of the stacked tensor of `U ⊗ U†` in the block coordinates: block upper triangular,
with the letters of `δ` on the diagonal block of the target and zero on the zero slots (data file
§2.2). -/
def udConjEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem ud_conj_eq (i : Fin 9) :
    udGaugeEis * udStackEis i * udGaugeInvEis = udConjEis i := by
  revert i
  decide +kernel

/-- The single target of the block `U ⊗ U† → δ`. -/
def udTarget : (s : Unit) → MPSTensor 9 (scalarDim s) := fun _ => identityMPS

theorem udTarget_eq (s : Unit) (a : Fin 9) :
    udTarget s a = complexOfEisenstein (identityEisMPS a) :=
  identityMPS_eq a

private theorem ud_triangular (i : Fin 9) (x y : BlockSpace scalarDim singleSlot 3)
    (h : scalarOrd y.1 < scalarOrd x.1) :
    (udGaugeEis * udStackEis i * udGaugeInvEis) (scalarCoord x) (scalarCoord y) = 0 := by
  rw [ud_conj_eq]
  revert i x y h
  decide +kernel

private theorem ud_matched (i : Fin 9) :
    (Matrix.of fun p q : Fin 1 =>
      udConjEis i (scalarCoord ⟨Sum.inl theSlot, p⟩) (scalarCoord ⟨Sum.inl theSlot, q⟩)) =
      identityEisMPS i := by
  revert i
  decide +kernel

private theorem ud_unmatched (i : Fin 9) (t : Fin 3) :
    (Matrix.of fun p q : Fin 1 =>
      udConjEis i (scalarCoord ⟨Sum.inr t, p⟩) (scalarCoord ⟨Sum.inr t, q⟩)) = 0 := by
  revert i t
  decide +kernel

/-- **The multi-block asymmetric compression datum of the block `U ⊗ U† → δ`** (P5 note, Theorem
7.7, clauses (i)–(iii); data file §2.2): the stacked tensor of `U ⊗ U†` compresses onto `δ` with `3`
zero slots. -/
def ud_compression : MultiBlockCompression udStack singleSlot udTarget :=
  MultiBlockCompression.ofEisenstein udStackEis udStack_eq (fun _ => identityEisMPS)
    udTarget_eq 3 scalarOrd scalarCoord udGaugeEis udGaugeInvEis udGauge_mul_inv udGaugeInv_mul
    ud_triangular
    (fun i s p q => by
      rw [ud_conj_eq]
      obtain ⟨⟨⟩, _⟩ := s
      exact congrFun (congrFun (ud_matched i) p) q)
    (fun i t p q => by
      rw [ud_conj_eq]
      exact congrFun (congrFun (ud_unmatched i t) p) q)

/-- **The word-trace form of `U ⊗ U† → δ`** (data file §2.2): at every positive length the stacked
tensor of `U ⊗ U†` has the word traces of `δ`. -/
theorem ud_trace_evalWord (w : List (Fin 9)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord udStack w) =
      Matrix.trace (Kraus.evalWord identityMPS w) := by
  have h := ud_compression.trace_evalWord_eq_sum w hw
  rwa [Fintype.sum_unique] at h

/-- **Biorthogonal compression of `U ⊗ U† → δ`** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem ud_isReduction :
    IsReduction udStack identityMPS (ud_compression.left theSlot)
      (ud_compression.right theSlot) :=
  ud_compression.isReduction theSlot

/-- The compression pair of `U ⊗ U† → δ` is the recorded one (data file §2.2): `V` is the column
block of the inverse gauge carrying the target and `W` the row block of the gauge. -/
theorem ud_right_eq :
    ud_compression.right theSlot =
      complexOfEisenstein !![⟨1, 0⟩;
           ⟨0, 0⟩;
           ⟨0, 0⟩;
           ⟨1, 0⟩] := by
  rw [ud_compression.right_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one udGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one udGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

theorem ud_left_eq :
    ud_compression.left theSlot =
      complexOfEisenstein !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] := by
  rw [ud_compression.left_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one udGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one udGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

/-- **The dimension count of `U ⊗ U† → δ`**: `4 = 1 + 3` (P5 note, Theorem 7.7(vii)). -/
theorem ud_dim_eq : (4 : ℕ) = ∑ s ∈ singleSlot, scalarDim s + 3 :=
  ud_compression.dim_eq

/-- The remainder letters `R^i = B^i - V C^i W` of the block `U ⊗ U† → δ` (data file §2.2). -/
def udRemainderEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 =>
    !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem ud_remainder_eq (i : Fin 9) :
    ud_compression.remainder i = complexOfEisenstein (udRemainderEis i) := by
  rw [MultiBlockCompression.remainder,
    Finset.sum_eq_single_of_mem theSlot (Finset.mem_univ theSlot)
      fun b _ hb => absurd (Subtype.ext (Subsingleton.elim b.1 theSlot.1)) hb,
    ud_left_eq, ud_right_eq, udStack_eq, udTarget_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, ← complexOfEisenstein_sub]
  congr 1
  revert i
  decide +kernel

/-- The three letters carrying the nonzero remainder matrices of `U ⊗ U† → δ`. -/
def udRemainderSupport : Fin 3 → Fin 9 := ![0, 4, 8]

private theorem udRemainder_support (a : Fin 9) :
    udRemainderEis a = 0 ∨ ∃ j, udRemainderSupport j = a := by
  revert a
  decide +kernel

private theorem udRemainder_triple_support (i j l : Fin 3) :
    udRemainderEis (udRemainderSupport i) * udRemainderEis (udRemainderSupport j) *
      udRemainderEis (udRemainderSupport l) = 0 := by
  revert i j l
  decide +kernel

private theorem udRemainder_triple (a b c : Fin 9) :
    udRemainderEis a * udRemainderEis b * udRemainderEis c = 0 :=
  triple_mul_eq_zero_of_support _ udRemainderSupport udRemainder_support
    udRemainder_triple_support a b c

/-- **Nilpotency of the remainder of `U ⊗ U† → δ`** (data file §2.2): every word of length three in
the remainder vanishes, so the nilpotency order is at most three, one less than the bound `4` of
Theorem 7.7(vi). -/
theorem ud_evalWord_remainder_eq_zero (w : List (Fin 9)) (hw : 3 ≤ w.length) :
    Kraus.evalWord ud_compression.remainder w = 0 := by
  refine evalWord_eq_zero_of_triple_mul_eq_zero _ (fun a b c => ?_) w hw
  rw [ud_remainder_eq, ud_remainder_eq, ud_remainder_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, udRemainder_triple, complexOfEisenstein_zero]

/-- The nilpotency order of the remainder of `U ⊗ U† → δ` is exactly three, as recorded in the data
file (§2.2): the product of the remainder letters `0` and `4` does not vanish. -/
theorem ud_remainder_mul_ne_zero :
    ud_compression.remainder 0 * ud_compression.remainder 4 ≠ 0 := by
  rw [ud_remainder_eq, ud_remainder_eq, ← complexOfEisenstein_mul]
  exact complexOfEisenstein_ne_zero (by decide)

/-- The selected sitewise intertwining equations of the right certificate of `U ⊗ U† → δ`. -/
def udRightRows : Fin 4 → Fin 9 × Fin 4 × Fin 1 :=
  ![(0, 0, 0), (0, 1, 0), (0, 2, 0), (4, 1, 0)]

/-- The left inverse, up to the scalar `⟨-1, 1⟩`, of the coefficient matrix of the selected
equations of the right certificate of `U ⊗ U† → δ`. -/
def udRightCert : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩;
     ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩;
     ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩;
     ⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]

private theorem udRight_certificate :
    (Matrix.of fun rs j => udRightCert (finProdFinEquiv (m := 4) (n := 1) rs) j) *
        (sitewiseEqMatrix udStackEis identityEisMPS).submatrix udRightRows id =
      (⟨-1, 1⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero right sitewise intertwiner for `U ⊗ U† → δ`** (data file §2.2): the compression
exists at the level of words but not site by site. -/
theorem ud_right_intertwiner_eq_zero (X : Matrix (Fin 4) (Fin 1) ℂ)
    (hX : ∀ i, udStack i * X = X * identityMPS i) : X = 0 :=
  right_intertwiner_eq_zero_of_eisenstein udStackEis udStack_eq identityEisMPS identityMPS_eq
    udRightRows _ (by decide) udRight_certificate X hX

/-- The selected sitewise intertwining equations of the left certificate of `U ⊗ U† → δ`. -/
def udLeftRows : Fin 4 → Fin 9 × Fin 4 × Fin 1 :=
  ![(0, 0, 0), (0, 1, 0), (0, 2, 0), (4, 3, 0)]

/-- The left inverse, up to the scalar `⟨1, 0⟩`, of the coefficient matrix of the selected equations
of the left certificate of `U ⊗ U† → δ`. -/
def udLeftCert : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]

private theorem udLeft_certificate :
    (Matrix.of fun rs j => udLeftCert (finProdFinEquiv (m := 4) (n := 1) rs) j) *
        (sitewiseEqMatrix (fun i => (udStackEis i)ᵀ)
          fun i => (identityEisMPS i)ᵀ).submatrix udLeftRows id =
      (⟨1, 0⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero left sitewise intertwiner for `U ⊗ U† → δ`** (data file §2.2). -/
theorem ud_left_intertwiner_eq_zero (Y : Matrix (Fin 1) (Fin 4) ℂ)
    (hY : ∀ i, Y * udStack i = identityMPS i * Y) : Y = 0 :=
  left_intertwiner_eq_zero_of_eisenstein udStackEis udStack_eq identityEisMPS identityMPS_eq
    udLeftRows _ (by decide) udLeft_certificate Y hY

/-- **The fusion rule `U ⊗ U† → δ` as an identity of periodic operators** at every positive length
(data file §2.2). -/
theorem mpo_ud (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uTensor L * MPOTensor.mpo uDagTensor L = MPOTensor.mpo identityTensor L :=
  MPOTensor.mpo_mul_eq_of_trace_evalWord uTensor uDagTensor identityTensor ud_trace_evalWord L hL

/-! ### The block `U† ⊗ U → δ` (data file §2.3)

The stacked tensor of `U† ⊗ U` compresses onto `δ` with `z = 3` zero slots, in the flag order two
zero slots, the target, a zero slot. The remainder is nilpotent of order exactly three, and both
sitewise intertwiner spaces vanish.
-/

/-- The change of bond coordinates of the block `U† ⊗ U → δ` (data file §2.3); its inverse
`duGaugeInvEis` has the adapted basis as columns and unit determinant. -/
def duGaugeEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
     ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]

/-- The inverse change of bond coordinates of the block `U† ⊗ U → δ` (data file §2.3). -/
def duGaugeInvEis : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩;
     ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]

theorem duGauge_mul_inv : duGaugeEis * duGaugeInvEis = 1 := by decide +kernel

theorem duGaugeInv_mul : duGaugeInvEis * duGaugeEis = 1 := by decide +kernel

/-- The letters of the stacked tensor of `U† ⊗ U` in the block coordinates: block upper triangular,
with the letters of `δ` on the diagonal block of the target and zero on the zero slots (data file
§2.3). -/
def duConjEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem du_conj_eq (i : Fin 9) :
    duGaugeEis * duStackEis i * duGaugeInvEis = duConjEis i := by
  revert i
  decide +kernel

/-- The single target of the block `U† ⊗ U → δ`. -/
def duTarget : (s : Unit) → MPSTensor 9 (scalarDim s) := fun _ => identityMPS

theorem duTarget_eq (s : Unit) (a : Fin 9) :
    duTarget s a = complexOfEisenstein (identityEisMPS a) :=
  identityMPS_eq a

private theorem du_triangular (i : Fin 9) (x y : BlockSpace scalarDim singleSlot 3)
    (h : scalarOrd y.1 < scalarOrd x.1) :
    (duGaugeEis * duStackEis i * duGaugeInvEis) (scalarCoord x) (scalarCoord y) = 0 := by
  rw [du_conj_eq]
  revert i x y h
  decide +kernel

private theorem du_matched (i : Fin 9) :
    (Matrix.of fun p q : Fin 1 =>
      duConjEis i (scalarCoord ⟨Sum.inl theSlot, p⟩) (scalarCoord ⟨Sum.inl theSlot, q⟩)) =
      identityEisMPS i := by
  revert i
  decide +kernel

private theorem du_unmatched (i : Fin 9) (t : Fin 3) :
    (Matrix.of fun p q : Fin 1 =>
      duConjEis i (scalarCoord ⟨Sum.inr t, p⟩) (scalarCoord ⟨Sum.inr t, q⟩)) = 0 := by
  revert i t
  decide +kernel

/-- **The multi-block asymmetric compression datum of the block `U† ⊗ U → δ`** (P5 note, Theorem
7.7, clauses (i)–(iii); data file §2.3): the stacked tensor of `U† ⊗ U` compresses onto `δ` with `3`
zero slots. -/
def du_compression : MultiBlockCompression duStack singleSlot duTarget :=
  MultiBlockCompression.ofEisenstein duStackEis duStack_eq (fun _ => identityEisMPS)
    duTarget_eq 3 scalarOrd scalarCoord duGaugeEis duGaugeInvEis duGauge_mul_inv duGaugeInv_mul
    du_triangular
    (fun i s p q => by
      rw [du_conj_eq]
      obtain ⟨⟨⟩, _⟩ := s
      exact congrFun (congrFun (du_matched i) p) q)
    (fun i t p q => by
      rw [du_conj_eq]
      exact congrFun (congrFun (du_unmatched i t) p) q)

/-- **The word-trace form of `U† ⊗ U → δ`** (data file §2.3): at every positive length the stacked
tensor of `U† ⊗ U` has the word traces of `δ`. -/
theorem du_trace_evalWord (w : List (Fin 9)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord duStack w) =
      Matrix.trace (Kraus.evalWord identityMPS w) := by
  have h := du_compression.trace_evalWord_eq_sum w hw
  rwa [Fintype.sum_unique] at h

/-- **Biorthogonal compression of `U† ⊗ U → δ`** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem du_isReduction :
    IsReduction duStack identityMPS (du_compression.left theSlot)
      (du_compression.right theSlot) :=
  du_compression.isReduction theSlot

/-- The compression pair of `U† ⊗ U → δ` is the recorded one (data file §2.3): `V` is the column
block of the inverse gauge carrying the target and `W` the row block of the gauge. -/
theorem du_right_eq :
    du_compression.right theSlot =
      complexOfEisenstein !![⟨1, 0⟩;
           ⟨0, 0⟩;
           ⟨0, 0⟩;
           ⟨1, 0⟩] := by
  rw [du_compression.right_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one duGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one duGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

theorem du_left_eq :
    du_compression.left theSlot =
      complexOfEisenstein !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] := by
  rw [du_compression.left_gaugeOfMatrix (hG := complexOfEisenstein_mul_eq_one duGauge_mul_inv)
    (hG' := complexOfEisenstein_mul_eq_one duGaugeInv_mul) rfl, ← complexOfEisenstein_submatrix]
  congr 1
  decide +kernel

/-- **The dimension count of `U† ⊗ U → δ`**: `4 = 1 + 3` (P5 note, Theorem 7.7(vii)). -/
theorem du_dim_eq : (4 : ℕ) = ∑ s ∈ singleSlot, scalarDim s + 3 :=
  du_compression.dim_eq

/-- The remainder letters `R^i = B^i - V C^i W` of the block `U† ⊗ U → δ` (data file §2.3). -/
def duRemainderEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt
  | 0 =>
    !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem du_remainder_eq (i : Fin 9) :
    du_compression.remainder i = complexOfEisenstein (duRemainderEis i) := by
  rw [MultiBlockCompression.remainder,
    Finset.sum_eq_single_of_mem theSlot (Finset.mem_univ theSlot)
      fun b _ hb => absurd (Subtype.ext (Subsingleton.elim b.1 theSlot.1)) hb,
    du_left_eq, du_right_eq, duStack_eq, duTarget_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, ← complexOfEisenstein_sub]
  congr 1
  revert i
  decide +kernel

/-- The three letters carrying the nonzero remainder matrices of `U† ⊗ U → δ`. -/
def duRemainderSupport : Fin 3 → Fin 9 := ![0, 4, 8]

private theorem duRemainder_support (a : Fin 9) :
    duRemainderEis a = 0 ∨ ∃ j, duRemainderSupport j = a := by
  revert a
  decide +kernel

private theorem duRemainder_triple_support (i j l : Fin 3) :
    duRemainderEis (duRemainderSupport i) * duRemainderEis (duRemainderSupport j) *
      duRemainderEis (duRemainderSupport l) = 0 := by
  revert i j l
  decide +kernel

private theorem duRemainder_triple (a b c : Fin 9) :
    duRemainderEis a * duRemainderEis b * duRemainderEis c = 0 :=
  triple_mul_eq_zero_of_support _ duRemainderSupport duRemainder_support
    duRemainder_triple_support a b c

/-- **Nilpotency of the remainder of `U† ⊗ U → δ`** (data file §2.3): every word of length three in
the remainder vanishes, so the nilpotency order is at most three, one less than the bound `4` of
Theorem 7.7(vi). -/
theorem du_evalWord_remainder_eq_zero (w : List (Fin 9)) (hw : 3 ≤ w.length) :
    Kraus.evalWord du_compression.remainder w = 0 := by
  refine evalWord_eq_zero_of_triple_mul_eq_zero _ (fun a b c => ?_) w hw
  rw [du_remainder_eq, du_remainder_eq, du_remainder_eq, ← complexOfEisenstein_mul,
    ← complexOfEisenstein_mul, duRemainder_triple, complexOfEisenstein_zero]

/-- The nilpotency order of the remainder of `U† ⊗ U → δ` is exactly three, as recorded in the data
file (§2.3): the product of the remainder letters `0` and `0` does not vanish. -/
theorem du_remainder_mul_ne_zero :
    du_compression.remainder 0 * du_compression.remainder 0 ≠ 0 := by
  rw [du_remainder_eq, ← complexOfEisenstein_mul]
  exact complexOfEisenstein_ne_zero (by decide)

/-- The selected sitewise intertwining equations of the right certificate of `U† ⊗ U → δ`. -/
def duRightRows : Fin 4 → Fin 9 × Fin 4 × Fin 1 :=
  ![(0, 1, 0), (0, 2, 0), (0, 3, 0), (4, 1, 0)]

/-- The left inverse, up to the scalar `⟨-1, 1⟩`, of the coefficient matrix of the selected
equations of the right certificate of `U† ⊗ U → δ`. -/
def duRightCert : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩;
     ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩;
     ⟨-1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩;
     ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]

private theorem duRight_certificate :
    (Matrix.of fun rs j => duRightCert (finProdFinEquiv (m := 4) (n := 1) rs) j) *
        (sitewiseEqMatrix duStackEis identityEisMPS).submatrix duRightRows id =
      (⟨-1, 1⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero right sitewise intertwiner for `U† ⊗ U → δ`** (data file §2.3): the compression
exists at the level of words but not site by site. -/
theorem du_right_intertwiner_eq_zero (X : Matrix (Fin 4) (Fin 1) ℂ)
    (hX : ∀ i, duStack i * X = X * identityMPS i) : X = 0 :=
  right_intertwiner_eq_zero_of_eisenstein duStackEis duStack_eq identityEisMPS identityMPS_eq
    duRightRows _ (by decide) duRight_certificate X hX

/-- The selected sitewise intertwining equations of the left certificate of `U† ⊗ U → δ`. -/
def duLeftRows : Fin 4 → Fin 9 × Fin 4 × Fin 1 :=
  ![(0, 1, 0), (0, 2, 0), (0, 3, 0), (4, 0, 0)]

/-- The left inverse, up to the scalar `⟨-1, 0⟩`, of the coefficient matrix of the selected
equations of the left certificate of `U† ⊗ U → δ`. -/
def duLeftCert : Matrix (Fin 4) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
     ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]

private theorem duLeft_certificate :
    (Matrix.of fun rs j => duLeftCert (finProdFinEquiv (m := 4) (n := 1) rs) j) *
        (sitewiseEqMatrix (fun i => (duStackEis i)ᵀ)
          fun i => (identityEisMPS i)ᵀ).submatrix duLeftRows id =
      (⟨-1, 0⟩ : EisensteinInt) • 1 := by
  decide +kernel

/-- **No nonzero left sitewise intertwiner for `U† ⊗ U → δ`** (data file §2.3). -/
theorem du_left_intertwiner_eq_zero (Y : Matrix (Fin 1) (Fin 4) ℂ)
    (hY : ∀ i, Y * duStack i = identityMPS i * Y) : Y = 0 :=
  left_intertwiner_eq_zero_of_eisenstein duStackEis duStack_eq identityEisMPS identityMPS_eq
    duLeftRows _ (by decide) duLeft_certificate Y hY

/-- **The fusion rule `U† ⊗ U → δ` as an identity of periodic operators** at every positive length
(data file §2.3). -/
theorem mpo_du (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uDagTensor L * MPOTensor.mpo uTensor L = MPOTensor.mpo identityTensor L :=
  MPOTensor.mpo_mul_eq_of_trace_evalWord uDagTensor uTensor identityTensor du_trace_evalWord L hL

/-! ### The exact `ℤ/3` representation -/

/-- `U U† = 1` at every positive length: the fusion `U ⊗ U† → δ` together with the identity
operator of the identity tensor. -/
theorem mpo_u_mul_uDag (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uTensor L * MPOTensor.mpo uDagTensor L = 1 := by
  rw [mpo_ud L hL, mpo_identityTensor]

/-- `U† U = 1` at every positive length. -/
theorem mpo_uDag_mul_u (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uDagTensor L * MPOTensor.mpo uTensor L = 1 := by
  rw [mpo_du L hL, mpo_identityTensor]

/-- **`U³ = 1` exactly at every positive length** (data file §2.0): the symmetry generates an
exact representation of `ℤ/3`, without any length-dependent phase. -/
theorem mpo_u_pow_three (L : ℕ) (hL : 0 < L) : MPOTensor.mpo uTensor L ^ 3 = 1 := by
  rw [pow_succ, pow_two, mpo_uu L hL, mpo_uDag_mul_u L hL]

end Z3Anomalous
