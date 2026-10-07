/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PeriodicFullRingString
import TNLean.MPS.Examples.AKLTPhysicalStringOrder
import TNLean.MPS.Examples.ClusterPhysicalStringOrder

/-!
# Exact periodic AKLT and cluster symmetry overlaps

The whole-ring overlaps in arXiv:0802.0447, Examples 1 and 2, are one whenever
there is a nonzero periodic vector. For the printed AKLT tensor the exact
squared norm is `1 + 3 (-1/3)^L`: the one-site vector vanishes, while length zero
and every length at least two are nonzero. Its normalized full-ring overlap
is therefore zero at length one and one at every other length.

The printed cluster tensor is nonzero at every length, and its full-ring
`(-σx)` overlap is always one. At positive lengths its squared norm is one,
by the existing controlled-`Z` construction on the ring. At length zero its
sole coefficient is the bond dimension two. The one-site and two-site rings
retain the conventions of that construction: their vectors are respectively
`|−⟩` and `|+⟩ ⊗ |+⟩`.

These are finite periodic expectations, rather than stationary-boundary
string correlators. The length-one AKLT exception is a zero-vector convention,
not an additional nonvanishing hypothesis.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  display `RL` and Examples 1–2, lines 380–411.
-/

open scoped Matrix BigOperators InnerProductSpace

noncomputable section

namespace MPSTensor

local notation "Mat₂" => Matrix (Fin 2) (Fin 2) ℂ

/-- The source's physical rephasing leaves the ordinary AKLT transfer map
unchanged. Source: arXiv:0802.0447, Example 1, lines 392–399. -/
private lemma akltPGWSVC08_transferMap_eq :
    Kraus.transferMap akltPGWSVC08Tensor = Kraus.transferMap akltTensor := by
  ext X : 1
  rw [← twistedTransferMap_one, ← twistedTransferMap_one]
  simpa using congrArg (fun E : Module.End ℂ Mat₂ => E X)
    (twistedTransferMap_akltPGWSVC08_diagonal (fun _ => 1))

/-- The transfer power is the sum of its scalar and traceless components,
with eigenvalues one and `(-1/3)^L`. Source: arXiv:0802.0447, Example 1,
lines 392–399; supporting finite-size calculation for `RL`. -/
theorem akltPGWSVC08_transferMap_pow (L : ℕ) (X : Mat₂) :
    (Kraus.transferMap akltPGWSVC08Tensor ^ L) X =
      (-1 / 3 : ℂ) ^ L • X +
        (1 - (-1 / 3 : ℂ) ^ L) • ((Matrix.trace X / 2) • (1 : Mat₂)) := by
  have hstep (Y : Mat₂) : Kraus.transferMap akltPGWSVC08Tensor Y =
      (-1 / 3 : ℂ) • Y + (2 / 3 : ℂ) • ((Matrix.trace Y) • (1 : Mat₂)) := by
    rw [akltPGWSVC08_transferMap_eq, ← twistedTransferMap_one]
    rw [show (1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal (fun _ => 1) by simp]
    rw [twistedTransferMap_aklt_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.trace, Fin.sum_univ_two] <;> ring
  induction L with
  | zero => simp
  | succ L ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul,
      map_smul, map_smul, akltPGWSVC08_canonical.1, hstep, pow_succ]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- The exact squared norm of the printed periodic AKLT vector is
`1 + 3 (-1/3)^L`. In particular, length one is the sole zero-vector exception.
Source: arXiv:0802.0447, `MPS` and Example 1, lines 392–399. -/
theorem akltPGWSVC08_mpvState_inner_self (L : ℕ) :
    ⟪mpvState akltPGWSVC08Tensor L, mpvState akltPGWSVC08Tensor L⟫_ℂ =
      1 + 3 * (-1 / 3 : ℂ) ^ L := by
  rw [inner_mpvState_self_eq_trace]
  have hp : Kraus.transferMap akltPGWSVC08Tensor ^ L =
      (-1 / 3 : ℂ) ^ L • (1 : Module.End ℂ Mat₂) +
        (1 - (-1 / 3 : ℂ) ^ L) •
          (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight ((1 / 2 : ℂ) • (1 : Mat₂)) := by
    ext X i j
    simp [akltPGWSVC08_transferMap_pow, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply, smul_smul, div_eq_mul_inv]
  rw [hp, map_add, map_smul, map_smul, LinearMap.trace_one,
    LinearMap.trace_smulRight]
  norm_num [Module.finrank_matrix, Matrix.traceLinearMap_apply,
    Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  ring

/-- The length-one periodic AKLT vector is zero because every physical
letter is traceless. Source: arXiv:0802.0447, Example 1, lines 394–395. -/
@[simp] theorem akltPGWSVC08_mpvState_one : mpvState akltPGWSVC08Tensor 1 = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [akltPGWSVC08_mpvState_inner_self]
  norm_num

/-- Every periodic AKLT length at least two is nonzero, as follows from its
exact norm; no nonvanishing assumption is supplied by the caller.
Source: arXiv:0802.0447, Example 1, lines 392–399. -/
private theorem akltPGWSVC08_mpvState_ne_zero_of_two_le {L : ℕ} (hL : 2 ≤ L) :
    mpvState akltPGWSVC08Tensor L ≠ 0 := by
  have hcorrection : ‖(3 : ℂ) * (-1 / 3 : ℂ) ^ L‖ ≤ 1 / 3 := by
    calc
      ‖(3 : ℂ) * (-1 / 3 : ℂ) ^ L‖ = 3 * (1 / 3 : ℝ) ^ L := by
        simp [norm_pow]
      _ ≤ 3 * (1 / 3 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hL)
          (by norm_num)
      _ = 1 / 3 := by norm_num
  intro hzero
  have hnorm := akltPGWSVC08_mpvState_inner_self L
  rw [hzero, inner_zero_left] at hnorm
  have hterm : (3 : ℂ) * (-1 / 3 : ℂ) ^ L = -1 := by linear_combination -hnorm
  rw [hterm] at hcorrection
  norm_num at hcorrection

/-- Exact admissible lengths for a nonzero periodic AKLT vector, including
length zero under the trace convention. Source: arXiv:0802.0447, `MPS` and
Example 1, lines 392–399. -/
theorem akltPGWSVC08_mpvState_ne_zero_iff (L : ℕ) :
    mpvState akltPGWSVC08Tensor L ≠ 0 ↔ L ≠ 1 := by
  constructor
  · rintro h rfl
    exact h akltPGWSVC08_mpvState_one
  · intro hL
    by_cases hzero : L = 0
    · subst L
      intro h
      have hnorm := akltPGWSVC08_mpvState_inner_self 0
      rw [h] at hnorm
      norm_num at hnorm
    · exact akltPGWSVC08_mpvState_ne_zero_of_two_le (by omega)

/-- The normalized AKLT whole-ring overlap is exactly one at every
nonvanishing length, with the length condition derived from the tensor.
Source: arXiv:0802.0447, Example 1, line 399. -/
private theorem akltPGWSVC08_fullRing_eq_one {L : ℕ} (hL : L ≠ 1) :
    mpvExpectation akltPGWSVC08Tensor L
      (Matrix.finKronecker fun _ : Fin L => akltSpinRotationZ) = 1 := by
  have hstar : (!![(1 : ℂ), 0; 0, -1] : Mat₂)ᴴ = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hunit : (!![(1 : ℂ), 0; 0, -1] : Mat₂) *
      (!![(1 : ℂ), 0; 0, -1] : Mat₂)ᴴ = 1 := by
    rw [hstar]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  simpa only [one_pow] using mpvExpectation_finKronecker_const_eq_phase_pow
    akltPGWSVC08Tensor akltSpinRotationZ !![1, 0; 0, -1] 1 hunit
    (fun i => by simpa only [one_smul, hstar] using akltPGWSVC08_sigmaZ_intertwine i)
    L ((akltPGWSVC08_mpvState_ne_zero_iff L).mpr hL)

/-- At the exceptional length one, zero normalization gives overlap zero.
At every other length the source's whole-ring value is exactly one.
Source: arXiv:0802.0447, Example 1, line 399, with its zero-vector case made explicit. -/
theorem akltPGWSVC08_fullRing (L : ℕ) :
    mpvExpectation akltPGWSVC08Tensor L
      (Matrix.finKronecker fun _ : Fin L => akltSpinRotationZ) =
        if L = 1 then 0 else 1 := by
  split_ifs with hL
  · subst L
    simp [mpvExpectation, akltPGWSVC08_mpvState_one]
  · exact akltPGWSVC08_fullRing_eq_one hL

/-- At every positive ring length the printed cluster vector has squared
norm one. The proof uses its existing controlled-`Z` construction, including
its short-ring conventions. Source: arXiv:0802.0447, Example 2, lines 401–411,
and arXiv:2011.12127, Appendix A, lines 2364–2369. -/
theorem clusterTensorRMP_mpvState_norm_sq {L : ℕ} (hL : 0 < L) :
    ‖mpvState clusterTensorRMP L‖ ^ 2 = 1 := by
  have hsqrt : ‖(↑(1 / Real.sqrt 2) : ℂ)‖ ^ 2 = 1 / 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg,
      Real.sqrt_nonneg, Real.sq_sqrt]
  have hcoeff (s : Fin L → Fin 2) : ‖mpv clusterTensorRMP s‖ ^ 2 = (1 / 2 : ℝ) ^ L := by
    rw [clusterTensorRMP_mpv_eq_clusterCZRing hL, clusterCZRing_apply, plusProductState]
    simp only [norm_mul, norm_prod, norm_pow, norm_neg, norm_one, one_pow,
      Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm L 2, pow_mul, hsqrt]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [mpvState_apply, hcoeff, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- The cluster vector is nonzero at every length: positive lengths are unit
vectors, and the empty ring has the sole coefficient two.
Source: arXiv:0802.0447, `MPS` and Example 2, lines 401–411. -/
theorem clusterTensorRMP_mpvState_ne_zero (L : ℕ) :
    mpvState clusterTensorRMP L ≠ 0 := by
  cases L with
  | zero =>
    intro h
    have heval := congrArg (fun v : MPVSpace 2 0 => v Fin.elim0) h
    norm_num [mpvState_apply] at heval
  | succ L =>
    intro h
    have hnorm := clusterTensorRMP_mpvState_norm_sq (Nat.succ_pos L)
    rw [h] at hnorm
    norm_num at hnorm

/-- The cluster whole-ring overlap with `(-σx)^{⊗L}` is exactly one at every
length, including the empty and short rings. Source: arXiv:0802.0447,
Example 2, lines 406–411. -/
theorem clusterTensorRMP_fullRing (L : ℕ) :
    mpvExpectation clusterTensorRMP L
      (Matrix.finKronecker fun _ : Fin L => -pauliX) = 1 := by
  have hunit : SpinCover.pauli 1 * (SpinCover.pauli 1)ᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [SpinCover.pauli, Matrix.mul_apply, Fin.sum_univ_two]
  have hInter (i : Fin 2) : ∑ j : Fin 2, (-pauliX) i j • clusterTensorRMP j =
      (1 : ℂ) • (SpinCover.pauli 1 * clusterTensorRMP i * (SpinCover.pauli 1)ᴴ) := by
    have hi := congrArg (fun M : Mat₂ => M * (SpinCover.pauli 1)ᴴ)
      (clusterTensorRMP_pauliY_intertwine i)
    simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one, one_smul] using hi
  simpa only [one_pow] using mpvExpectation_finKronecker_const_eq_phase_pow
    clusterTensorRMP (-pauliX) (SpinCover.pauli 1) 1 hunit hInter L
    (clusterTensorRMP_mpvState_ne_zero L)

end MPSTensor

end
