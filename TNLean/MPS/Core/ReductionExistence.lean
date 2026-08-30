/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RankOneFactorization
import TNLean.Algebra.SemisimpleTracePowers
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Core.Reduction
import TNLean.MPS.Core.ReductionCrossMatrix
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Equality-case rectangular reductions

This file proves the equality specialization of Proposition 20 of
Molnár--Ge--Schuch--Cirac.  The target tensor is first made injective by a
positive physical blocking.  Its coefficient-dual inverse and the source
tensor define the mixed-bond cross matrix on `Fin D_B × Fin D_A`.
Jordan--Chevalley decomposition separates this cross endomorphism into
commuting nilpotent and semisimple parts.  The source trace-power identities
force the semisimple part to have rank one; its rectangular factorization is
then inserted into the source's padded open-boundary contraction.  Cancellation
of the nonzero target-bond scalar gives the word identity at the original
physical scale, including the empty word.

No same-bond Fundamental Theorem, block-normal form, left-canonical gauge, or
trace-preserving normalization enters the argument.

Source: arXiv:1706.07329v2, Proposition 20, `cornerproblem.tex` lines
3815--3938.

**Scope restriction (equality-only local fix):** The results assume
`SameMPV₂Pos`, and hence prove the `λ = 1` specialization of the proportional
premise printed in Proposition 20.  The unscaled conclusion is false for
unrestricted `λ ≠ 1`; see
`docs/paper-gaps/mgsc18_reduction_proportionality_scalar.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D_A D_B : ℕ}

/-- Source-faithful assembly after choosing a positive blocking at which the
target is injective.  The arbitrary unblocked tail in the open contraction is
what returns the final relation to the original physical scale.

Source: arXiv:1706.07329v2, proof of Proposition 20,
`cornerproblem.tex` lines 3815--3938. -/
private theorem exists_isReduction_of_blockTensor_isInjective_of_sameMPV₂Pos
    [NeZero D_A] (A : MPSTensor d D_A) (B : MPSTensor d D_B)
    (hSame : SameMPV₂Pos B A) (p : ℕ) (hp : 0 < p)
    (hA : Kraus.IsInjective (blockTensor (d := d) (D := D_A) A p)) :
    ∃ (V : Matrix (Fin D_A) (Fin D_B) ℂ)
      (W : Matrix (Fin D_B) (Fin D_A) ℂ), IsReduction B A V W := by
  classical
  let Aₚ := blockTensor (d := d) (D := D_A) A p
  let Bₚ := blockTensor (d := d) (D := D_B) B p
  let C := coefficientDualInverse Aₚ hA
  let K := reductionCrossMatrix Bₚ C
  let f : Module.End ℂ (Fin D_B × Fin D_A → ℂ) := Matrix.toLin' K
  obtain ⟨N, hNmem, S, hSmem, hNnil, hSsemi, hf⟩ :=
    f.exists_isNilpotent_isSemisimple
  have hfN : Commute f N := Algebra.commute_of_mem_adjoin_self hNmem
  have hNS : Commute N S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hSmem hfN.symm
  have hSameBlock : SameMPV₂Pos Bₚ Aₚ := by
    exact sameMPV₂Pos_blockTensor B A hSame p hp
  have hTraceS (k : ℕ) (hk : 0 < k) :
      LinearMap.trace ℂ _ (S ^ k) = (D_A : ℂ) ^ k := by
    calc
      LinearMap.trace ℂ _ (S ^ k) = LinearMap.trace ℂ _ ((N + S) ^ k) :=
        (Module.End.IsNilpotent.trace_add_pow_eq_trace_pow_of_commute
          hNnil S hNS k).symm
      _ = LinearMap.trace ℂ _ (f ^ k) := by rw [hf]
      _ = Matrix.trace (K ^ k) := by
        rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow]
      _ = (D_A : ℂ) ^ k := by
        exact trace_reductionCrossMatrix_pow_of_sameMPV₂Pos Aₚ Bₚ hA hSameBlock k hk
  have hDA : (D_A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D_A)
  have hScaledTrace : ∀ k : ℕ, 1 < k →
      LinearMap.trace ℂ _ (((D_A : ℂ)⁻¹ • S) ^ k) = 1 := by
    intro k hk
    rw [smul_pow, map_smul, hTraceS k (by omega)]
    change (D_A : ℂ)⁻¹ ^ k * (D_A : ℂ) ^ k = 1
    rw [← mul_pow]
    simp [hDA]
  have hInv : (D_A : ℂ)⁻¹ ≠ 0 := inv_ne_zero hDA
  have hSrank : Module.finrank ℂ S.range = 1 :=
    Module.End.finrank_range_eq_one_of_isSemisimple_of_scaled_trace_pow_eq_one
      S hSsemi (D_A : ℂ)⁻¹ hInv hScaledTrace
  obtain ⟨hNSzero, hSNzero⟩ :=
    Module.End.IsNilpotent.mul_eq_zero_and_mul_eq_zero_of_commute_of_finrank_range_eq_one
      hNnil S hNS hSrank
  obtain ⟨J, hJ, hEventual⟩ :=
    Module.End.IsNilpotent.exists_add_pow_eq_right_of_mul_eq_zero
      hNnil S hNSzero hSNzero
  have hfPow : f ^ J = S ^ J := by
    rw [hf]
    exact hEventual J le_rfl
  let SM : Matrix (Fin D_B × Fin D_A) (Fin D_B × Fin D_A) ℂ :=
    LinearMap.toMatrix' S
  have hSMrank : SM.rank = 1 := by
    change (LinearMap.toMatrix' S).rank = 1
    calc
      (LinearMap.toMatrix' S).rank =
          Module.finrank ℂ (LinearMap.range (Matrix.toLin'
            (LinearMap.toMatrix' S))) := by
        rw [← Matrix.toLin_eq_toLin']
        exact (LinearMap.toMatrix' S).rank_eq_finrank_range_toLin
          (Pi.basisFun ℂ (Fin D_B × Fin D_A))
          (Pi.basisFun ℂ (Fin D_B × Fin D_A))
      _ = Module.finrank ℂ S.range := by rw [Matrix.toLin'_toMatrix']
      _ = 1 := hSrank
  obtain ⟨W, V, _hW, _hV, hSMouter, hSMentry⟩ :=
    Matrix.exists_rectangular_factors_of_rank_eq_one SM hSMrank
  have hTraceSM : Matrix.trace SM = (D_A : ℂ) := by
    change Matrix.trace (LinearMap.toMatrix' S) = (D_A : ℂ)
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    simpa using hTraceS 1 (by omega)
  have hdot :
      (fun q : Fin D_B × Fin D_A => V q.2 q.1) ⬝ᵥ
        (fun q : Fin D_B × Fin D_A => W q.1 q.2) = (D_A : ℂ) := by
    rw [dotProduct_comm, ← Matrix.trace_vecMulVec, ← hSMouter]
    exact hTraceSM
  have hSMpow (n : ℕ) (hn : 0 < n) :
      SM ^ n = ((D_A : ℂ) ^ (n - 1)) • SM := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih (Nat.zero_lt_succ k), Matrix.smul_mul,
          hSMouter, Matrix.vecMulVec_mul_vecMulVec, hdot]
        ext q r
        simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
        rw [Nat.succ_sub (Nat.zero_lt_succ k), pow_succ]
        ring
  have hKpow : K ^ J = SM ^ J := by
    calc
      K ^ J = LinearMap.toMatrix' ((K ^ J).toLin') :=
        (LinearMap.toMatrix'_toLin' (K ^ J)).symm
      _ = LinearMap.toMatrix' (f ^ J) := by
        simp only [f, Matrix.toLin'_pow]
      _ = LinearMap.toMatrix' (S ^ J) := by rw [hfPow]
      _ = SM ^ J := by
        change LinearMap.toMatrix' (S ^ J) = (LinearMap.toMatrix' S) ^ J
        exact (LinearMap.toMatrix_pow (Pi.basisFun ℂ (Fin D_B × Fin D_A)) S J).symm
  have hCrossSum (X : Matrix (Fin D_B) (Fin D_B) ℂ) (a' a : Fin D_A) :
      (∑ x : Fin D_B, ∑ y : Fin D_B, (W x a * V a' y) * X y x) =
        (V * X * W) a' a := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  refine ⟨V, W, IsReduction.iff_forall_evalWord.mpr ?_⟩
  intro w
  ext a' a
  have hopen :=
    reductionOpenBoundaryMatrixContraction_blockTensor_of_sameMPV₂Pos
      A B hSame p hp hA J hJ w a' a
  rw [reductionOpenBoundaryMatrixContraction_eq_cross_sum] at hopen
  have hleft :
      (∑ x : Fin D_B, ∑ y : Fin D_B,
        (K ^ J) (x, a) (y, a') * Kraus.evalWord B w y x) =
        (D_A : ℂ) ^ (J - 1) * (V * Kraus.evalWord B w * W) a' a := by
    rw [hKpow, hSMpow J hJ]
    simp only [Matrix.smul_apply, hSMentry, smul_eq_mul]
    calc
      (∑ x : Fin D_B, ∑ y : Fin D_B,
          (D_A : ℂ) ^ (J - 1) * (W x a * V a' y) * Kraus.evalWord B w y x) =
          (D_A : ℂ) ^ (J - 1) *
            (∑ x : Fin D_B, ∑ y : Fin D_B,
              (W x a * V a' y) * Kraus.evalWord B w y x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = _ := by rw [hCrossSum (Kraus.evalWord B w) a' a]
  rw [hleft] at hopen
  exact mul_left_cancel₀ (pow_ne_zero _ hDA) hopen

/-- An injective target with the same positive-length matrix product vectors as
a possibly larger-bond source admits a rectangular reduction from the source.

This is the injective-target specialization of arXiv:1706.07329v2,
Proposition 20; see `cornerproblem.tex` lines 3815--3938. -/
theorem exists_isReduction_of_isInjective_of_sameMPV₂Pos [NeZero D_A]
    (A : MPSTensor d D_A) (B : MPSTensor d D_B)
    (hA : Kraus.IsInjective A) (hSame : SameMPV₂Pos B A) :
    ∃ (V : Matrix (Fin D_A) (Fin D_B) ℂ)
      (W : Matrix (Fin D_B) (Fin D_A) ℂ), IsReduction B A V W := by
  apply exists_isReduction_of_blockTensor_isInjective_of_sameMPV₂Pos A B hSame 1 (by omega)
  exact (isNBlkInjective_iff_blockTensor_isInjective A 1).mp
    (Kraus.isNBlkInjective_one_of_isInjective hA)

/-- A normal target with the same positive-length matrix product vectors as a
possibly larger-bond source admits a rectangular reduction from the source.
Normality is used only to choose a positive injective blocking; the padded open
contraction then proves the relation for every original-scale word.

This is the equality case of arXiv:1706.07329v2, Proposition 20,
`cornerproblem.tex` lines 3815--3938. -/
theorem exists_isReduction_of_isNormal_of_sameMPV₂Pos [NeZero D_A]
    (A : MPSTensor d D_A) (B : MPSTensor d D_B)
    (hA : Kraus.IsNormal A) (hSame : SameMPV₂Pos B A) :
    ∃ (V : Matrix (Fin D_A) (Fin D_B) ℂ)
      (W : Matrix (Fin D_B) (Fin D_A) ℂ), IsReduction B A V W := by
  obtain ⟨p, hp, hAp⟩ := hA
  apply exists_isReduction_of_blockTensor_isInjective_of_sameMPV₂Pos A B hSame p hp
  exact (isNBlkInjective_iff_blockTensor_isInjective A p).mp hAp

end MPSTensor
