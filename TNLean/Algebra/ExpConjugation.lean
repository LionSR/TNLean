/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Data.FunLike.IsApply
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Conjugation by a matrix exponential

A factorial bound for iterated commutators gives
`‖exp(sH) * O * exp(-sH)‖ ≤ 2 * ‖O‖` for `0 ≤ s ≤ 1 / 8`.
The hypothesis is a bound on the actual commutator iterates; no locality or
Hermiticity assumption is imposed on the matrices.

This is the conditional exponential-series estimate used in Arad, Kuwahara
and Landau, arXiv:1406.3898, Lemma `lem:Hadamard-bound`, `low70.tex`,
lines 795–837. The factorial bound must be established separately in a
nearest-neighbour application.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponentiating left multiplication gives left multiplication by the
exponential. Supporting the Hadamard identity of AKL14, arXiv:1406.3898,
low70.tex, lines 795–810. -/
private theorem exp_left_multiplication_apply (H O : Matrix n n ℂ) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H) O =
      NormedSpace.exp H * O := by
  let L : Matrix n n ℂ →+* (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    { toFun := ContinuousLinearMap.mul ℂ (Matrix n n ℂ)
      map_zero' := ContinuousLinearMap.ext fun X ↦ zero_mul X
      map_one' := ContinuousLinearMap.ext fun X ↦ one_mul X
      map_add' := fun X Y ↦ ContinuousLinearMap.ext fun Z ↦ add_mul X Y Z
      map_mul' := fun X Y ↦ ContinuousLinearMap.ext fun Z ↦ mul_assoc X Y Z }
  have hL : Continuous L := (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).continuous
  have hx : H ∈ Metric.eball (0 : Matrix n n ℂ)
      (NormedSpace.expSeries ℂ (Matrix n n ℂ)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) L hL H hx
  exact (congrArg (fun f : Matrix n n ℂ →L[ℂ] Matrix n n ℂ ↦ f O) h).symm

/-- The opposite regular representation gives the corresponding right
multiplication identity. Supporting AKL14, arXiv:1406.3898, lines 795–810. -/
private theorem exp_right_multiplication_apply (H O : Matrix n n ℂ) :
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) O =
      O * NormedSpace.exp H := by
  let R : (Matrix n n ℂ)ᵐᵒᵖ →+* (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    { toFun := fun a ↦ (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip a.unop
      map_zero' := ContinuousLinearMap.ext fun X ↦ mul_zero X
      map_one' := ContinuousLinearMap.ext fun X ↦ mul_one X
      map_add' := fun X Y ↦ ContinuousLinearMap.ext fun Z ↦ mul_add Z X.unop Y.unop
      map_mul' := by
        intro X Y
        apply ContinuousLinearMap.ext
        intro Z
        change Z * (Y.unop * X.unop) = (Z * Y.unop) * X.unop
        exact (mul_assoc Z Y.unop X.unop).symm }
  have hR : Continuous R :=
    (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip.continuous.comp
      MulOpposite.continuous_unop
  have hx : MulOpposite.op H ∈ Metric.eball (0 : (Matrix n n ℂ)ᵐᵒᵖ)
      (NormedSpace.expSeries ℂ ((Matrix n n ℂ)ᵐᵒᵖ)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) R hR (MulOpposite.op H) hx
  have hO := congrArg (fun f : Matrix n n ℂ →L[ℂ] Matrix n n ℂ ↦ f O) h
  change O * (NormedSpace.exp (MulOpposite.op H)).unop =
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) O at hO
  simpa only [NormedSpace.exp_op, MulOpposite.unop_op,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hO.symm

end Matrix

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Left and right multiplication commute, so the exponential of their
commutator splits into two regular exponentials. This is the algebraic step in
AKL14, arXiv:1406.3898, low70.tex, lines 795–810. -/
private theorem exp_commutator_operator (H : Matrix n n ℂ) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H -
      (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) =
    NormedSpace.exp (ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H) *
      NormedSpace.exp (-((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H)) := by
  let L := ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H
  let R := (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H
  have hcomm : Commute L R := by
    apply ContinuousLinearMap.ext
    intro X
    change H * (X * H) = (H * X) * H
    exact (mul_assoc H X H).symm
  have hball (T : Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :
      T ∈ Metric.eball (0 : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
        (NormedSpace.expSeries ℂ (Matrix n n ℂ →L[ℂ] Matrix n n ℂ)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  simpa only [sub_eq_add_neg] using
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      hcomm.neg_right (hball L) (hball (-R))

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exponential of the commutator acts by conjugation. This is the
algebraic Hadamard identity underlying AKL14, arXiv:1406.3898,
low70.tex, lines 795–810; no locality estimate is asserted here. -/
private theorem exp_commutator_apply (H O : Matrix n n ℂ) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H -
      (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) O =
      NormedSpace.exp H * O * NormedSpace.exp (-H) := by
  have hneg : -((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) =
      (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip (-H) :=
    (map_neg (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H).symm
  rw [exp_commutator_operator H, hneg, mul_apply_eq_comp,
    exp_right_multiplication_apply, exp_left_multiplication_apply, mul_assoc]

end Matrix

namespace ContinuousLinearMap

/-- Evaluate the complex operator exponential series at an arbitrary vector.
Supporting AKL14, arXiv:1406.3898, low70.tex, lines 804–811. -/
private theorem hasSum_exp_smul_apply_iterate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (s : ℂ) (O : E) :
    HasSum (fun m : ℕ ↦ (s ^ m / (m.factorial : ℂ)) • ((T : E → E)^[m] O))
      ((NormedSpace.exp (s • T)) O) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • T)).mapL
    (ContinuousLinearMap.apply ℂ E O)
  simpa only [ContinuousLinearMap.apply_apply, smul_pow, smul_apply,
    pow_apply_eq_iterate, smul_smul, div_eq_mul_inv, mul_comm] using h

end ContinuousLinearMap

open scoped BigOperators

namespace NormedSpace

/-- A factorial growth estimate gives a geometric majorant for the scaled
series. Supporting the Hadamard-series argument of AKL14, arXiv:1406.3898,
low70.tex, lines 795–810. The growth bound is supplied independently;
no algebra, locality or positive-dimension premise is imposed here. -/
private theorem summable_factorial_smul_and_norm_tsum_le_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (v : ℕ → E) (C s : ℝ) (hC : 0 ≤ C) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8)
    (hv : ∀ m, ‖v m‖ ≤ (4 : ℝ) ^ m * (m.factorial : ℝ) * C) :
    Summable (fun m : ℕ ↦ ((s : ℂ) ^ m / (m.factorial : ℂ)) • v m) ∧
      ‖∑' m : ℕ, ((s : ℂ) ^ m / (m.factorial : ℂ)) • v m‖ ≤ 2 * C := by
  have hscale : 4 * s ≤ (1 / 2 : ℝ) := by linarith
  have hbound (m : ℕ) :
      ‖((s : ℂ) ^ m / (m.factorial : ℂ)) • v m‖ ≤ (1 / 2 : ℝ) ^ m * C := by
    have hfac : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    calc
      ‖((s : ℂ) ^ m / (m.factorial : ℂ)) • v m‖ =
          (s ^ m / (m.factorial : ℝ)) * ‖v m‖ := by
        rw [norm_smul, norm_div, norm_pow, Complex.norm_of_nonneg hs0,
          Complex.norm_natCast]
      _ ≤ (s ^ m / (m.factorial : ℝ)) *
          ((4 : ℝ) ^ m * (m.factorial : ℝ) * C) :=
        mul_le_mul_of_nonneg_left (hv m) (div_nonneg (pow_nonneg hs0 _) hfac.le)
      _ = ((s ^ m / (m.factorial : ℝ)) * (m.factorial : ℝ)) *
          ((4 : ℝ) ^ m * C) := by ring
      _ = (4 * s) ^ m * C := by
        rw [div_mul_cancel₀ _ hfac.ne', mul_pow]
        ring
      _ ≤ (1 / 2 : ℝ) ^ m * C :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (by norm_num) hs0) hscale m) hC
  have hgeom : HasSum (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m * C) (2 * C) :=
    hasSum_geometric_two.mul_right C
  exact ⟨hgeom.summable.of_norm_bounded hbound, tsum_of_norm_bounded hgeom hbound⟩

end NormedSpace

namespace ContinuousLinearMap

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- Scalar multiplication of the commutator map is scalar multiplication
of its generator. Auxiliary to AKL14, arXiv:1406.3898, lines 804–837. -/
private theorem smul_mul_sub_flip (A : R) (s : ℂ) :
    s • (mul ℂ R A - (mul ℂ R).flip A) =
      mul ℂ R (s • A) - (mul ℂ R).flip (s • A) := by
  apply ContinuousLinearMap.ext
  intro O
  change s • (A * O - O * A) = (s • A) * O - O * (s • A)
  rw [smul_sub, smul_mul_assoc, mul_smul_comm]

end ContinuousLinearMap

namespace Matrix

open scoped Matrix.Norms.L2Operator

/-- A factorial bound for the actual commutator iterates implies the
short-time conjugation bound. This is an auxiliary conditional estimate
supporting AKL14, arXiv:1406.3898, low70.tex, lines 804–837.
The factorial hypothesis is to be proved from locality in its application. -/
theorem norm_exp_conjugation_le_two {n : Type*} [Fintype n] [DecidableEq n]
    (H O : Matrix n n ℂ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8)
    (hgrowth : ∀ m : ℕ,
      ‖((fun X : Matrix n n ℂ ↦ H * X - X * H)^[m] O)‖ ≤
        (4 : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖) :
    ‖NormedSpace.exp ((s : ℂ) • H) * O *
      NormedSpace.exp (-((s : ℂ) • H))‖ ≤ 2 * ‖O‖ := by
  let ad : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
    ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H -
      (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H
  have hsum := ContinuousLinearMap.hasSum_exp_smul_apply_iterate ad (s : ℂ) O
  obtain ⟨_hsummable, hbound⟩ :=
    NormedSpace.summable_factorial_smul_and_norm_tsum_le_two
      (fun m : ℕ ↦ ((ad : Matrix n n ℂ → Matrix n n ℂ)^[m] O))
      ‖O‖ s (norm_nonneg O) hs0 hs (by exact hgrowth)
  rw [hsum.tsum_eq] at hbound
  have had : (s : ℂ) • ad =
      ContinuousLinearMap.mul ℂ (Matrix n n ℂ) ((s : ℂ) • H) -
        (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip ((s : ℂ) • H) :=
    ContinuousLinearMap.smul_mul_sub_flip H (s : ℂ)
  rw [had, exp_commutator_apply] at hbound
  exact hbound

end Matrix
