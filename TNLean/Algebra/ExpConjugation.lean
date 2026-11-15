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
import Mathlib.Algebra.Group.IsApply
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Conjugation by a matrix exponential

A factorial bound for iterated commutators gives
`‖exp(sH) * O * exp(-sH)‖ ≤ 2 * ‖O‖` for `0 ≤ s ≤ 1 / 8`.
The hypothesis is a bound on the actual commutator iterates; no locality or
Hermiticity assumption is imposed on the matrices.

This is the conditional exponential-series estimate used in Arad, Kuwahara
and Landau, arXiv:1406.3898, Lemma `lem:Hadamard-bound`, `low70.tex`,
lines 795–837. The factorial bound must be established separately from
locality. A version with an arbitrary growth constant `κ`, valid for
`0 ≤ s ≤ 1 / (2κ)`, serves interactions of bounded support and degree.
A positive contraction has commutator norm at most the norm of the other factor.
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


open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive contraction has commutator norm at most the norm of the other
factor. Auxiliary to AKL14, arXiv:1406.3898, low70.tex, lines 831–837.
The other factor need not be Hermitian, and the index type may be empty. -/
theorem norm_commutator_le_of_nonneg_le_one (h O : Matrix n n ℂ)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) : ‖h * O - O * h‖ ≤ ‖O‖ := by
  let c : Matrix n n ℂ := (1 / 2 : ℝ) • 1
  have hsplit : (1 : Matrix n n ℂ) = c + c := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hlo : -c ≤ h - c := by
    simpa only [zero_sub] using sub_le_sub_right h0 c
  have hhi : h - c ≤ c := by
    apply (sub_le_iff_le_add).2
    rw [← hsplit]
    exact h1
  have hcself : IsSelfAdjoint c :=
    IsSelfAdjoint.smul (IsSelfAdjoint.all (1 / 2 : ℝ)) (IsSelfAdjoint.one (Matrix n n ℂ))
  have hcenterself : IsSelfAdjoint (h - c) := (IsSelfAdjoint.of_nonneg h0).sub hcself
  have hnorm1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one (Matrix n n ℂ))
  have hcnorm : ‖c‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖c‖ = (1 / 2 : ℝ) * ‖(1 : Matrix n n ℂ)‖ := by
        dsimp [c]
        rw [norm_smul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left hnorm1 (by norm_num)
      _ = 1 / 2 := by ring
  have hcenternorm0 : ‖h - c‖ ≤ ‖c‖ := by
    simpa only [norm_neg, max_self] using
      (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hcenterself)
  have hcenternorm : ‖h - c‖ ≤ (1 / 2 : ℝ) := hcenternorm0.trans hcnorm
  have hcomm : h * O - O * h = (h - c) * O - O * (h - c) := by
    dsimp [c]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  calc
    ‖h * O - O * h‖ = ‖(h - c) * O - O * (h - c)‖ := congrArg (‖·‖) hcomm
    _ ≤ ‖(h - c) * O‖ + ‖O * (h - c)‖ := norm_sub_le _ _
    _ ≤ ‖h - c‖ * ‖O‖ + ‖O‖ * ‖h - c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (1 / 2 : ℝ) * ‖O‖ + ‖O‖ * (1 / 2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right hcenternorm (norm_nonneg O))
        (mul_le_mul_of_nonneg_left hcenternorm (norm_nonneg O))
    _ = ‖O‖ := by ring


omit [DecidableEq n] in
/-- Rescaling the generator rescales every commutator iterate by the same power.
Auxiliary to AKL14, arXiv:1406.3898, low70.tex, lines 795–837. -/
private theorem commutator_iterate_smul (H O : Matrix n n ℂ) (c : ℂ) (m : ℕ) :
    (fun X : Matrix n n ℂ ↦ (c • H) * X - X * (c • H))^[m] O =
      c ^ m • (fun X : Matrix n n ℂ ↦ H * X - X * H)^[m] O := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, pow_succ]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
    ring_nf

/-- A factorial bound with growth constant `κ` for the actual commutator
iterates implies the short-time conjugation bound for `0 ≤ s ≤ 1 / (2κ)`.
This is the conditional estimate of AKL14, arXiv:1406.3898, low70.tex,
lines 795–837, with the constant left free; the factorial hypothesis is
proved from locality in its application. -/
theorem norm_exp_conjugation_le_two_of_growth (H O : Matrix n n ℂ) (κ s : ℝ)
    (hκ : 0 < κ) (hs0 : 0 ≤ s) (hs : 2 * κ * s ≤ 1)
    (hgrowth : ∀ m : ℕ,
      ‖((fun X : Matrix n n ℂ ↦ H * X - X * H)^[m] O)‖ ≤
        κ ^ m * (m.factorial : ℝ) * ‖O‖) :
    ‖NormedSpace.exp ((s : ℂ) • H) * O *
      NormedSpace.exp (-((s : ℂ) • H))‖ ≤ 2 * ‖O‖ := by
  let c : ℝ := 4 / κ
  have hc : 0 < c := by positivity
  have hscale : ((s * κ / 4 : ℝ) : ℂ) • ((c : ℂ) • H) = (s : ℂ) • H := by
    have hk : (s * κ / 4) * c = s := by
      simp only [c]
      field_simp
    rw [smul_smul, ← Complex.ofReal_mul, hk]
  have h := norm_exp_conjugation_le_two ((c : ℂ) • H) O (s * κ / 4) (by positivity)
    (by linarith) (by
      intro m
      rw [commutator_iterate_smul, norm_smul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hc.le]
      calc
        c ^ m * ‖(fun X : Matrix n n ℂ ↦ H * X - X * H)^[m] O‖ ≤
            c ^ m * (κ ^ m * (m.factorial : ℝ) * ‖O‖) :=
          mul_le_mul_of_nonneg_left (hgrowth m) (by positivity)
        _ = (c * κ) ^ m * (m.factorial : ℝ) * ‖O‖ := by ring
        _ = (4 : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖ := by
          rw [show c * κ = 4 by simp only [c]; field_simp])
  rwa [hscale] at h

end Matrix
