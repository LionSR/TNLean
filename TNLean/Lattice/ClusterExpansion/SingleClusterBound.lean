/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceCFC
import QICLean.Analysis.TraceMulBound
import QICLean.Analysis.WeylMonotonicity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The single-cluster bound of Hastings' cluster expansion

Let `H` be a Hermitian matrix with partition function `Z = Tr e^{-βH}`, and let `V` be a
Hermitian perturbation. For every operator `O` and every `β ≥ 0`,
`Z⁻¹ |Tr(O e^{-β(H - V)})| ≤ ‖O‖ e^{β‖V‖}`, where `‖·‖` is the operator norm. When `V` is a sum
of `|T|` Hermitian terms of norm at most `J`, the right side is at most `‖O‖ e^{|T| J β}`. With
`T` the terms supported on a cluster `C` and on its boundary `B(C)`, this is equation `ddb` of
Hastings, *Solving gapped Hamiltonians locally*, Section IV, lines 1141–1175 of the source.

The source proves the bound by a Dyson expansion of `e^{-β(H - V)}` in imaginary-time evolved
operators. Here the inequality is proved instead from three facts.

* `|Tr(O A)| ≤ ‖O‖ Tr A` for positive semidefinite `A`.
* The map `X ↦ Tr e^X` is monotone in the Loewner order on Hermitian matrices, because Weyl
  monotonicity compares the ordered eigenvalues term by term.
* `V ≤ ‖V‖ 1`, so `-β(H - V) ≤ -βH + β‖V‖ 1` and `Tr e^{-β(H - V)} ≤ e^{β‖V‖} Tr e^{-βH}`.

## Main results

* `Matrix.IsHermitian.re_trace_exp_le`: monotonicity of `X ↦ Tr e^X`.
* `Matrix.IsHermitian.re_trace_exp_add_le`: `Tr e^{X + V} ≤ e^{‖V‖} Tr e^X`.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_le`: the bound for one perturbation.
* `TNLean.Lattice.ClusterExpansion.inv_mul_norm_trace_mul_exp_sub_sum_le`: equation `ddb`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73, 085115 (2006),
  arXiv:cond-mat/0508554v3, Section IV, equation `ddb`, lines 1141–1175.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of the exponential of a Hermitian matrix is the sum of the exponentials of its
eigenvalues. -/
theorem IsHermitian.re_trace_exp_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp A).trace.re = ∑ i, Real.exp (hA.eigenvalues i) := by
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hA.cfc_eq]
  exact hA.trace_cfc_eq_sum_re Real.exp

/-- **Monotonicity of the trace of the exponential.** If `A ≤ B` are Hermitian, then
`Tr e^A ≤ Tr e^B`. The ordered eigenvalues of `A` are bounded term by term by those of `B`. -/
theorem IsHermitian.re_trace_exp_le {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) :
    (NormedSpace.exp A).trace.re ≤ (NormedSpace.exp B).trace.re := by
  rw [hA.re_trace_exp_eq_sum, hB.re_trace_exp_eq_sum]
  exact Finset.sum_le_sum fun i _ ↦ Real.exp_le_exp.mpr (hA.eigenvalues_mono hB hAB i)

/-- Adding a real multiple of the identity in the exponent multiplies the exponential by a
scalar: `e^{A + c 1} = e^c e^A`. -/
theorem exp_add_smul_one (A : Matrix ι ι ℂ) (c : ℝ) :
    NormedSpace.exp (A + c • (1 : Matrix ι ι ℂ)) = Real.exp c • NormedSpace.exp A := by
  rw [← Algebra.algebraMap_eq_smul_one, Matrix.exp_add_of_commute _ _ (Algebra.commutes c A).symm,
    ← NormedSpace.algebraMap_exp_comm, Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul, Matrix.mul_one]

/-- A Hermitian perturbation `V` raises the trace of the exponential by at most `e^{‖V‖}`:
`Tr e^{X + V} ≤ e^{‖V‖} Tr e^X`, with `‖V‖` the operator norm. -/
theorem IsHermitian.re_trace_exp_add_le {X V : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (hV : V.IsHermitian) :
    (NormedSpace.exp (X + V)).trace.re ≤ Real.exp ‖V‖ * (NormedSpace.exp X).trace.re := by
  have hVle : V ≤ ‖V‖ • (1 : Matrix ι ι ℂ) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hV.isSelfAdjoint.le_algebraMap_norm_self
  have hc : (‖V‖ • (1 : Matrix ι ι ℂ)).IsHermitian := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      (IsSelfAdjoint.algebraMap (Matrix ι ι ℂ) (IsSelfAdjoint.all ‖V‖)).isHermitian
  calc (NormedSpace.exp (X + V)).trace.re
      ≤ (NormedSpace.exp (X + ‖V‖ • (1 : Matrix ι ι ℂ))).trace.re :=
        (hX.add hV).re_trace_exp_le (hX.add hc) (add_le_add_right hVle X)
    _ = Real.exp ‖V‖ * (NormedSpace.exp X).trace.re := by
        rw [exp_add_smul_one, trace_smul, Complex.real_smul, Complex.re_ofReal_mul]

end Matrix

namespace TNLean.Lattice.ClusterExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Bound for one perturbation.** For Hermitian `H` and `V`, every operator `O` and `β ≥ 0`,
`|Tr(O e^{-β(H - V)})| ≤ ‖O‖ e^{β‖V‖} Tr e^{-βH}`, with `‖·‖` the operator norm. This is the
estimate behind Hastings, *Solving gapped Hamiltonians locally*, equation `ddb`
(arXiv:cond-mat/0508554v3, lines 1141–1175), proved by the monotonicity of `X ↦ Tr e^X`
rather than by the source's Dyson expansion. -/
theorem norm_trace_mul_exp_sub_le {H V : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hV : V.IsHermitian) (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) :
    ‖(O * NormedSpace.exp (-(β • (H - V)))).trace‖ ≤
      ‖O‖ * Real.exp (β * ‖V‖) * (NormedSpace.exp (-(β • H))).trace.re := by
  have hX : (-(β • H)).IsHermitian := (hH.smul (IsSelfAdjoint.all β)).neg
  have hβV : (β • V).IsHermitian := hV.smul (IsSelfAdjoint.all β)
  have hsum : -(β • (H - V)) = -(β • H) + β • V := by
    rw [smul_sub]; abel
  have hpsd : (NormedSpace.exp (-(β • (H - V)))).PosSemidef := by
    rw [hsum]
    exact Matrix.nonneg_iff_posSemidef.mp (hX.add hβV).isSelfAdjoint.exp_nonneg
  have hnorm : ‖β • V‖ = β * ‖V‖ := by
    rw [norm_smul, Real.norm_of_nonneg hβ]
  calc ‖(O * NormedSpace.exp (-(β • (H - V)))).trace‖
      = ‖(NormedSpace.exp (-(β • (H - V))) * O).trace‖ := by rw [Matrix.trace_mul_comm]
    _ ≤ (NormedSpace.exp (-(β • (H - V)))).trace.re * ‖O‖ := hpsd.norm_trace_mul_le O
    _ ≤ (Real.exp (β * ‖V‖) * (NormedSpace.exp (-(β • H))).trace.re) * ‖O‖ := by
        gcongr
        rw [hsum, ← hnorm]
        exact hX.re_trace_exp_add_le hβV
    _ = ‖O‖ * Real.exp (β * ‖V‖) * (NormedSpace.exp (-(β • H))).trace.re := by ring

/-- **The single-cluster bound (Hastings, equation `ddb`).** Let `H` be Hermitian with
`Z = Tr e^{-βH}`, and let `h k`, for `k` in a finite set `T`, be Hermitian terms of operator norm
at most `J`. For every operator `O` and `β ≥ 0`,
`Z⁻¹ |Tr(O e^{-β(H - ∑_{k ∈ T} h_k)})| ≤ ‖O‖ e^{|T| J β}`.
With `T` the terms supported on a cluster `C` and its boundary `B(C)`, so that
`|T| = n_C + n_{B(C)}`, this is equation `ddb` of *Solving gapped Hamiltonians locally*
(arXiv:cond-mat/0508554v3, lines 1141–1175). The proof replaces the source's Dyson expansion by
the monotonicity of `X ↦ Tr e^X`. -/
theorem inv_mul_norm_trace_mul_exp_sub_sum_le {κ : Type*} {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (h : κ → Matrix ι ι ℂ) (T : Finset κ)
    (hh : ∀ k ∈ T, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k ∈ T, ‖h k‖ ≤ J)
    (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) :
    ((NormedSpace.exp (-(β • H))).trace.re)⁻¹ *
        ‖(O * NormedSpace.exp (-(β • (H - ∑ k ∈ T, h k)))).trace‖ ≤
      ‖O‖ * Real.exp (T.card * J * β) := by
  set Z := (NormedSpace.exp (-(β • H))).trace.re with hZdef
  have hV : (∑ k ∈ T, h k).IsHermitian :=
    (isSelfAdjoint_sum T fun k hk ↦ (hh k hk).isSelfAdjoint).isHermitian
  have hZ : 0 ≤ Z := by
    rw [hZdef, (hH.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_eq_sum]
    exact Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le
  have hVn : β * ‖∑ k ∈ T, h k‖ ≤ T.card * J * β := by
    have : ‖∑ k ∈ T, h k‖ ≤ T.card * J := by
      refine (norm_sum_le _ _).trans ?_
      simpa using Finset.sum_le_card_nsmul T (fun k ↦ ‖h k‖) J hJ
    nlinarith
  rcases hZ.eq_or_lt with hZ0 | hZpos
  · rw [← hZ0, inv_zero, zero_mul]
    positivity
  rw [inv_mul_le_iff₀ hZpos]
  calc ‖(O * NormedSpace.exp (-(β • (H - ∑ k ∈ T, h k)))).trace‖
      ≤ ‖O‖ * Real.exp (β * ‖∑ k ∈ T, h k‖) * Z := norm_trace_mul_exp_sub_le hH hV O hβ
    _ ≤ ‖O‖ * Real.exp (T.card * J * β) * Z := by gcongr
    _ = Z * (‖O‖ * Real.exp (T.card * J * β)) := by ring

end TNLean.Lattice.ClusterExpansion
