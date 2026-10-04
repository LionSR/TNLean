/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.Core.TracePairing

/-!
# Finite-ring trace data and the bond matrix algebra

For one-site injective tensors, nonzero proportionality of two-site periodic
trace data identifies the kernel of the physical coefficient map and the
minimal bond dimension. Three-site trace data then identify multiplication,
up to the ratio of the trace normalization constants.

The trace pairing is complex bilinear; it is not a positive Hermitian form.
These finite-data results are auxiliary to the extraction of tensor data in
arXiv:1010.3732, Section II.F.2, lines 953–993. Continuous canonical coordinates
through a changing quotient dimension remain a separate problem, recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators

namespace MPSTensor

/-- The two-site trace form is the composition of the tensor coefficient
map with trace pairing. This gives a physical description of the minimal
coefficient quotient. Auxiliary context: arXiv:1010.3732, Section II.F.2,
lines 953–993. -/
theorem traceGram_eq_smul_of_twoSite_trace_eq
    {d D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E) (c : ℂ)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c * Matrix.trace (A i * A j)) :
    (traceMulRightPi B).comp (Fintype.linearCombination ℂ B) =
      c • (traceMulRightPi A).comp (Fintype.linearCombination ℂ A) := by
  ext x j
  simp [Fintype.linearCombination_apply, hpair]

/-- The nonzero two-site ground ray determines the kernel of the minimal
one-site coefficient map. Different injective bond realizations therefore
have the same physical quotient, even before their dimensions are compared.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem ker_linearCombination_eq_of_twoSite_trace_eq
    {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (c : ℂ) (hc : c ≠ 0)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c * Matrix.trace (A i * A j)) :
    (Fintype.linearCombination ℂ B).ker = (Fintype.linearCombination ℂ A).ker := by
  rw [← LinearMap.ker_comp_of_ker_eq_bot (Fintype.linearCombination ℂ B)
    (traceMulRightPi_ker_eq_bot hB), traceGram_eq_smul_of_twoSite_trace_eq A B c hpair,
    LinearMap.ker_smul _ c hc,
    LinearMap.ker_comp_of_ker_eq_bot _ (traceMulRightPi_ker_eq_bot hA)]

/-- Two-site trace data extend the assignment of injective tensor letters
uniquely to a linear map between their full bond matrix spaces. The scalar
may be zero in this purely linear statement. Auxiliary context:
arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem linearExtension_exists_unique_of_twoSite_trace_eq
    {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B) (c : ℂ)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c * Matrix.trace (A i * A j)) :
    ∃! T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin E) (Fin E) ℂ,
      ∀ i, T (A i) = B i := by
  obtain ⟨g, hg⟩ := (traceMulRightPi B).exists_leftInverse_of_injective
    (traceMulRightPi_ker_eq_bot hB)
  let T := g.comp (c • traceMulRightPi A)
  have hT : ∀ i, T (A i) = B i := by
    intro i
    have hΦ : traceMulRightPi B (B i) = c • traceMulRightPi A (A i) := by
      funext j
      simpa only [traceMulRightPi_apply, Pi.smul_apply, smul_eq_mul] using hpair i j
    change g (c • traceMulRightPi A (A i)) = B i
    rw [← hΦ]
    simpa only [LinearMap.comp_apply, LinearMap.id_apply]
      using congrArg (fun f => f (B i)) hg
  exact ⟨T, hT, fun T' hT' =>
    LinearMap.ext_on_range (hv := hA.span_eq_top) fun i => by rw [hT' i, hT i]⟩

/-- Three-site trace data recover multiplication on the coefficient quotient,
up to the ratio of the two trace normalization constants. Zero-dimensional
matrix spaces are allowed. The three-site normalization is nonzero.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem linearExtension_mul_of_two_three_trace_eq
    {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c₂ * Matrix.trace (A i * A j))
    (htriple : ∀ i j k, Matrix.trace (B i * B j * B k) =
      c₃ * Matrix.trace (A i * A j * A k))
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin E) (Fin E) ℂ)
    (hT : ∀ i, T (A i) = B i) :
    ∀ M N, T (M * N) = (c₂ / c₃) • (T M * T N) := by
  have hΦComp : (traceMulRightPi B).comp T = c₂ • traceMulRightPi A :=
    LinearMap.ext_on_range (hv := hA.span_eq_top) fun i => by
      ext j
      simpa only [LinearMap.comp_apply, hT i, LinearMap.smul_apply,
        Pi.smul_apply, traceMulRightPi_apply, smul_eq_mul] using hpair i j
  have hMul_gen : ∀ i j, T (A i * A j) = (c₂ / c₃) • (B i * B j) := by
    intro i j
    apply (LinearMap.ker_eq_bot.mp (traceMulRightPi_ker_eq_bot hB))
    funext k
    have hleft := congrFun (congrArg (fun f => f (A i * A j)) hΦComp) k
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply,
      traceMulRightPi_apply, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      htriple, ← mul_assoc, div_mul_cancel₀ _ hc₃] using hleft
  have hfg :
      (LinearMap.mul ℂ (Matrix (Fin D) (Fin D) ℂ)).compr₂ T =
        (c₂ / c₃) • (LinearMap.mul ℂ (Matrix (Fin E) (Fin E) ℂ)).compl₁₂ T T :=
    LinearMap.ext_on_range (hv := hA.span_eq_top) fun i =>
      LinearMap.ext_on_range (hv := hA.span_eq_top) fun j => by
        simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
          LinearMap.mul_apply', LinearMap.smul_apply, hT i, hT j] using hMul_gen i j
  intro M N
  simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', LinearMap.smul_apply] using congrArg (fun f => f M N) hfg

/-- The two-site ray also determines the minimal injective bond dimension.
Zero-dimensional tensors cause no exception. Auxiliary context:
arXiv:1010.3732, Section II.F.2, lines 1059–1068. -/
theorem bondDimension_eq_of_twoSite_trace_eq
    {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (c : ℂ) (hc : c ≠ 0)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c * Matrix.trace (A i * A j)) :
    D = E := by
  have hker := ker_linearCombination_eq_of_twoSite_trace_eq hA hB c hc hpair
  have hRA := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination ℂ A)
  have hRB := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination ℂ B)
  rw [LinearMap.range_eq_top.mpr hA.linearCombination_surjective, finrank_top] at hRA
  rw [LinearMap.range_eq_top.mpr hB.linearCombination_surjective, finrank_top, hker] at hRB
  have hdim := Nat.add_right_cancel (hRA.trans hRB.symm)
  have hsq : D * D = E * E := by simpa [Module.finrank_matrix] using hdim
  nlinarith

end MPSTensor
