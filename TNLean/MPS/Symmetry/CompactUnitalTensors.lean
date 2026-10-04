/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Channel.Schwarz.Basic
import QICLean.Channel.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Compactness of unital tensors and stationary densities

In fixed physical and bond dimensions, each entry of a unital tensor has
modulus at most one. Unitality is a closed condition, so these tensors form
a compact set. Pairing this set with the compact set of density matrices
gives a common convergent subsequence of tensors and stationary densities.
Stationarity passes to the limit by continuity. The limiting density is
allowed to have smaller rank.

These are finite-dimensional compactness results for the exact MPS families
of arXiv:1010.3732, Section II.F.2 and Appendix C, lines 2653–2717. They do not
identify the limiting stationary support with a prescribed minimal tensor.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

private theorem norm_entry_le_one_of_isUnital {d D : ℕ}
    (A : MPSTensor d D) (hA : Kraus.IsUnital A) (i : Fin d) (a b : Fin D) :
    ‖A i a b‖ ≤ 1 := by
  have hdiag := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => (M a a).re) hA
  have hsum : ∑ j : Fin d, ∑ c : Fin D, ‖A j a c‖ ^ 2 = 1 := by
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_sum, Complex.mul_re, Complex.norm_mul_self_eq_normSq,
      Complex.normSq_apply, pow_two] using hdiag
  have hle : ‖A i a b‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    apply (Finset.single_le_sum (fun c _ => sq_nonneg ‖A i a c‖)
      (Finset.mem_univ b)).trans
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg
      (fun c _ => sq_nonneg ‖A j a c‖)) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i a b)]

/-- In fixed physical and bond dimensions the unital tensors form a compact
set, irrespective of injectivity or the rank of a stationary density. -/
theorem MPSTensor.isCompact_setOf_isUnital (d D : ℕ) :
    IsCompact {A : MPSTensor d D | Kraus.IsUnital A} := by
  have hclosed : IsClosed {A : MPSTensor d D | Kraus.IsUnital A} := by
    apply isClosed_eq ?_ continuous_const
    fun_prop
  have hcompact : IsCompact {A : MPSTensor d D |
      ∀ i a b, A i a b ∈ Metric.closedBall (0 : ℂ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite
      (fun _ => isCompact_pi_infinite (fun _ => isCompact_closedBall 0 1)))
  apply hcompact.of_isClosed_subset hclosed
  intro A hA i a b
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_entry_le_one_of_isUnital A hA i a b

/-- Unital tensors and stationary density matrices admit a common convergent
subsequence in fixed dimensions. The limiting density may have smaller rank. -/
theorem MPSTensor.exists_subsequence_unital_stationary_limit {d D : ℕ}
    (A : ℕ → MPSTensor d D) (σ : ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ n, Kraus.IsUnital (A n))
    (hσ : ∀ n, σ n ∈ densityMatrices D)
    (hfixed : ∀ n, Kraus.adjointMap (A n) (σ n) = σ n) :
    ∃ B : MPSTensor d D, ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.IsUnital B ∧ τ ∈ densityMatrices D ∧ Kraus.adjointMap B τ = τ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (A ∘ φ) Filter.atTop (nhds B) ∧
        Filter.Tendsto (σ ∘ φ) Filter.atTop (nhds τ) := by
  let : FirstCountableTopology (Fin D → ℂ) := inferInstance
  let : FirstCountableTopology (Matrix (Fin D) (Fin D) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin D → Fin D → ℂ))
  let : FirstCountableTopology (MPSTensor d D) :=
    inferInstanceAs (FirstCountableTopology (Fin d → Matrix (Fin D) (Fin D) ℂ))
  obtain ⟨p, hp, φ, hφ, hconv⟩ :=
    ((MPSTensor.isCompact_setOf_isUnital d D).prod
      (densityMatrices_isCompact (D := D))).tendsto_subseq
        (fun n => show (A n, σ n) ∈
          {B : MPSTensor d D | Kraus.IsUnital B} ×ˢ densityMatrices D from ⟨hA n, hσ n⟩)
  have hadj : Continuous (fun p : MPSTensor d D × Matrix (Fin D) (Fin D) ℂ =>
      Kraus.adjointMap p.1 p.2) := by
    unfold Kraus.adjointMap
    fun_prop
  have hAc : Filter.Tendsto (A ∘ φ) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hconv
  have hσc : Filter.Tendsto (σ ∘ φ) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hconv
  refine ⟨p.1, p.2, hp.1, hp.2, ?_, φ, hφ, hAc, hσc⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hadj.tendsto p).comp hconv) hσc
    (Filter.Eventually.of_forall (fun n => hfixed (φ n)))
