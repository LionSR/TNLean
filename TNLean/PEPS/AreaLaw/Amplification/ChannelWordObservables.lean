/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SpectatorOscillationSupport
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelWeightedRow

/-!
# Observables evolved along finite words of physical channels

A list of event labels is read chronologically: appending a label applies its
actual spectator root channel to the current observable. Positive contraction
effects give uniform operator-norm and site-oscillation bounds. The summed
append increments are controlled by the existing graph-ball event kernel,
evaluated at that same evolved observable.

At the empty word, `siteOscillation_le_support_indicator` supplies the initial
support bound directly. No new word type, abstract recurrence, or Poisson
growth estimate is introduced here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–173, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

/-- The physical observable after the events in `w`, in chronological order,
with the identity on the spectator system. Source: area law,
`09-amplification.tex`, lines 161–173. -/
noncomputable def spectatorRootChannelWord
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ :=
  w.foldl (fun B i => spectatorRootChannel (k i) B) B

/-- Relabelling a chronological word evaluates exactly the same physical
channels in the same order. In particular, forgetting membership in a retained
family preserves the observable. Source: area law, `09-amplification.tex`,
lines 161–173. -/
theorem spectatorRootChannelWord_map {η : Type*} (f : η → κ)
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List η)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k (w.map f) B =
      spectatorRootChannelWord (k ∘ f) w B :=
  List.foldl_map

/-- The empty chronological word leaves the initial observable unchanged. -/
@[simp] theorem spectatorRootChannelWord_nil
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k [] B = B := rfl

/-- Appending an event applies its channel after all earlier events. -/
@[simp] theorem spectatorRootChannelWord_append_singleton
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List κ) (i : κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k (w ++ [i]) B =
      spectatorRootChannel (k i) (spectatorRootChannelWord k w B) := by
  simp only [spectatorRootChannelWord, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Every finite chronological composition is an operator-norm contraction,
uniformly in the word and spectator dimension. Source: area law,
`09-amplification.tex`, lines 161–173, using `03-quasilocal.tex`, lines 355–357. -/
theorem norm_spectatorRootChannelWord_le
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannelWord k w B‖ ≤ ‖B‖ := by
  induction w generalizing B with
  | nil => exact le_rfl
  | cons i w ih =>
    exact (ih (spectatorRootChannel (k i) B)).trans
      (norm_spectatorRootChannel_le (hk₀ i) (hk₁ i) B)

/-- The physical oscillations are nonnegative and uniformly bounded by twice
the initial operator norm, without Hermiticity. Source: area law,
`09-amplification.tex`, lines 127 and 161–173. -/
theorem siteOscillation_spectatorRootChannelWord_bounds
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    0 ≤ siteOscillation q y (spectatorRootChannelWord k w B) ∧
      siteOscillation q y (spectatorRootChannelWord k w B) ≤ 2 * ‖B‖ := by
  refine ⟨siteOscillation_nonneg y _, (siteOscillation_le_two_mul_norm y _).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (norm_spectatorRootChannelWord_le k hk₀ hk₁ w B)
    (by norm_num)

/-- The literal summed append increments of the actual evolved observable are
dominated by the graph-ball event kernel at that observable. Source: area law,
`09-amplification.tex`, lines 139–173. -/
theorem sum_siteOscillation_spectatorRootChannelWord_append_sub_le_graphChannelEventKernel
    [Fintype κ] [NeZero q]
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (N : ℕ) (hN : ∀ i, Finset.univ.sup (G.dist (a i)) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (w : List κ) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ i, (siteOscillation q y (spectatorRootChannelWord k (w ++ [i]) B) -
      siteOscillation q y (spectatorRootChannelWord k w B))) ≤
      ∑ z, graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z * siteOscillation q z (spectatorRootChannelWord k w B) := by
  simpa only [spectatorRootChannelWord_append_singleton] using
    sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
      G a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε y (spectatorRootChannelWord k w B)

end TNLean.PEPS.AreaLaw
