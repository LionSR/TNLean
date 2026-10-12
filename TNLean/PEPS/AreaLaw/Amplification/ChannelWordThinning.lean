/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Probability.PoissonWordPartition
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables

/-!
# Retained physical channels in a full Poisson word

Filtering a full word preserves the order and multiplicity of retained events.
Its actual spectator root-channel composition equals the composition indexed
by the retained subtype word. The fixed-time marginal law therefore transfers
Bochner integrability and expectations of this physical observable between
the full and retained alphabets.

All physical matrices use the Euclidean operator norm. The transport applies
to arbitrary functions of the evolved matrix, including the matrix itself
and its site oscillations; countability of the word space supplies strong
measurability. No continuous-time clock process is constructed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 161–188, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory
open scoped NNReal Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

/-- Keeping precisely the retained letters in their original order evaluates
the same physical channels as the selected subtype word, with all repeated
labels preserved. Source: area law, `09-amplification.tex`, lines 161–173. -/
theorem spectatorRootChannelWord_filter
    (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : PoissonWord.Word κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B =
      spectatorRootChannelWord (fun i : {i // P i} => k i)
        (List.ofFn (PoissonWord.partitionWords P w).1.2) B := by
  rw [← PoissonWord.ofFn_partitionWords_fst P w, spectatorRootChannelWord_map]
  rfl

variable [Fintype κ]

/-- Integrability of an observation of the filtered physical evolution under
the full word law is equivalent to integrability under the retained word law.
Source: area law, `09-amplification.tex`, lines 161–188. -/
theorem integrable_spectatorRootChannelWord_filter_iff
    {E : Type*} [NormedAddCommGroup E]
    (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (F : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ → E) (t : ℝ≥0) :
    Integrable (fun w : PoissonWord.Word κ =>
        F (spectatorRootChannelWord k
          ((List.ofFn w.2).filter (fun i => decide (P i))) B))
      (PoissonWord.measure κ t) ↔
      Integrable (fun u : PoissonWord.Word {i // P i} =>
        F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
        (PoissonWord.measure {i // P i} t) := by
  simp_rw [spectatorRootChannelWord_filter]
  rw [← PoissonWord.map_partitionWords_fst P t]
  exact (integrable_map_measure
    (f := fun w : PoissonWord.Word κ => (PoissonWord.partitionWords P w).1)
    (g := fun u : PoissonWord.Word {i // P i} =>
      F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
    (μ := PoissonWord.measure κ t) AEStronglyMeasurable.of_discrete
    Measurable.of_discrete.aemeasurable).symm

/-- The expectation of an observation of the actual filtered physical word
equals its retained-alphabet expectation. This is a fixed-time change of law,
valid also for matrix-valued observations in the Euclidean operator norm.
Source: area law, `09-amplification.tex`, lines 161–188. -/
theorem integral_spectatorRootChannelWord_filter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (F : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ → E) (t : ℝ≥0) :
    (∫ w : PoissonWord.Word κ, F (spectatorRootChannelWord k
        ((List.ofFn w.2).filter (fun i => decide (P i))) B) ∂PoissonWord.measure κ t) =
      ∫ u : PoissonWord.Word {i // P i},
        F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B)
          ∂PoissonWord.measure {i // P i} t := by
  simp_rw [spectatorRootChannelWord_filter]
  rw [← PoissonWord.map_partitionWords_fst P t]
  exact (integral_map_of_stronglyMeasurable
    (φ := fun w : PoissonWord.Word κ => (PoissonWord.partitionWords P w).1)
    (f := fun u : PoissonWord.Word {i // P i} =>
      F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
    (μ := PoissonWord.measure κ t)
    Measurable.of_discrete StronglyMeasurable.of_discrete).symm

/-- A retained-law site-oscillation estimate applies to filtering the actual
full-word sample with exactly the same bound. Source: area law,
`09-amplification.tex`, lines 174–188. -/
theorem integrable_and_integral_siteOscillation_filter_le
    (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (t : ℝ≥0) (y : ι) (R : ℝ)
    (h : Integrable (fun u : PoissonWord.Word {i // P i} =>
        siteOscillation q y
          (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
        (PoissonWord.measure {i // P i} t) ∧
      (∫ u : PoissonWord.Word {i // P i}, siteOscillation q y
        (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B)
          ∂PoissonWord.measure {i // P i} t) ≤ R) :
    Integrable (fun w : PoissonWord.Word κ => siteOscillation q y
        (spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B))
      (PoissonWord.measure κ t) ∧
      (∫ w : PoissonWord.Word κ, siteOscillation q y
        (spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B)
          ∂PoissonWord.measure κ t) ≤ R := by
  rw [integrable_spectatorRootChannelWord_filter_iff P k B (siteOscillation q y),
    integral_spectatorRootChannelWord_filter P k B (siteOscillation q y)]
  exact h

end TNLean.PEPS.AreaLaw
