/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Probability.PoissonWord.Partition
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.ChannelWordObservables
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.LatticeChannelPoissonGrowth
import QICLean.ManyBody.Hamiltonian.GroundSpace

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

## Spatial growth after filtering a full lattice Poisson word

The expected spatial oscillation bound for retained lattice channels also
holds when the sample is a full-alphabet Poisson word and the omitted events
are deleted. Filtering preserves the chronological order of all retained
events. Its fixed-time marginal law is the retained Poisson-word law, so both
integrability and the expected bound transfer with the same constants.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 161–188, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

section

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

end

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open ManyBody (IsGapped groundSpace AdmissibleSupport planeDomainGraph PlaneInteraction)

namespace TNLean.PEPS.AreaLaw

/-- Filtering the actual full Poisson sample gives the same uniform spatial
bound as sampling the retained alphabet. The effects are still constructed
from the original Hamiltonian. Constants precede the domain, local dimension,
retained predicate, spectator and supported initial matrix. This is a
fixed-time word-law statement. Source: area law, `09-amplification.tex`,
lines 161–188. -/
theorem exists_latticeChannelWord_filter_spatial_growth {p : ℕ} (hp : 1 ≤ p)
    (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c v : ℝ, 0 < c ∧ 0 ≤ v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R)
          (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (a : AdmissibleSupport Λ R → ↥Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (P : AdmissibleSupport Λ R → Prop) [DecidablePred P]
          (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset ↥Λ)
          (B : Matrix ((↥Λ → Fin q) × Aux) ((↥Λ → Fin q) × Aux) ℂ),
        (∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
          ManyBody.supportedOperators (fun _ ↦ Fin q) S) →
        ∀ (t : ℝ≥0) (y : ↥Λ),
        letI := ManyBody.graphPseudoEMetricSpace (planeDomainGraph Λ)
        let α := kernelExponent p
        let k := fun i : AdmissibleSupport Λ R =>
          positiveConstraint (positiveNormalization p (Δ / 2) J)
            (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))
        Integrable (fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
            siteOscillation q y (spectatorRootChannelWord k
              ((List.ofFn w.2).filter (fun i => decide (P i))) B))
          (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
          (∫ w, siteOscillation q y (spectatorRootChannelWord k
              ((List.ofFn w.2).filter (fun i => decide (P i))) B)
            ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
            Real.exp (v * t) * (2 * ‖B‖) * Metric.exponentialDistanceProfile
              (S : Set ↥Λ) (c / (4 * (2 : ℝ) ^ α)) α y ∧
          (∀ w : PoissonWord.Word (AdmissibleSupport Λ R),
            Metric.infEDist y (S : Set ↥Λ) = ⊤ →
            siteOscillation q y (spectatorRootChannelWord k
              ((List.ofFn w.2).filter (fun i => decide (P i))) B) = 0) := by
  obtain ⟨c, v, hc, hv, hgrowth⟩ := exists_latticeChannelWord_spatial_growth hp R hJ hΔ
  refine ⟨c, v, hc, hv, ?_⟩
  intro q _ Λ h hh hhJ a ha E₀ Ω hΩ hgap hspan P _ Aux _ _ S B hB t y
  let := ManyBody.graphPseudoEMetricSpace (planeDomainGraph Λ)
  let k := fun i : AdmissibleSupport Λ R =>
    positiveConstraint (positiveNormalization p (Δ / 2) J)
      (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))
  have hg := hgrowth Λ h hh hhJ a ha E₀ Ω hΩ hgap hspan P Aux S B hB t y
  have htransport := integrable_and_integral_siteOscillation_filter_le P k B t y _
    ⟨hg.1, hg.2.1⟩
  refine ⟨htransport.1, htransport.2, fun w hy => ?_⟩
  rw [spectatorRootChannelWord_filter]
  exact hg.2.2 (PoissonWord.partitionWords P w).1 hy

end TNLean.PEPS.AreaLaw

end
