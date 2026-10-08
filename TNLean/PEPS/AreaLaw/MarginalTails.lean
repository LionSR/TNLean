/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.SupportedMarginalTails
import QICLean.Analysis.TypicalSet
import QICLean.Algebra.TraceReindex

/-!
# Marginal surprisal tails for finite-range lattice Hamiltonians

Lemma 3.1 of the area-law manuscript holds for any finite tensor product. This module
instantiates it on a finite induced square-lattice domain with local dimension `q`: an
operator in the supported-operator algebra of the circuit layer is supported on its
region in the sense of the general lemma, and the regional state of a gapped ground
vector of a finite-range Hamiltonian satisfies the moment and tail bounds with
`ℬ = 1 + ∑ log² (e q^{|X|})` over the admissible supports `X` that meet both sides of the
cut.

## Main results

* `QuantumCircuit.isSupportedOn_of_mem_supportedOperators`: the support bridge.
* `TNLean.PEPS.AreaLaw.LocalHamiltonian.log_surprisalMoment_reducedState_le`:
  `eq:initial-tail-mgf` for the regional state.
* `TNLean.PEPS.AreaLaw.LocalHamiltonian.surprisalTail_reducedState_le`:
  `eq:initial-tail-probability` for the regional state.
* `TNLean.PEPS.AreaLaw.LocalHamiltonian.one_sub_rpow_le_typicalMass_reducedState`: the
  typical marginal spectrum at the concentration width `concentrationWidth`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and the
  concentration statement after it, lines 209–219.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- An operator of the supported-operator algebra on `S` acts as the identity outside `S`
in the sense of the general marginal-tail lemma. -/
theorem isSupportedOn_of_mem_supportedOperators {S : Finset ι}
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A ∈ supportedOperators q (S : Set ι)) :
    Entropy.IsSupportedOn (n := fun _ ↦ q) A S := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ apply_eq_zero_of_mem_supportedOperators hA ⟨v, hv, hne⟩, ?_⟩
  intro σ τ σ' τ' h1 h2 h3 h4
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨m, hm, rfl⟩ := hA
    simp only [rectKronecker_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hi : i ∈ S
    · rw [h1 i hi, h2 i hi]
    · rw [hm i hi, h3 i hi, h4 i hi, one_apply_eq, one_apply_eq]
  | zero => rfl
  | add A B _ _ hA hB => simp [hA, hB]
  | smul c A _ hA => simp [hA]

end QuantumCircuit

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- The regional state is the marginal of the ground vector in cut coordinates. -/
theorem partialTraceRight_cutVector (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    partialTraceRight (vecMulVec (WithLp.ofLp (Entropy.cutVector (n := fun _ ↦ q) A Ω))
      (star (WithLp.ofLp (Entropy.cutVector (n := fun _ ↦ q) A Ω)))) =
      reducedState Λ q Ω A := by
  ext a b
  simp [reducedState, configurationSplit, vecMulVec_apply]

/-- The parameter `ℬ = 1 + ∑ log² (e q^{|X|})` of Lemma 3.1 for a finite-range Hamiltonian
and a cut `A`, the sum running over the admissible supports that meet both sides.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, lines 47–55. -/
noncomputable def cutLogBudget (Λ : Finset (ℤ × ℤ)) (q R : ℕ) (A : Finset (Site Λ)) : ℝ :=
  Entropy.cutLogBudget (Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A)
    (Entropy.supportDim (fun _ ↦ q) ∘ fun X : AdmissibleSupport Λ R ↦ X.1)

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, moment bound.** For a gapped
ground vector `Ω` with gap `Δ > 0` of a finite-range Hamiltonian with term norms at most
`J ≥ 0`, and any cut `A`, the surprisal of the regional state satisfies
`log E e^{uK} ≤ u S(A) + 512 e (J/Δ) ℬ u²` for `|u| ≤ 1/(32 √((1 + J/Δ) ℬ))`.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–63,
`eq:initial-tail-mgf`. -/
theorem LocalHamiltonian.log_surprisalMoment_reducedState_le (h : LocalHamiltonian Λ q R J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q} (hΔ : 0 < Δ)
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ)) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (J / Δ) (cutLogBudget Λ q R A)) :
    Real.log (Entropy.surprisalMoment (reducedState_isHermitian Λ q Ω A).eigenvalues u) ≤
      u * regionalEntropy Λ q Ω A +
        512 * Real.exp 1 * (J / Δ) * cutLogBudget Λ q R A * u ^ 2 := by
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  replace heig : toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]; exact heig
  exact Entropy.log_surprisalMoment_cut_le (n := fun _ ↦ q) (B := A)
    (fun X ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported X))
    h.hermitian hJ h.norm_le hΩ hΔ heig hgap (partialTraceRight_cutVector Ω A)
    (reducedState_isHermitian Λ q Ω A) hu

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, tail bound.** Under the hypotheses
of `LocalHamiltonian.log_surprisalMoment_reducedState_le`, for every real `w` (the
manuscript states `w ≥ 0`),
`Pr {|K - S(A)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + J/Δ) ℬ)))}`.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 64–69,
`eq:initial-tail-probability`. -/
theorem LocalHamiltonian.surprisalTail_reducedState_le (h : LocalHamiltonian Λ q R J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q} (hΔ : 0 < Δ)
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ)) (w : ℝ) :
    Entropy.surprisalTail (reducedState_isHermitian Λ q Ω A).eigenvalues
        (regionalEntropy Λ q Ω A) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) * cutLogBudget Λ q R A))))) := by
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  replace heig : toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]; exact heig
  exact Entropy.surprisalTail_cut_le (n := fun _ ↦ q) (B := A)
    (fun X ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported X))
    h.hermitian hJ h.norm_le hΩ hΔ heig hgap (partialTraceRight_cutVector Ω A)
    (reducedState_isHermitian Λ q Ω A) w

/-- The concentration width `32 √((1 + J/Δ) ℬ_A) (M log (n + 2) + e/2 + log 2)` at which
the marginal tail of Lemma 3.1 drops to `(n + 2)^{-M}`. -/
noncomputable def concentrationWidth (Λ : Finset (ℤ × ℤ)) (q R : ℕ) (J Δ : ℝ)
    (A : Finset (Site Λ)) (n : ℕ) (M : ℝ) : ℝ :=
  32 * Real.sqrt ((1 + J / Δ) * cutLogBudget Λ q R A) *
    (M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2)

/-- **Typical marginal spectrum.** The positive eigenvalues of the regional state whose
surprisal lies within the concentration width of `S_Ω(A)` carry mass at least
`1 - (n + 2)^{-M}`.
Area-law manuscript, `02-initial.tex`, lines 209–219, the concentration statement after
Lemma 3.1, before the lattice budget `ℬ_A ≤ C (1 + |∂_Λ A|)` is inserted. -/
theorem LocalHamiltonian.one_sub_rpow_le_typicalMass_reducedState
    (h : LocalHamiltonian Λ q R J) (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q} (hΔ : 0 < Δ)
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ)) (n : ℕ) (M : ℝ) :
    1 - ((n : ℝ) + 2) ^ (-M) ≤
      Entropy.typicalMass (reducedState_isHermitian Λ q Ω A).eigenvalues
        (regionalEntropy Λ q Ω A) (concentrationWidth Λ q R J Δ A n M) := by
  have hpsd := ((Matrix.posSemidef_vecMulVec_self_star (fun x ↦ Ω x)).submatrix
    (configurationSplit Λ q A).symm).partialTraceRight
  have hp : ∀ i, 0 ≤ (reducedState_isHermitian Λ q Ω A).eigenvalues i :=
    hpsd.eigenvalues_nonneg
  have hs : ∑ i, (reducedState_isHermitian Λ q Ω A).eigenvalues i = 1 := by
    have htr := (reducedState_isHermitian Λ q Ω A).trace_eq_sum_eigenvalues
    have h1 : (reducedState Λ q Ω A).trace = 1 := by
      have hn := hgs.1
      rw [reducedState, Matrix.trace_partialTraceRight]
      change (Matrix.reindex (configurationSplit Λ q A) (configurationSplit Λ q A)
        (Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).trace = 1
      rw [Matrix.trace_reindex, Matrix.trace_vecMulVec,
        ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hn]
      simp
    rw [h1] at htr
    have h2 := congrArg Complex.re htr
    simp only [Complex.one_re, Complex.re_sum] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ ↦ by simp
  have htail := h.surprisalTail_reducedState_le hJ hΔ hgs A (concentrationWidth Λ q R J Δ A n M)
  have hmass := Entropy.one_sub_surprisalTail_le_typicalMass hp hs (regionalEntropy Λ q Ω A)
    (concentrationWidth Λ q R J Δ A n M)
  set Rr := Real.sqrt ((1 + J / Δ) * cutLogBudget Λ q R A)
  have hB : 1 ≤ cutLogBudget Λ q R A := Entropy.one_le_cutLogBudget _ _
  have hR : 0 < Rr := Real.sqrt_pos.mpr (by
    have : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
    positivity)
  have hexp : 2 * Real.exp (Real.exp 1 / 2) *
      Real.exp (-(concentrationWidth Λ q R J Δ A n M / (32 * Rr))) = ((n : ℝ) + 2) ^ (-M) := by
    have hw : concentrationWidth Λ q R J Δ A n M / (32 * Rr) =
        M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2 := by
      unfold concentrationWidth
      change 32 * Rr * _ / (32 * Rr) = _
      field_simp
    rw [hw, Real.rpow_def_of_pos (by positivity)]
    rw [show -(M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2) =
      Real.log (n + 2) * -M + (-(Real.exp 1 / 2) + -Real.log 2) by ring, Real.exp_add,
      Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log two_pos]
    field_simp
  have h2 := htail.trans (min_le_right _ _)
  rw [hexp] at h2
  linarith

end TNLean.PEPS.AreaLaw
