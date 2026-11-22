/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.StateSpace
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Entropy.Typical.TypicalMarginalMass
import QICLean.Entropy.Typical.TypicalSet
import QICLean.Algebra.Matrix.MatrixReindex
import QICLean.ManyBody.Hamiltonian.GroundSpace

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

* `ManyBody.PlaneInteraction.log_surprisalMoment_regionState_le`:
  `eq:initial-tail-mgf` for the regional state.
* `ManyBody.PlaneInteraction.surprisalTail_regionState_le`:
  `eq:initial-tail-probability` for the regional state.
* `ManyBody.PlaneInteraction.one_sub_rpow_le_typicalMass_regionState`: the
  typical marginal spectrum at QICLean's concentration width `Entropy.concentrationWidth`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and the
  concentration statement after it, lines 209–219.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace mem_groundSpace_iff AdmissibleSupport PlaneInteraction)

namespace TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, moment bound.** For a gapped
ground vector `Ω` with gap `Δ > 0` of a finite-range Hamiltonian with term norms at most
`J ≥ 0`, and any cut `A`, the surprisal of the regional state satisfies
`log E e^{uK} ≤ u S(A) + 512 e (J/Δ) ℬ u²` for `|u| ≤ 1/(32 √((1 + J/Δ) ℬ))`, where
`ℬ = 1 + ∑ log² (e q^{|X|})` is the cut budget `ManyBody.cutLogBudget` of the admissible
supports `X` meeting both sides of the cut.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–63,
`eq:initial-tail-mgf`. -/
theorem _root_.ManyBody.PlaneInteraction.log_surprisalMoment_regionState_le
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Site Λ)) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (J / Δ)
      (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A)) :
    Real.log (Entropy.surprisalMoment (ManyBody.regionState_isHermitian A Ω).eigenvalues u) ≤
      u * ManyBody.regionEntropy Ω A +
        512 * Real.exp 1 * (J / Δ) *
          ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A * u ^ 2 := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  exact Entropy.log_surprisalMoment_cut_le (n := fun _ ↦ q) (B := A)
    (fun X ↦ (h.mem X))
    hh hJ hhJ hΩ hΔ heig
    (hgap.posSemidef_sub_smul_one (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hspan)
        (ManyBody.regionState_eq_partialTraceRight_cutVector A Ω).symm
    (ManyBody.regionState_isHermitian A Ω) hu

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, tail bound.** Under the hypotheses
of `ManyBody.PlaneInteraction.log_surprisalMoment_regionState_le`, for every real `w` (the
manuscript states `w ≥ 0`),
`Pr {|K - S(A)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + J/Δ) ℬ)))}`.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 64–69,
`eq:initial-tail-probability`. -/
theorem _root_.ManyBody.PlaneInteraction.surprisalTail_regionState_le (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Site Λ)) (w : ℝ) :
    Entropy.surprisalTail (ManyBody.regionState_isHermitian A Ω).eigenvalues
        (ManyBody.regionEntropy Ω A) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) *
          ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A))))) := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  exact Entropy.surprisalTail_cut_le (n := fun _ ↦ q) (B := A)
    (fun X ↦ (h.mem X))
    hh hJ hhJ hΩ hΔ heig
    (hgap.posSemidef_sub_smul_one (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hspan)
        (ManyBody.regionState_eq_partialTraceRight_cutVector A Ω).symm
    (ManyBody.regionState_isHermitian A Ω) w

/-- **Typical marginal spectrum.** The positive eigenvalues of the regional state whose
surprisal lies within the concentration width of `S_Ω(A)` carry mass at least
`1 - (n + 2)^{-M}`.
Area-law manuscript, `02-initial.tex`, lines 209–219, the concentration statement after
Lemma 3.1, before the lattice budget `ℬ_A ≤ C (1 + |∂_Λ A|)` is inserted. -/
theorem _root_.ManyBody.PlaneInteraction.one_sub_rpow_le_typicalMass_regionState
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (A : Finset (Site Λ)) (n : ℕ) (M : ℝ) :
    1 - ((n : ℝ) + 2) ^ (-M) ≤
      Entropy.typicalMass (ManyBody.regionState_isHermitian A Ω).eigenvalues
        (ManyBody.regionEntropy Ω A)
        (Entropy.concentrationWidth (J / Δ)
          (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M) := by
  have hpsd := ManyBody.regionState_posSemidef A Ω
  have hp : ∀ i, 0 ≤ (ManyBody.regionState_isHermitian A Ω).eigenvalues i :=
    hpsd.eigenvalues_nonneg
  have hs : ∑ i, (ManyBody.regionState_isHermitian A Ω).eigenvalues i = 1 := by
    have htr := (ManyBody.regionState_isHermitian A Ω).trace_eq_sum_eigenvalues
    have h1 : (ManyBody.regionState Ω A).trace = 1 := ManyBody.trace_regionState_eq_one hΩ
    rw [h1] at htr
    have h2 := congrArg Complex.re htr
    simp only [Complex.one_re, Complex.re_sum] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ ↦ by simp
  have htail := h.surprisalTail_regionState_le hh hhJ hJ hΔ hΩ hgap hspan A
    (Entropy.concentrationWidth (J / Δ)
      (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M)
  have hmass := Entropy.one_sub_surprisalTail_le_typicalMass hp hs (ManyBody.regionEntropy Ω A)
    (Entropy.concentrationWidth (J / Δ)
      (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M)
  set Rr := Real.sqrt ((1 + J / Δ) *
    ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A)
  have hB : 1 ≤ ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A :=
    Entropy.one_le_cutLogBudget _ _
  have hR : 0 < Rr := Real.sqrt_pos.mpr (by
    have : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
    positivity)
  have hexp : 2 * Real.exp (Real.exp 1 / 2) *
      Real.exp (-(Entropy.concentrationWidth (J / Δ)
        (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M /
          (32 * Rr))) =
        ((n : ℝ) + 2) ^ (-M) := by
    have hw : Entropy.concentrationWidth (J / Δ)
        (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M /
          (32 * Rr) =
        M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2 := by
      unfold Entropy.concentrationWidth
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

end TNLean.Lattice
