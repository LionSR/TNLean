/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.QuadraticSolutionRephasing

/-!
# The corrected same-state quadratic reconstruction converse

A solution of system (S) already supplies row normalization of its tensor.
If that tensor separately represents the same actual nonzero length-N state
as a condition-C1 canonical tensor, the complete-cut uniqueness theorem
supplies a unitary gauge and an Nth-root phase. The candidate solution is
not assumed canonical or injective. Its explicit rephasing is a solution of
the same system, retains the actual length-N state, and is exactly gauged
to the canonical tensor.

**Scope restriction (same state and full cut regime):** the supplied
solution must separately represent the prescribed nonzero state, and
N > 2 L0 + D^4 supplies both endpoint cuts. These conditions are not derived
from the internal quadratic equations. The construction of a solution from
an actual unique OBC canonical window remains separate. See
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex` and
`docs/paper-gaps/pgvwc07_intertwiner_chain_off_by_one.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 8 and proof, lines 1154--1176,
with the complete-cut uniqueness argument of Theorem 7, lines 1002--1108.
-/

open scoped BigOperators Matrix

namespace MPSTensor.QuadraticReconstructionSolution

variable {d D m : ℕ}
    {H : Fin m → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}

/-- The actual same-state solution tensor is unitarily conjugate to the
canonical tensor up to an Nth-root phase. The solution's normalization is
used; no canonical or injectivity hypothesis on the solution tensor is added.
Both endpoint cuts are derived from the actual fixed-length equality and
condition C1 in the displayed size regime.
Source: the corrected PGVWC07 Theorem 8 converse, lines 1154--1176;
finite-ring phase and cut corrections in the module's cited paper-gap notes. -/
theorem exists_unitary_phase_of_same_state (s : QuadraticReconstructionSolution H)
    {A : MPSTensor d D} {L₀ N : ℕ} (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L₀) (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv A σ = mpv s.tensor σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    (∑ i, A i * (A i)ᴴ = 1) ∧
      ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ξ : ℂ), ‖ξ‖ = 1 ∧ ξ ^ N = 1 ∧
        ∀ i, A i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * s.tensor i *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hnonzero
  let : NeZero D := ⟨fun hD ↦ hσ₀ (by subst D; simp [mpv, coeff, Matrix.trace])⟩
  obtain ⟨C⟩ := hA
  obtain ⟨lam, hlam, _, hsum⟩ := C.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hcandidate : ∑ i, s.tensor i * (s.tensor i)ᴴ = ((1 : ℝ) : ℂ) ^ 2 • 1 := by
    simpa only [Complex.ofReal_one, one_pow, one_smul] using s.sum_mul_conjTranspose
  obtain ⟨hlameq, U, ξ, hξ, hξN, hconj⟩ := pgvwc07_uniqueness_of_weighted
    hlam (by norm_num : (0 : ℝ) < 1) hsum hcandidate hC1 hN hstate ⟨σ₀, hσ₀⟩
  refine ⟨?_, U, ξ, hξ, hξN, hconj⟩
  simpa only [hlameq, Complex.ofReal_one, one_pow, one_smul] using hsum

/-- The corrected converse as the existing unit-modulus gauge-phase
predicate, with the same explicit nonzero fixed-length state condition.
Source: corrected PGVWC07 Theorem 8, lines 1154--1176. -/
theorem unitGaugePhaseEquiv_of_same_state (s : QuadraticReconstructionSolution H)
    {A : MPSTensor d D} {L₀ N : ℕ} (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L₀) (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv A σ = mpv s.tensor σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    UnitGaugePhaseEquiv s.tensor A := by
  obtain ⟨_, U, ξ, hξ, _, hconj⟩ :=
    s.exists_unitary_phase_of_same_state hA hC1 hN hstate hnonzero
  refine ⟨Unitary.toUnits U, ξ, ?_, fun i ↦ ?_⟩
  · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
    norm_num
  · change A i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * s.tensor i *
      star (U : Matrix (Fin D) (Fin D) ℂ))
    simpa only [Matrix.star_eq_conjTranspose] using hconj i

/-- The explicitly rephased tensor remains a solution of the very same
quadratic system and represents the same length-N state. It is exactly
gauge equivalent, through an actual unitary, to the canonical tensor.
Source: corrected PGVWC07 Theorem 8, lines 1154--1176, and
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`. -/
theorem exists_rephased_solution_exact_gauge_of_same_state
    (s : QuadraticReconstructionSolution H)
    {A : MPSTensor d D} {L₀ N : ℕ} (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L₀) (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv A σ = mpv s.tensor σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    ∃ (ξ : ℂ) (hξ : ‖ξ‖ = 1), ξ ^ N = 1 ∧
      (∀ σ : Fin N → Fin d, mpv (s.rephase ξ hξ).tensor σ = mpv s.tensor σ) ∧
      GaugeEquiv (s.rephase ξ hξ).tensor A ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∀ i, A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨_, U, ξ, hξ, hξN, hconj⟩ :=
    s.exists_unitary_phase_of_same_state hA hC1 hN hstate hnonzero
  have hhat : ∀ i, A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
    intro i
    rw [hconj i]
    simp only [rephase_tensor, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨ξ, hξ, hξN, s.mpv_rephase ξ hξ hξN, ?_, U, hhat⟩
  refine ⟨Unitary.toUnits U, fun i ↦ ?_⟩
  change A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
    star (U : Matrix (Fin D) (Fin D) ℂ)
  simpa only [Matrix.star_eq_conjTranspose] using hhat i

end MPSTensor.QuadraticReconstructionSolution
