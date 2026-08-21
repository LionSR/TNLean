/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteCauchySchwarz
import TNLean.Algebra.HermitianTracePower
import TNLean.Algebra.OrthogonalProjection
import TNLean.Algebra.PosSemidefSupport

/-!
# Trace-square and purity equality criteria

This file proves two spectral equality criteria for finite complex matrices. For a
Hermitian matrix, the square of the trace is at most the dimension times the trace
of the square, with equality precisely for scalar matrices. For a positive
semidefinite matrix of Hilbert--Schmidt norm one, the trace is at least one, with
equality precisely for rank-one orthogonal projections.

## Main results

* `Matrix.IsHermitian.trace_re_sq_le_card_mul_trace_sq_re`
* `Matrix.IsHermitian.trace_re_sq_eq_card_mul_trace_sq_re_iff`
* `Matrix.PosSemidef.one_le_trace_re_of_trace_sq_eq_one`
* `Matrix.PosSemidef.trace_re_eq_one_iff_isRankOneOrthogonalProjection`

## References

* Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
  equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
  lines 802--815
-/

open scoped Matrix ComplexOrder BigOperators

variable {D : ℕ}

/-- A rank-one orthogonal projection is a Hermitian idempotent matrix of rank one.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs";
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 807--815. -/
def IsRankOneOrthogonalProjection (P : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  IsOrthogonalProjection P ∧ P.rank = 1

namespace Matrix

private theorem IsHermitian.trace_re_eq_sum_eigenvalues
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) :
    Q.trace.re = ∑ i, hQ.eigenvalues i := by
  rw [hQ.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

private theorem IsHermitian.trace_sq_re_eq_sum_eigenvalues_sq
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) :
    (Q ^ 2).trace.re = ∑ i, (hQ.eigenvalues i) ^ 2 := by
  rw [hQ.trace_pow_eq_sum_eigenvalues_pow, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (congrArg Complex.re (Complex.ofReal_pow (hQ.eigenvalues i) 2)).symm

/-- For a Hermitian matrix, the square of its real trace is at most the dimension
times the real trace of its square.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 802--815. -/
theorem IsHermitian.trace_re_sq_le_card_mul_trace_sq_re
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) :
    Q.trace.re ^ 2 ≤ D * (Q ^ 2).trace.re := by
  rw [hQ.trace_re_eq_sum_eigenvalues, hQ.trace_sq_re_eq_sum_eigenvalues_sq]
  simpa using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := hQ.eigenvalues))

/-- Equality in the Hermitian trace-square inequality holds precisely for real
scalar multiples of the identity.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 802--815. -/
theorem IsHermitian.trace_re_sq_eq_card_mul_trace_sq_re_iff
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) :
    Q.trace.re ^ 2 = D * (Q ^ 2).trace.re ↔
      ∃ r : ℝ, Q = (r : ℂ) • 1 := by
  constructor
  · intro heq
    have heq' : (∑ i, hQ.eigenvalues i) ^ 2 = D * ∑ i, (hQ.eigenvalues i) ^ 2 := by
      rw [← hQ.trace_re_eq_sum_eigenvalues, ← hQ.trace_sq_re_eq_sum_eigenvalues_sq]
      exact heq
    have hconst : ∀ i : Fin D, ∀ j : Fin D, hQ.eigenvalues i = hQ.eigenvalues j := by
      have h := (Finset.sq_sum_eq_card_mul_sum_sq_iff
        (s := Finset.univ) (f := hQ.eigenvalues)).mp (by simpa using heq')
      exact fun i j ↦ h i (Finset.mem_univ i) j (Finset.mem_univ j)
    cases isEmpty_or_nonempty (Fin D) with
    | inl hD =>
        refine ⟨0, Subsingleton.elim _ _⟩
    | inr hD =>
        let i : Fin D := Classical.choice hD
        refine ⟨hQ.eigenvalues i, ?_⟩
        let U := hQ.eigenvectorUnitary
        let Δ : Matrix (Fin D) (Fin D) ℂ :=
          Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues)
        have hspec : Q = (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) Δ := by
          simpa [Δ, U] using hQ.spectral_theorem
        have hΔ : Δ = (hQ.eigenvalues i : ℂ) • 1 := by
          ext j k
          by_cases hjk : j = k
          · subst k
            simp [Δ, hconst j i]
          · simp [Δ, hjk]
        calc
          Q = (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) Δ := hspec
          _ = (hQ.eigenvalues i : ℂ) • 1 := by rw [hΔ]; simp
  · rintro ⟨r, rfl⟩
    simp [pow_two]
    ring

/-- A positive semidefinite matrix whose squared trace norm is one has trace at
least one.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 802--815. -/
theorem PosSemidef.one_le_trace_re_of_trace_sq_eq_one
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef)
    (hpurity : (P ^ 2).trace = 1) :
    1 ≤ P.trace.re := by
  let lam : Fin D → ℝ := hP.isHermitian.eigenvalues
  have hsum : P.trace.re = ∑ i, lam i := hP.isHermitian.trace_re_eq_sum_eigenvalues
  have hsq : ∑ i, (lam i) ^ 2 = 1 := by
    have h := hP.isHermitian.trace_sq_re_eq_sum_eigenvalues_sq
    rw [hpurity] at h
    simpa using h.symm
  have hnonneg : ∀ i, 0 ≤ lam i := hP.eigenvalues_nonneg
  have hsum_nonneg : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ ↦ hnonneg i
  have hsq_le : ∑ i, (lam i) ^ 2 ≤ (∑ i, lam i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ hnonneg i
  rw [hsum]
  nlinarith

/-- Under unit squared trace norm, a positive semidefinite matrix has trace one
precisely when it is a rank-one orthogonal projection.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 802--815. -/
theorem PosSemidef.trace_re_eq_one_iff_isRankOneOrthogonalProjection
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef)
    (hpurity : (P ^ 2).trace = 1) :
    P.trace.re = 1 ↔ IsRankOneOrthogonalProjection P := by
  let lam : Fin D → ℝ := hP.isHermitian.eigenvalues
  have htrace : P.trace.re = ∑ i, lam i := hP.isHermitian.trace_re_eq_sum_eigenvalues
  have hsq : ∑ i, (lam i) ^ 2 = 1 := by
    have h := hP.isHermitian.trace_sq_re_eq_sum_eigenvalues_sq
    rw [hpurity] at h
    simpa using h.symm
  constructor
  · intro htrace_one
    have hsum : ∑ i, lam i = 1 := htrace.symm.trans htrace_one
    have hnonneg : ∀ i, 0 ≤ lam i := hP.eigenvalues_nonneg
    have hle_one : ∀ i, lam i ≤ 1 := by
      intro i
      calc
        lam i ≤ ∑ j, lam j :=
          Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
        _ = 1 := hsum
    have hterm_nonneg : ∀ i, 0 ≤ lam i * (1 - lam i) := fun i ↦
      mul_nonneg (hnonneg i) (sub_nonneg.mpr (hle_one i))
    have hsum_term : ∑ i, lam i * (1 - lam i) = 0 := by
      calc
        ∑ i, lam i * (1 - lam i) = (∑ i, lam i) - ∑ i, (lam i) ^ 2 := by
          simp_rw [mul_sub, mul_one, pow_two]
          rw [Finset.sum_sub_distrib]
        _ = 0 := by rw [hsum, hsq]; norm_num
    have heig_idem : ∀ i, (lam i) ^ 2 = lam i := by
      intro i
      have hi := congrFun
        (Fintype.sum_eq_zero_iff_of_nonneg hterm_nonneg |>.mp hsum_term) i
      have hi' : lam i * (1 - lam i) = 0 := by simpa using hi
      nlinarith
    have hidem : P * P = P := by
      let U := hP.isHermitian.eigenvectorUnitary
      let Δ : Matrix (Fin D) (Fin D) ℂ :=
        Matrix.diagonal (RCLike.ofReal ∘ hP.isHermitian.eigenvalues)
      have hspec : P = (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) Δ := by
        simpa [Δ, U] using hP.isHermitian.spectral_theorem
      have hΔidem : Δ * Δ = Δ := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        change (lam i : ℂ) * (lam i : ℂ) = (lam i : ℂ)
        have hi := heig_idem i
        rw [pow_two] at hi
        exact_mod_cast hi
      calc
        P * P =
            (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) Δ *
              (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) Δ := by
                rw [hspec]
        _ = (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) (Δ * Δ) := by
          rw [map_mul]
        _ = (Unitary.conjStarAlgAut ℂ (Matrix (Fin D) (Fin D) ℂ) U) Δ := by rw [hΔidem]
        _ = P := hspec.symm
    refine ⟨⟨hP.isHermitian, hidem⟩, ?_⟩
    have hrank_re := hP.isHermitian.rank_eq_trace_re_of_idem hidem
    rw [htrace_one] at hrank_re
    exact_mod_cast hrank_re
  · rintro ⟨hproj, hrank⟩
    have hrank_re := hproj.1.rank_eq_trace_re_of_idem hproj.2
    rw [hrank] at hrank_re
    norm_num at hrank_re ⊢
    exact hrank_re.symm

end Matrix
