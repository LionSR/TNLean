/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TracePurity

/-!
# The SIC--POVM overlap bound

This file proves Wolf's lower bound for the sum of the squared pairwise
Hilbert--Schmidt overlaps of positive semidefinite matrices of unit purity,
together with its equality criterion.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
  Equation (2.30); `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 790--823
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix

variable {d n : ℕ}

private lemma trace_sum_sq_re_eq_diag_add_offDiag
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    ((∑ i, P i) ^ 2).trace.re =
      (∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        ((P ij.1 * P ij.2).trace).re) +
      ∑ i, ((P i) ^ 2).trace.re := by
  classical
  rw [pow_two, Finset.sum_mul_sum, Matrix.trace_sum, Complex.re_sum]
  simp_rw [Matrix.trace_sum, Complex.re_sum]
  calc
    (∑ i, ∑ j, (P i * P j).trace.re) =
        ∑ ij ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ,
          (P ij.1 * P ij.2).trace.re := by
      rw [Finset.sum_product]
    _ = ∑ ij ∈ (Finset.univ : Finset (Fin n)).diag ∪ Finset.univ.offDiag,
          (P ij.1 * P ij.2).trace.re := by
      rw [Finset.diag_union_offDiag]
    _ = _ := by
      rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
      simp [pow_two, add_comm]

private lemma sum_trace_re_eq_trace_sum_re
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, (P i).trace.re) = (∑ i, P i).trace.re := by
  rw [Matrix.trace_sum, Complex.re_sum]

private lemma sum_posSemidef (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, (P i).PosSemidef) :
    (∑ i, P i).PosSemidef := by
  classical
  exact Finset.sum_induction _ Matrix.PosSemidef (fun A B hA hB ↦ hA.add hB)
    Matrix.PosSemidef.zero (fun i _ ↦ hP i)

private lemma offDiag_card_fin (hn : 2 ≤ n) :
    ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
  rw [Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Nat.cast_sub (by nlinarith : n ≤ n * n)]
  push_cast
  ring

private lemma rankOne_of_sum_trace_eq_card
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, (P i).PosSemidef)
    (hpurity : ∀ i, ((P i) ^ 2).trace = 1)
    (hsumtrace : ∑ i, (P i).trace.re = n) :
    ∀ i, IsRankOneOrthogonalProjection (P i) := by
  have htrace_each : ∀ i, 1 ≤ (P i).trace.re := fun i ↦
    (hP i).one_le_trace_re_of_trace_sq_eq_one (hpurity i)
  have hdefsum : ∑ i, ((P i).trace.re - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsumtrace]
    simp
  have hdefnonneg : ∀ i, 0 ≤ (P i).trace.re - 1 := fun i ↦
    sub_nonneg.mpr (htrace_each i)
  intro i
  have hiFun : (fun i ↦ (P i).trace.re - 1) = 0 :=
    Fintype.sum_eq_zero_iff_of_nonneg hdefnonneg |>.mp hdefsum
  have hi := congrFun hiFun i
  change (P i).trace.re - 1 = 0 at hi
  apply ((hP i).trace_re_eq_one_iff_isRankOneOrthogonalProjection (hpurity i)).mp
  linarith

private lemma eq_card_div_smul_one_of_trace_equalities
    (Q : Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    (hQ : Q.IsHermitian) (htrace : Q.trace.re = n)
    (htraceSq : Q.trace.re ^ 2 = (d : ℝ) * (Q ^ 2).trace.re) :
    Q = ((n : ℝ) / d : ℂ) • 1 := by
  obtain ⟨r, hr⟩ := hQ.trace_re_sq_eq_card_mul_trace_sq_re_iff.mp htraceSq
  have hrval : r = (n : ℝ) / d := by
    rw [hr] at htrace
    simp at htrace
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    apply (eq_div_iff hdR.ne').2
    nlinarith
  simpa [hrval] using hr

private lemma offDiag_overlap_eq_of_cauchySchwarz_eq
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (hn : 2 ≤ n) (hd : 0 < d)
    (hcsEq :
      (∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
          (P ij.1 * P ij.2).trace.re) ^ 2 =
        (n : ℝ) * ((n : ℝ) - 1) *
          ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
            ((P ij.1 * P ij.2).trace.re) ^ 2)
    (hT_eq :
      (d : ℝ) *
          (∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
            (P ij.1 * P ij.2).trace.re) =
        (n : ℝ) * ((n : ℝ) - d)) :
    ∀ i j, i ≠ j →
      (P i * P j).trace.re =
        ((n : ℝ) - d) / (((n : ℝ) - 1) * d) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hconst : ∀ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ∀ kl ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (P ij.1 * P ij.2).trace.re = (P kl.1 * P kl.2).trace.re := by
    apply (Finset.sq_sum_eq_card_mul_sum_sq_iff
      (s := (Finset.univ : Finset (Fin n)).offDiag)
      (f := fun ij ↦ (P ij.1 * P ij.2).trace.re)).mp
    rw [offDiag_card_fin hn]
    simpa [mul_assoc] using hcsEq
  intro i j hij
  have hijmem : (i, j) ∈ (Finset.univ : Finset (Fin n)).offDiag := by simp [hij]
  have hsumconst :
      (∑ kl ∈ (Finset.univ : Finset (Fin n)).offDiag,
          (P kl.1 * P kl.2).trace.re) =
        ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) *
          (P i * P j).trace.re := by
    calc
      (∑ kl ∈ (Finset.univ : Finset (Fin n)).offDiag,
          (P kl.1 * P kl.2).trace.re) =
          ∑ _kl ∈ (Finset.univ : Finset (Fin n)).offDiag,
            (P i * P j).trace.re := by
        apply Finset.sum_congr rfl
        intro kl hkl
        exact hconst kl hkl (i, j) hijmem
      _ = _ := by simp
  rw [offDiag_card_fin hn] at hsumconst
  apply (eq_div_iff (by positivity : ((n : ℝ) - 1) * d ≠ 0)).2
  nlinarith

private lemma sicPOVM_bound_eq_of_offDiag_overlap_eq
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (hn : 2 ≤ n) (hd : 0 < d)
    (hoverlap : ∀ i j, i ≠ j →
      (P i * P j).trace.re =
        ((n : ℝ) - d) / (((n : ℝ) - 1) * d)) :
    (n : ℝ) * ((n : ℝ) - d) ^ 2 / (((n : ℝ) - 1) * (d : ℝ) ^ 2) =
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        ((P ij.1 * P ij.2).trace.re) ^ 2 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    (n : ℝ) * ((n : ℝ) - d) ^ 2 / (((n : ℝ) - 1) * (d : ℝ) ^ 2) =
        (n : ℝ) * ((n : ℝ) - 1) *
          (((n : ℝ) - d) / (((n : ℝ) - 1) * d)) ^ 2 := by
      field_simp
    _ = ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) *
          (((n : ℝ) - d) / (((n : ℝ) - 1) * d)) ^ 2 := by
      rw [offDiag_card_fin hn]
    _ = ∑ _ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
          (((n : ℝ) - d) / (((n : ℝ) - 1) * d)) ^ 2 := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hoverlap ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2]

/-- Wolf's SIC--POVM bound: among positive semidefinite matrices of unit purity,
the sum of the squared off-diagonal Hilbert--Schmidt overlaps has the stated
dimension-dependent lower bound.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
Equation (2.30); `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 790--807. -/
theorem sicPOVM_offDiag_overlap_sq_bound
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hP : ∀ i, (P i).PosSemidef)
    (hpurity : ∀ i, ((P i) ^ 2).trace = 1) :
    (n : ℝ) * ((n : ℝ) - d) ^ 2 / (((n : ℝ) - 1) * (d : ℝ) ^ 2) ≤
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        ((P ij.1 * P ij.2).trace.re) ^ 2 := by
  classical
  let Q : Matrix (Fin d) (Fin d) ℂ := ∑ i, P i
  let T : ℝ := ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    (P ij.1 * P ij.2).trace.re
  let S : ℝ := ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    ((P ij.1 * P ij.2).trace.re) ^ 2
  have hQpsd : Q.PosSemidef := sum_posSemidef P hP
  have htrace_each : ∀ i, 1 ≤ (P i).trace.re := fun i ↦
    (hP i).one_le_trace_re_of_trace_sq_eq_one (hpurity i)
  have htraceQ : (n : ℝ) ≤ Q.trace.re := by
    rw [← sum_trace_re_eq_trace_sum_re P]
    calc
      (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i, (P i).trace.re := Finset.sum_le_sum fun i _ ↦ htrace_each i
  have hQsq : (Q ^ 2).trace.re = T + n := by
    rw [trace_sum_sq_re_eq_diag_add_offDiag]
    simp only [hpurity, Complex.one_re, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rfl
  have htrace_sq := hQpsd.isHermitian.trace_re_sq_le_card_mul_trace_sq_re
  have hTlower : (n : ℝ) * ((n : ℝ) - d) ≤ (d : ℝ) * T := by
    rw [hQsq] at htrace_sq
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have htrace0 : 0 ≤ Q.trace.re := le_trans hn0 htraceQ
    nlinarith
  have hT0 : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro ij hij
    exact (Complex.nonneg_iff.mp
      ((hP ij.1).trace_mul_nonneg (hP ij.2))).1
  have hcs : T ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) * S := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)).offDiag)
      (f := fun ij ↦ (P ij.1 * P ij.2).trace.re)
    rw [offDiag_card_fin hn] at h
    simpa [T, S, mul_assoc] using h
  have hnum0 : 0 ≤ (n : ℝ) * ((n : ℝ) - d) := by
    have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
    positivity
  have hsquared :
      ((n : ℝ) * ((n : ℝ) - d)) ^ 2 ≤ ((d : ℝ) * T) ^ 2 := by
    nlinarith
  have hpoly :
      (n : ℝ) * ((n : ℝ) - d) ^ 2 ≤
        ((n : ℝ) - 1) * (d : ℝ) ^ 2 * S := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    nlinarith
  rw [div_le_iff₀]
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hpoly
  · have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    positivity

/-- Equality in Wolf's SIC--POVM bound holds precisely for rank-one
projections forming a tight equiangular family.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
Equations (2.30)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 798--815. -/
theorem sicPOVM_offDiag_overlap_sq_eq_iff
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hP : ∀ i, (P i).PosSemidef)
    (hpurity : ∀ i, ((P i) ^ 2).trace = 1) :
    (n : ℝ) * ((n : ℝ) - d) ^ 2 / (((n : ℝ) - 1) * (d : ℝ) ^ 2) =
        ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
          ((P ij.1 * P ij.2).trace.re) ^ 2 ↔
      (∀ i, IsRankOneOrthogonalProjection (P i)) ∧
      (∑ i, P i) = ((n : ℝ) / d : ℂ) • 1 ∧
      ∀ i j, i ≠ j →
        (P i * P j).trace.re =
          ((n : ℝ) - d) / (((n : ℝ) - 1) * d) := by
  classical
  let Q : Matrix (Fin d) (Fin d) ℂ := ∑ i, P i
  let T : ℝ := ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    (P ij.1 * P ij.2).trace.re
  let S : ℝ := ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    ((P ij.1 * P ij.2).trace.re) ^ 2
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_trans (by norm_num) hnR
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdnR : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hden : 0 < ((n : ℝ) - 1) * (d : ℝ) ^ 2 := by positivity
  have hQpsd : Q.PosSemidef := sum_posSemidef P hP
  have htrace_each : ∀ i, 1 ≤ (P i).trace.re := fun i ↦
    (hP i).one_le_trace_re_of_trace_sq_eq_one (hpurity i)
  have htraceQ : (n : ℝ) ≤ Q.trace.re := by
    rw [← sum_trace_re_eq_trace_sum_re P]
    calc
      (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i, (P i).trace.re := Finset.sum_le_sum fun i _ ↦ htrace_each i
  have hQsq : (Q ^ 2).trace.re = T + n := by
    rw [trace_sum_sq_re_eq_diag_add_offDiag]
    simp only [hpurity, Complex.one_re, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rfl
  have htrace_sq := hQpsd.isHermitian.trace_re_sq_le_card_mul_trace_sq_re
  have hTlower : (n : ℝ) * ((n : ℝ) - d) ≤ (d : ℝ) * T := by
    rw [hQsq] at htrace_sq
    nlinarith
  have hT0 : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro ij hij
    exact (Complex.nonneg_iff.mp
      ((hP ij.1).trace_mul_nonneg (hP ij.2))).1
  have hcs : T ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) * S := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)).offDiag)
      (f := fun ij ↦ (P ij.1 * P ij.2).trace.re)
    rw [offDiag_card_fin hn] at h
    simpa [T, S, mul_assoc] using h
  constructor
  · intro heq
    have heqpoly :
        (n : ℝ) * ((n : ℝ) - d) ^ 2 =
          ((n : ℝ) - 1) * (d : ℝ) ^ 2 * S := by
      rw [div_eq_iff hden.ne'] at heq
      simpa [S, mul_assoc, mul_left_comm, mul_comm] using heq
    have hsquared :
        ((n : ℝ) * ((n : ℝ) - d)) ^ 2 ≤ ((d : ℝ) * T) ^ 2 := by
      have hnum0 : 0 ≤ (n : ℝ) * ((n : ℝ) - d) := by positivity
      nlinarith
    have heqpoly' :
        ((n : ℝ) * ((n : ℝ) - d)) ^ 2 =
          (d : ℝ) ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) * S) := by
      nlinarith [heqpoly]
    have hreverse : ((d : ℝ) * T) ^ 2 ≤
        ((n : ℝ) * ((n : ℝ) - d)) ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hcs (sq_nonneg (d : ℝ))
      rw [← heqpoly'] at hscaled
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hsquaresEq :
        ((d : ℝ) * T) ^ 2 = ((n : ℝ) * ((n : ℝ) - d)) ^ 2 :=
      le_antisymm hreverse hsquared
    have hcsEq : T ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * S := by
      nlinarith [heqpoly']
    have hT_eq : (d : ℝ) * T = (n : ℝ) * ((n : ℝ) - d) := by
      have hnum0 : 0 ≤ (n : ℝ) * ((n : ℝ) - d) := by positivity
      nlinarith [hsquaresEq]
    have htraceQeq : Q.trace.re = n := by
      rw [hQsq] at htrace_sq
      nlinarith
    have htraceSqEq :
        Q.trace.re ^ 2 = (d : ℝ) * (Q ^ 2).trace.re := by
      rw [hQsq]
      nlinarith
    have hsumtrace : ∑ i, (P i).trace.re = n := by
      rw [sum_trace_re_eq_trace_sum_re P]
      exact htraceQeq
    have hrankOne := rankOne_of_sum_trace_eq_card P hP hpurity hsumtrace
    have hQscalar := eq_card_div_smul_one_of_trace_equalities
      Q hd hQpsd.isHermitian htraceQeq htraceSqEq
    dsimp only [T, S] at hcsEq hT_eq
    have hoverlap := offDiag_overlap_eq_of_cauchySchwarz_eq P hn hd hcsEq hT_eq
    exact ⟨hrankOne, hQscalar, hoverlap⟩
  · rintro ⟨hrankOne, hQscalar, hoverlap⟩
    exact sicPOVM_bound_eq_of_offDiag_overlap_eq P hn hd hoverlap

/-- Equality families in Wolf's SIC--POVM bound are linearly independent when
the matrix dimension is at least two.

**Local fix (one-dimensional equality families):** Wolf's concluding
linear-independence assertion fails for `d = 1` and `n > 1`; see
`docs/paper-gaps/wolf_sic_povm_linear_independence.tex`. The hypothesis `2 ≤ d`
is exactly the nondegeneracy condition needed by the coefficient equation.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs";
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 807--823. -/
theorem sicPOVM_linearIndependent_of_overlap_bound_eq
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hn : 2 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n)
    (hP : ∀ i, (P i).PosSemidef)
    (hpurity : ∀ i, ((P i) ^ 2).trace = 1)
    (heq :
      (n : ℝ) * ((n : ℝ) - d) ^ 2 / (((n : ℝ) - 1) * (d : ℝ) ^ 2) =
        ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
          ((P ij.1 * P ij.2).trace.re) ^ 2) :
    LinearIndependent ℂ P := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by omega) hd
  obtain ⟨hrankOne, hsumP, hoverlap⟩ :=
    (sicPOVM_offDiag_overlap_sq_eq_iff P hn hd0 hdn hP hpurity).mp heq
  let a : ℝ := ((n : ℝ) - d) / (((n : ℝ) - 1) * d)
  have htraceP : ∀ i, (P i).trace = 1 := by
    intro i
    have hre := ((hP i).trace_re_eq_one_iff_isRankOneOrthogonalProjection
      (hpurity i)).mpr (hrankOne i)
    have him := (Complex.nonneg_iff.mp (hP i).trace_nonneg).2
    apply Complex.ext
    · simpa using hre
    · simpa using him.symm
  have hoverlapComplex : ∀ i j, i ≠ j → (P i * P j).trace = (a : ℂ) := by
    intro i j hij
    have hre := hoverlap i j hij
    have him := (Complex.nonneg_iff.mp ((hP i).trace_mul_nonneg (hP j))).2
    apply Complex.ext
    · change (P i * P j).trace.re = a
      simpa [a] using hre
    · simpa using him.symm
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hsumc : ∑ i, c i = 0 := by
    have h := congrArg Matrix.trace hc
    simp only [Matrix.trace_sum, Matrix.trace_smul, htraceP, Matrix.trace_zero,
      smul_eq_mul, mul_one] at h
    exact h
  have hsumErase : ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, c i = -c j := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) c
      (Finset.mem_univ j)
    rw [hsumc] at hsplit
    linear_combination hsplit
  have hpair : ∑ i, c i * (P j * P i).trace = 0 := by
    have h := congrArg (fun X ↦ Matrix.trace (P j * X)) hc
    simpa only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Matrix.mul_zero, Matrix.trace_zero, smul_eq_mul] using h
  have hpairSplit :
      c j * (P j * P j).trace +
        ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
          c i * (P j * P i).trace = 0 := by
    rw [Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun i ↦ c i * (P j * P i).trace) (Finset.mem_univ j)]
    exact hpair
  have hcoeff : (1 - (a : ℂ)) * c j = 0 := by
    rw [show (P j * P j).trace = 1 by simpa [pow_two] using hpurity j] at hpairSplit
    have hoff :
        (∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
          c i * (P j * P i).trace) = (a : ℂ) * (-c j) := by
      calc
        (∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
            c i * (P j * P i).trace) =
            ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, c i * (a : ℂ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hoverlapComplex j i (Finset.ne_of_mem_erase hi).symm]
        _ = (a : ℂ) *
            ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, c i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (a : ℂ) * (-c j) := by rw [hsumErase]
    rw [hoff] at hpairSplit
    linear_combination hpairSplit
  have ha_ne : (1 - (a : ℂ)) ≠ 0 := by
    intro ha
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have hdR : (1 : ℝ) < d := by exact_mod_cast hd
    have haone : a = 1 := by
      have := congrArg Complex.re (sub_eq_zero.mp ha)
      simpa using this.symm
    dsimp [a] at haone
    rw [div_eq_one_iff_eq (by positivity : ((n : ℝ) - 1) * d ≠ 0)] at haone
    nlinarith
  exact (mul_eq_zero.mp hcoeff).resolve_left ha_ne

/-- A singleton family containing a matrix of unit purity is linearly
independent.

**Local fix (one-dimensional equality families):** This is the `n = 1` branch
of the corrected nondegeneracy condition; see
`docs/paper-gaps/wolf_sic_povm_linear_independence.tex`.

Source context: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition
"SIC POVMs"; `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 807--823. -/
theorem singleton_linearIndependent_of_trace_sq_eq_one
    (P : Fin 1 → Matrix (Fin d) (Fin d) ℂ)
    (hpurity : ((P 0) ^ 2).trace = 1) :
    LinearIndependent ℂ P := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  fin_cases i
  simp only [Fin.sum_univ_one] at hc
  by_contra hcoeff
  have hPzero : P 0 = 0 := (smul_eq_zero.mp hc).resolve_left hcoeff
  rw [hPzero] at hpurity
  norm_num at hpurity

end Matrix
