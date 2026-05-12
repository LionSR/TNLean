/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion

/-!
# Dominant projected contradiction for proportional BNT families

This module contains the dominant-block projection contradiction used in the
proportional non-decaying-overlap step of the fundamental theorem.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem thm1, lines 1170--1192.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section ProportionalDominant

/-- **Dominant normalized inner-product concentration.**

Source context: arXiv:1606.00608, Theorem thm1, lines 1170--1192. In the
fixed-block argument, after expanding a canonical-form tensor into weighted BNT
blocks, one projects the weighted sum against a selected dominant block. If all
other weights have strictly smaller modulus and the selected block is
asymptotically normalized while the off-diagonal overlaps decay, the normalized
projection tends to one. This is the inner-product concentration step used
before comparing the two proportional block sums. -/
lemma tendsto_normalized_weighted_mpvInner_sum_of_dominant
    {d r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (j₀ : Fin r) (hμ0 : μ j₀ ≠ 0)
    (hdiag :
      Tendsto (fun N => mpvInner (d := d) (A j₀) (A j₀) N) atTop (nhds 1))
    (hoff : ∀ j : Fin r, j ≠ j₀ →
      Tendsto (fun N => mpvInner (d := d) (A j₀) (A j) N) atTop (nhds 0))
    (hratio : ∀ j : Fin r, j ≠ j₀ → ‖μ j / μ j₀‖ < 1) :
    Tendsto
      (fun N : ℕ =>
        (μ j₀ ^ N)⁻¹ *
          (∑ j : Fin r, (μ j) ^ N * mpvInner (d := d) (A j₀) (A j) N))
      atTop (nhds 1) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ j : Fin r, (μ j / μ j₀) ^ N *
            mpvInner (d := d) (A j₀) (A j) N)
        atTop (nhds 1) :=
    sum_tendsto_one_of_diag (hμ0 := hμ0) (j0 := j₀) rfl hdiag hratio hoff
  convert hsum using 1
  ext N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_pow]
  field_simp [pow_ne_zero N hμ0]

/-- **Phase-normalized dominant inner-product concentration.**

Source context: arXiv:1606.00608, Theorem thm1, lines 1170--1192. After
Corollary eqV supplies a phase relation
\(|V^{(N)}(B_{k_0})\rangle = \zeta^N |V^{(N)}(A_0)\rangle\), the weighted
projection of the \(B\)-family against \(A_0\) is normalized by the combined
weight \((\mu_{k_0}\zeta)^N\). Under strict dominance of \(\mu_{k_0}\) and
decay of the remaining projected overlaps, the normalized projection tends to
one. -/
lemma tendsto_phase_normalized_weighted_mpvInner_sum_of_dominant
    {d r D₀ : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ} {ζ : ℂ}
    (A₀ : MPSTensor d D₀)
    (B : (k : Fin r) → MPSTensor d (dim k))
    (k₀ : Fin r) (hμ0 : μ k₀ ≠ 0) (hζ : ‖ζ‖ = 1)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) (B k₀) N = ζ ^ N • mpvState (d := d) A₀ N)
    (hdiag :
      Tendsto (fun N => mpvInner (d := d) A₀ A₀ N) atTop (nhds 1))
    (hoff : ∀ k : Fin r, k ≠ k₀ →
      Tendsto (fun N => mpvInner (d := d) A₀ (B k) N) atTop (nhds 0))
    (hratio : ∀ k : Fin r, k ≠ k₀ → ‖μ k / μ k₀‖ < 1) :
    Tendsto
      (fun N : ℕ =>
        ((μ k₀ * ζ) ^ N)⁻¹ *
          (∑ k : Fin r, (μ k) ^ N * mpvInner (d := d) A₀ (B k) N))
      atTop (nhds 1) := by
  classical
  have hζ_ne : ζ ≠ 0 := by
    intro hzero
    have : ‖ζ‖ = 0 := by simp [hzero]
    linarith
  have hμζ_ne : μ k₀ * ζ ≠ 0 := mul_ne_zero hμ0 hζ_ne
  have hterms : ∀ k : Fin r,
      Tendsto
        (fun N : ℕ =>
          (μ k / (μ k₀ * ζ)) ^ N * mpvInner (d := d) A₀ (B k) N)
        atTop (nhds (if k = k₀ then (1 : ℂ) else 0)) := by
    intro k
    by_cases hk : k = k₀
    · subst k
      have hdiag_phase :
          Tendsto
            (fun N : ℕ =>
              (μ k₀ / (μ k₀ * ζ)) ^ N * mpvInner (d := d) A₀ (B k₀) N)
            atTop (nhds 1) := by
        refine Tendsto.congr' ?_ hdiag
        filter_upwards with N
        have hinner :
            mpvInner (d := d) A₀ (B k₀) N =
              ζ ^ N * mpvInner (d := d) A₀ A₀ N := by
          dsimp [mpvInner]
          rw [hPhase N]
          simp [inner_smul_right]
        rw [hinner]
        have hcancel : (μ k₀ / (μ k₀ * ζ)) ^ N * ζ ^ N = 1 := by
          rw [← mul_pow]
          field_simp [hμ0, hζ_ne]
          simp
        symm
        calc
          (μ k₀ / (μ k₀ * ζ)) ^ N *
              (ζ ^ N * mpvInner (d := d) A₀ A₀ N) =
              ((μ k₀ / (μ k₀ * ζ)) ^ N * ζ ^ N) *
                mpvInner (d := d) A₀ A₀ N := by ring
          _ = mpvInner (d := d) A₀ A₀ N := by simp [hcancel]
      simpa using hdiag_phase
    · have hratio_phase : ‖μ k / (μ k₀ * ζ)‖ < 1 := by
        rw [norm_div, norm_mul, hζ, mul_one]
        simpa [norm_div] using hratio k hk
      simpa [hk] using
        bounded_mul_tendsto_zero
          (μ k / (μ k₀ * ζ))
          (fun N : ℕ => mpvInner (d := d) A₀ (B k) N)
          (le_of_lt hratio_phase) (hoff k hk)
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ k : Fin r,
            (μ k / (μ k₀ * ζ)) ^ N * mpvInner (d := d) A₀ (B k) N)
        atTop (nhds (∑ k : Fin r, if k = k₀ then (1 : ℂ) else 0)) := by
    exact tendsto_finset_sum Finset.univ (fun k _ => hterms k)
  have hsum_one :
      Tendsto
        (fun N : ℕ =>
          ∑ k : Fin r,
            (μ k / (μ k₀ * ζ)) ^ N * mpvInner (d := d) A₀ (B k) N)
        atTop (nhds 1) := by
    simpa using hsum
  convert hsum_one using 1
  ext N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_pow]
  field_simp [pow_ne_zero N hμζ_ne]

/-- **Leading BNT normalized inner-product concentration.**

Source context: arXiv:1606.00608, Theorem thm1, lines 1170--1192. This is
the preceding dominant projection estimate specialized to the leading block of
an `IsCanonicalFormBNT` family. The strict ordering of BNT weight moduli
supplies the required strict dominance of the leading weight.

**Scope restriction (one-copy-per-sector):** The predicate `IsCanonicalFormBNT`
selects one BNT representative in each sector. The general CPSV16 BNT
canonical form allows multiplicities inside a sector. This restriction is documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma tendsto_normalized_weighted_mpvInner_sum_of_leading_CFBNT
    {d r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hA : IsCanonicalFormBNT μ A) (hr : r ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        (μ ⟨0, Nat.pos_of_ne_zero hr⟩ ^ N)⁻¹ *
          (∑ j : Fin r,
            (μ j) ^ N *
              mpvInner (d := d) (A ⟨0, Nat.pos_of_ne_zero hr⟩) (A j) N))
      atTop (nhds 1) := by
  let j₀ : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  have hμ0 : μ j₀ ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero j₀
  have hdiag :
      Tendsto (fun N => mpvInner (d := d) (A j₀) (A j₀) N) atTop (nhds 1) :=
    tendsto_inner_one (A j₀) (hA.toHasNormalizedSelfOverlap.overlap_tendsto_one j₀)
  have hoff : ∀ j : Fin r, j ≠ j₀ →
      Tendsto (fun N => mpvInner (d := d) (A j₀) (A j) N) atTop (nhds 0) := by
    intro j hj
    exact tendsto_inner_zero (A j₀) (A j) (hA.cross_overlap_tendsto_zero j₀ j hj.symm)
  have hratio : ∀ j : Fin r, j ≠ j₀ → ‖μ j / μ j₀‖ < 1 := by
    intro j hj
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hμ0)).mpr
      (hA.mu_strict_anti (by
        simp only [j₀, Fin.lt_def]
        exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))))
  simpa [j₀] using
    tendsto_normalized_weighted_mpvInner_sum_of_dominant
      A j₀ hμ0 hdiag hoff hratio

/-- **Leading phase-normalized BNT inner-product concentration.**

Source context: arXiv:1606.00608, Theorem thm1, lines 1170--1192. This is
the phase-normalized projection estimate specialized to a leading \(B\)-block
which Corollary eqV has identified with the leading \(A\)-block up to the phase
\(\zeta^N\). The strict BNT ordering supplies dominance of the leading
\(B\)-weight, while BNT separation makes the remaining projected overlaps
vanish.

**Scope restriction (one-copy-per-sector):** The predicate `IsCanonicalFormBNT`
selects one BNT representative in each sector. The general CPSV16 BNT
canonical form allows multiplicities inside a sector. This restriction is documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma tendsto_phase_normalized_weighted_mpvInner_sum_of_leading_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ} {ζ : ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hζ : ‖ζ‖ = 1)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N =
        ζ ^ N • mpvState (d := d) (A ⟨0, Nat.pos_of_ne_zero hrA⟩) N) :
    Tendsto
      (fun N : ℕ =>
        ((μB ⟨0, Nat.pos_of_ne_zero hrB⟩ * ζ) ^ N)⁻¹ *
          (∑ k : Fin rB,
            (μB k) ^ N *
              mpvInner (d := d) (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k) N))
      atTop (nhds 1) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  have hζ_ne : ζ ≠ 0 := by
    intro hzero
    have : ‖ζ‖ = 0 := by simp [hzero]
    linarith
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  have hdiag :
      Tendsto (fun N => mpvInner (d := d) (A a0) (A a0) N) atTop (nhds 1) :=
    tendsto_inner_one (A a0) (hA.toHasNormalizedSelfOverlap.overlap_tendsto_one a0)
  have hoff : ∀ k : Fin rB, k ≠ b0 →
      Tendsto (fun N => mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) := by
    intro k hk
    have hB_inner :
        Tendsto (fun N => mpvInner (d := d) (B b0) (B k) N) atTop (nhds 0) :=
      tendsto_inner_zero (B b0) (B k)
        (hB.cross_overlap_tendsto_zero b0 k (fun h => hk h.symm))
    have hscale :
        Tendsto
          (fun N : ℕ => ((star ζ)⁻¹) ^ N * mpvInner (d := d) (B b0) (B k) N)
          atTop (nhds 0) := by
      refine bounded_mul_tendsto_zero ((star ζ)⁻¹)
        (fun N : ℕ => mpvInner (d := d) (B b0) (B k) N) ?_ hB_inner
      rw [norm_inv, norm_star, hζ]
      simp
    refine Tendsto.congr' ?_ hscale
    filter_upwards with N
    have hA_eq :
        mpvState (d := d) (A a0) N =
          (ζ ^ N)⁻¹ • mpvState (d := d) (B b0) N := by
      rw [hPhase N]
      rw [smul_smul]
      rw [inv_mul_cancel₀ (pow_ne_zero N hζ_ne), one_smul]
    dsimp [mpvInner]
    rw [hA_eq]
    simp [inner_smul_left, inv_pow]
  have hratio : ∀ k : Fin rB, k ≠ b0 → ‖μB k / μB b0‖ < 1 := by
    intro k hk
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
      (hB.mu_strict_anti (by
        simp only [b0, Fin.lt_def]
        exact Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))))
  simpa [a0, b0] using
    tendsto_phase_normalized_weighted_mpvInner_sum_of_dominant
      (A a0) B b0 hμB_ne hζ (by simpa [a0, b0] using hPhase)
      hdiag hoff hratio

/-- **Leading phase-adjusted scalar convergence.**

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. In the
dominant phase-matched situation, projecting the proportional weighted BNT
sums against the leading \(A\)-block and using the phase relation
\(|V^{(N)}(B_0)\rangle=\zeta^N |V^{(N)}(A_0)\rangle\) shows that the same
eventual proportionality scalar satisfies
\[
  c_N\left(\frac{\mu^B_0\zeta}{\mu^A_0}\right)^N \longrightarrow 1 .
\]
This is a projection consequence only; it does not assert exact selected
coefficient equality or any residual-family linear independence.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma exists_dominant_phase_adjusted_scalar_tendsto_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ} {ζ : ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hζ : ‖ζ‖ = 1)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N =
        ζ ^ N • mpvState (d := d) (A ⟨0, Nat.pos_of_ne_zero hrA⟩) N)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ c : ℕ → ℂ,
      (∀ᶠ N in atTop, c N ≠ 0) ∧
      (∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) ∧
      Tendsto
        (fun N : ℕ =>
          c N *
            ((μB ⟨0, Nat.pos_of_ne_zero hrB⟩ * ζ) /
              μA ⟨0, Nat.pos_of_ne_zero hrA⟩) ^ N)
        atTop (nhds (1 : ℂ)) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  obtain ⟨c, hc, hState⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  have hζ_ne : ζ ≠ 0 := by
    intro hzero
    have : ‖ζ‖ = 0 := by simp [hzero]
    linarith
  have hμBζ_ne : μB b0 * ζ ≠ 0 := mul_ne_zero hμB_ne hζ_ne
  have hA_proj :
      Tendsto
        (fun N : ℕ =>
          (μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA,
              (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N))
        atTop (nhds (1 : ℂ)) := by
    simpa [a0] using
      tendsto_normalized_weighted_mpvInner_sum_of_leading_CFBNT
        A hA hrA
  have hB_proj :
      Tendsto
        (fun N : ℕ =>
          ((μB b0 * ζ) ^ N)⁻¹ *
            (∑ k : Fin rB,
              (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N))
        atTop (nhds (1 : ℂ)) := by
    simpa [a0, b0] using
      tendsto_phase_normalized_weighted_mpvInner_sum_of_leading_CFBNT
        A B hA hB hrA hrB hζ hPhase
  have hInner :
      ∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N) =
          c N *
            (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N) :=
    eventually_weighted_mpvInner_eq_mul_sequence_of_eventually_weighted_mpvState_eq_smul_sequence
      A B c hState (A a0)
  have hProjected :
      ∀ᶠ N in atTop,
        (μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N) =
          (c N * ((μB b0 * ζ) / μA a0) ^ N) *
            (((μB b0 * ζ) ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N)) := by
    refine hInner.mono ?_
    intro N hN
    let S : ℂ := ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N
    rw [hN]
    change (μA a0 ^ N)⁻¹ * (c N * S) =
      (c N * ((μB b0 * ζ) / μA a0) ^ N) * (((μB b0 * ζ) ^ N)⁻¹ * S)
    calc
      (μA a0 ^ N)⁻¹ * (c N * S) = ((μA a0 ^ N)⁻¹ * c N) * S := by ring
      _ = ((c N * ((μB b0 * ζ) / μA a0) ^ N) *
            ((μB b0 * ζ) ^ N)⁻¹) * S := by
        rw [adjusted_scalar_factor_eq (c N) (μA a0) (μB b0 * ζ) N hμA_ne hμBζ_ne]
      _ = (c N * ((μB b0 * ζ) / μA a0) ^ N) *
            (((μB b0 * ζ) ^ N)⁻¹ * S) := by ring
  have hQuot :
      Tendsto
        (fun N : ℕ =>
          ((μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA,
              (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N)) /
            (((μB b0 * ζ) ^ N)⁻¹ *
              (∑ k : Fin rB,
                (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N)))
        atTop (nhds (1 : ℂ)) := by
    simpa using hA_proj.div hB_proj one_ne_zero
  have hPhaseAdjusted :
      Tendsto (fun N : ℕ => c N * ((μB b0 * ζ) / μA a0) ^ N)
        atTop (nhds (1 : ℂ)) := by
    refine Tendsto.congr' ?_ hQuot
    filter_upwards [hProjected, hB_proj.eventually_ne one_ne_zero] with N hN hB_ne
    let T : ℂ :=
      ((μB b0 * ζ) ^ N)⁻¹ *
        (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N)
    change
      ((μA a0 ^ N)⁻¹ *
        (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N)) / T =
        c N * ((μB b0 * ζ) / μA a0) ^ N
    rw [hN]
    exact mul_div_cancel_right₀ (c N * ((μB b0 * ζ) / μA a0) ^ N) hB_ne
  exact ⟨c, hc, hState, by simpa [a0, b0] using hPhaseAdjusted⟩

/-- **Dominant adjusted scalar has asymptotic modulus one.**

Source: arXiv:1606.00608, lines 1170--1192. In the
dominant-block projection comparison, eventual nonzero proportionality of the
assembled weighted BNT sums gives a scalar sequence. After normalizing
the two sums by their leading weights, this scalar is adjusted by
the leading-weight ratio; the normalized dominant terms on both sides have norm tending
to one, and therefore the adjusted scalar has modulus tending to one.

**Scope restriction (one-copy-per-sector):** The predicate `IsCanonicalFormBNT`
selects one BNT representative in each sector. The general CPSV16 BNT
canonical form allows multiplicities inside a sector. This restriction is documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ c : ℕ → ℂ,
      (∀ᶠ N in atTop, c N ≠ 0) ∧
      (∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) ∧
      Tendsto
        (fun N : ℕ =>
          ‖c N * (μB ⟨0, Nat.pos_of_ne_zero hrB⟩ /
            μA ⟨0, Nat.pos_of_ne_zero hrA⟩) ^ N‖)
        atTop (nhds (1 : ℝ)) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  have hA_self : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds 1) :=
    hA.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_self : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1) :=
    hB.toHasNormalizedSelfOverlap.overlap_tendsto_one
  obtain ⟨c, hc, hState⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  have hA_norm_dominant :
      Tendsto
        (fun N : ℕ =>
          ‖(μA a0 ^ N)⁻¹ •
            (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N)‖)
        atTop (nhds (1 : ℝ)) := by
    exact tendsto_norm_normalized_weighted_mpvState_sum_of_dominant
      A a0 hμA_ne hA_self (fun j hj => by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
          (hA.mu_strict_anti (by
            simp only [a0, Fin.lt_def]
            exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h)))))
  have hB_norm_dominant :
      Tendsto
        (fun N : ℕ =>
          ‖(μB b0 ^ N)⁻¹ •
            (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)‖)
        atTop (nhds (1 : ℝ)) := by
    exact tendsto_norm_normalized_weighted_mpvState_sum_of_dominant
      B b0 hμB_ne hB_self (fun k hk => by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
          (hB.mu_strict_anti (by
            simp only [b0, Fin.lt_def]
            exact Nat.pos_of_ne_zero (fun h => hk (Fin.ext h)))))
  have hAdjustedScalar_dom :
      Tendsto (fun N : ℕ => ‖c N * (μB b0 / μA a0) ^ N‖) atTop
        (nhds (1 : ℝ)) :=
    tendsto_norm_adjusted_weighted_mpvState_scalar_of_eventually_tendsto_norm_one
      A B c (μA a0) (μB b0) hμA_ne hμB_ne hState
      hA_norm_dominant hB_norm_dominant
  exact ⟨c, hc, hState, by simpa [a0, b0] using hAdjustedScalar_dom⟩

/-- **Dominant-block projection contradiction for proportional BNT families.**

Source: arXiv:1606.00608, Theorem thm1, lines 1170--1192. If the normalized
proportional projection identity eventually holds and has an adjusted scalar
whose modulus tends to one, then the dominant block on either side cannot have
all cross-overlaps tending to zero. This is the dominant case of the CPSV16
line 1182 argument after applying Lemma `Lem1`. -/
lemma dominant_projection_contradictions_of_normalized_proportional_inner
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (c : ℕ → ℂ)
    (hNormalizedInner :
      ∀ {D : ℕ} (X : MPSTensor d D) (μ ν : ℂ),
        μ ≠ 0 → ν ≠ 0 → ∀ᶠ N in atTop,
          (μ ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
            (c N * (ν / μ) ^ N) *
              ((ν ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)))
    (hAdjustedScalar_dom :
      Tendsto
        (fun N : ℕ =>
          ‖c N * (μB ⟨0, Nat.pos_of_ne_zero hrB⟩ /
            μA ⟨0, Nat.pos_of_ne_zero hrA⟩) ^ N‖)
        atTop (nhds (1 : ℝ))) :
    ((∀ j : Fin rA,
        Tendsto
          (fun N => mpvOverlap (d := d) (A j)
            (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N)
          atTop (nhds 0)) → False) ∧
    ((∀ k : Fin rB,
        Tendsto
          (fun N => mpvOverlap (d := d)
            (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k) N)
          atTop (nhds 0)) → False) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  have hAdjustedScalar :
      Tendsto (fun N : ℕ => ‖c N * (μB b0 / μA a0) ^ N‖) atTop
        (nhds (1 : ℝ)) := by
    simpa [a0, b0] using hAdjustedScalar_dom
  have hDominantB_contra :
      (∀ j : Fin rA, Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N)
        atTop (nhds 0)) → False := by
    intro hall
    have hall_inner : ∀ j : Fin rA,
        Tendsto (fun N => mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) :=
      fun j => tendsto_inner_zero_swap (d := d) (A j) (B b0) (hall j)
    have hA_proj_sum :
        Tendsto
          (fun N : ℕ =>
            ∑ j : Fin rA, (μA j / μA a0) ^ N *
              mpvInner (d := d) (B b0) (A j) N)
          atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rA))
        (fun (j : Fin rA) _ => show
          Tendsto
            (fun N : ℕ =>
              (μA j / μA a0) ^ N * mpvInner (d := d) (B b0) (A j) N)
            atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]
            exact (div_le_one (norm_pos_iff.mpr hμA_ne)).mpr
              (hA.toIsCanonicalForm.mu_antitone
                (show a0 ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le _))))
            (hall_inner j))
      simpa using this
    have hA_proj :
        Tendsto
          (fun N : ℕ =>
            (μA a0 ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N))
          atTop (nhds 0) := by
      convert hA_proj_sum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_pow]
      field_simp [pow_ne_zero N hμA_ne]
    have hB_proj :
        Tendsto
          (fun N : ℕ =>
            (μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N))
          atTop (nhds 1) := by
      simpa [b0] using tendsto_normalized_weighted_mpvInner_sum_of_leading_CFBNT B hB hrB
    have hRHS_norm_one :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (B b0) (B k) N))‖)
          atTop (nhds (1 : ℝ)) := by
      have hmul := hAdjustedScalar.mul hB_proj.norm
      simpa [norm_mul] using hmul
    have hRHS_norm_zero :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (B b0) (B k) N))‖)
          atTop (nhds (0 : ℝ)) := by
      have hnorm := hA_proj.norm
      have hnorm_zero :
          Tendsto
            (fun N : ℕ =>
              ‖(μA a0 ^ N)⁻¹ *
                (∑ j : Fin rA, (μA j) ^ N *
                  mpvInner (d := d) (B b0) (A j) N)‖)
            atTop (nhds (0 : ℝ)) := by
        simpa using hnorm
      have hEq :
          (fun N : ℕ =>
            ‖(μA a0 ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N *
                mpvInner (d := d) (B b0) (A j) N)‖) =ᶠ[atTop]
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (B b0) (B k) N))‖) := by
        filter_upwards [hNormalizedInner (B b0) (μA a0) (μB b0) hμA_ne hμB_ne]
          with N hN
        rw [hN]
      exact Tendsto.congr' hEq hnorm_zero
    exact zero_ne_one (tendsto_nhds_unique hRHS_norm_zero hRHS_norm_one)
  have hDominantA_contra :
      (∀ k : Fin rB, Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k) N)
        atTop (nhds 0)) → False := by
    intro hall
    have hall_inner : ∀ k : Fin rB,
        Tendsto (fun N => mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) :=
      fun k => tendsto_inner_zero (A a0) (B k) (hall k)
    have hA_proj :
        Tendsto
          (fun N : ℕ =>
            (μA a0 ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N))
          atTop (nhds 1) := by
      simpa [a0] using tendsto_normalized_weighted_mpvInner_sum_of_leading_CFBNT A hA hrA
    have hB_proj_sum :
        Tendsto
          (fun N : ℕ =>
            ∑ k : Fin rB, (μB k / μB b0) ^ N *
              mpvInner (d := d) (A a0) (B k) N)
          atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rB))
        (fun (k : Fin rB) _ => show
          Tendsto
            (fun N : ℕ =>
              (μB k / μB b0) ^ N * mpvInner (d := d) (A a0) (B k) N)
            atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]
            exact (div_le_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.toIsCanonicalForm.mu_antitone
                (show b0 ≤ k from Fin.mk_le_mk.mpr (Nat.zero_le _))))
            (hall_inner k))
      simpa using this
    have hB_proj :
        Tendsto
          (fun N : ℕ =>
            (μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N))
          atTop (nhds 0) := by
      convert hB_proj_sum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [div_pow]
      field_simp [pow_ne_zero N hμB_ne]
    have hRHS_norm_zero :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (A a0) (B k) N))‖)
          atTop (nhds (0 : ℝ)) := by
      have hmul := hAdjustedScalar.mul hB_proj.norm
      simpa [norm_mul] using hmul
    have hRHS_norm_one :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (A a0) (B k) N))‖)
          atTop (nhds (1 : ℝ)) := by
      have hnorm := hA_proj.norm
      have hnorm_one :
          Tendsto
            (fun N : ℕ =>
              ‖(μA a0 ^ N)⁻¹ *
                (∑ j : Fin rA, (μA j) ^ N *
                  mpvInner (d := d) (A a0) (A j) N)‖)
            atTop (nhds (1 : ℝ)) := by
        simpa using hnorm
      have hEq :
          (fun N : ℕ =>
            ‖(μA a0 ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N *
                mpvInner (d := d) (A a0) (A j) N)‖) =ᶠ[atTop]
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (A a0) (B k) N))‖) := by
        filter_upwards [hNormalizedInner (A a0) (μA a0) (μB b0) hμA_ne hμB_ne]
          with N hN
        rw [hN]
      exact Tendsto.congr' hEq hnorm_one
    exact zero_ne_one (tendsto_nhds_unique hRHS_norm_zero hRHS_norm_one)
  exact ⟨by simpa [b0] using hDominantB_contra, by simpa [a0] using hDominantA_contra⟩

/-- **Dominant-block projection contradiction from eventual proportionality.**

Source: arXiv:1606.00608, Theorem thm1, lines 1170--1192. After expanding
the two canonical-form tensors into their BNT block sums, eventual nonzero
proportionality supplies the scalar sequence used in the dominant-block
projection contradiction. This is the dominant case of the line 1182 argument,
with Lemma `Lem1` accounting for the sufficiently-large-length formulation. -/
lemma dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ((∀ j : Fin rA,
        Tendsto
          (fun N => mpvOverlap (d := d) (A j)
            (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N)
          atTop (nhds 0)) → False) ∧
    ((∀ k : Fin rB,
        Tendsto
          (fun N => mpvOverlap (d := d)
            (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k) N)
          atTop (nhds 0)) → False) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  obtain ⟨c, _hc, hState, hAdjustedScalar_dom⟩ :=
    exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp
  have hInner :
      ∀ {D : ℕ} (X : MPSTensor d D),
        ∀ᶠ N in atTop,
          (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
            c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) :=
    eventually_weighted_mpvInner_eq_mul_sequence_of_eventually_weighted_mpvState_eq_smul_sequence
      A B c hState
  have hNormalizedInner :
      ∀ {D : ℕ} (X : MPSTensor d D) (μ ν : ℂ),
        μ ≠ 0 → ν ≠ 0 → ∀ᶠ N in atTop,
          (μ ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
            (c N * (ν / μ) ^ N) *
              ((ν ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)) := by
    intro D X μ ν hμ hν
    refine (hInner X).mono ?_
    intro N hN
    let S : ℂ := ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N
    rw [hN]
    change (μ ^ N)⁻¹ * (c N * S) =
      (c N * (ν / μ) ^ N) * ((ν ^ N)⁻¹ * S)
    calc
      (μ ^ N)⁻¹ * (c N * S) = ((μ ^ N)⁻¹ * c N) * S := by ring
      _ = ((c N * (ν / μ) ^ N) * (ν ^ N)⁻¹) * S := by
        rw [adjusted_scalar_factor_eq (c N) μ ν N hμ hν]
      _ = (c N * (ν / μ) ^ N) * ((ν ^ N)⁻¹ * S) := by ring
  simpa [a0, b0] using
    dominant_projection_contradictions_of_normalized_proportional_inner
      A B hA hB hrA hrB c hNormalizedInner
      (by simpa [a0, b0] using hAdjustedScalar_dom)

/-- **Dominant blocks have non-decaying partners under eventual proportionality.**

Source: arXiv:1606.00608, Theorem thm1, lines 1170--1192. The dominant
projection contradiction rules out the alternative that the leading block on
one side has vanishing overlap with every block on the other side. Hence each
leading block admits a non-decaying overlap partner. -/
lemma exists_nondecaying_overlap_dominant_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    (∃ k₀ : Fin rB,
      ¬ Tendsto
        (fun N => mpvOverlap (d := d)
          (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k₀) N)
        atTop (nhds 0)) ∧
    (∃ j₀ : Fin rA,
      ¬ Tendsto
        (fun N => mpvOverlap (d := d)
          (A j₀) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N)
        atTop (nhds 0)) := by
  have hContra :=
    dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp
  constructor
  · by_contra h
    push Not at h
    exact hContra.2 h
  · by_contra h
    push Not at h
    exact hContra.1 h

end ProportionalDominant

end MPSTensor
