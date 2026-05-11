/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalScalar

/-!
# Proportional MPV expansion for assembled BNT blocks

This module records the expansion and projection identities used in the
proportional block-selection step of the fundamental theorem.  The hypotheses
are exactly the nonzero proportionality of the two assembled tensors; no
external coefficient-array hypotheses are introduced.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017), Theorem `thm1`, lines 1170--1192.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

section ProportionalExpansion

/-- **Weighted MPV-state proportionality from proportional assembled block tensors.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. The proof of the
block-selection step expands the two canonical-form tensors into their BNT
block sums and then uses proportionality of the total MPV families. This lemma
formalizes exactly that expansion, without adding coefficient-array hypotheses:
the scalar is the one supplied by the proportionality of the assembled tensors
at the fixed length `N`. -/
lemma exists_weighted_mpvState_eq_smul_of_nonzeroProportionalMPV₂_toTensorFromBlocks
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (N : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := by
  rcases hProp N with ⟨c, hc, hN⟩
  have hAstate :
      mpvState (d := d) (toTensorFromBlocks μA A) N =
        ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N := by
    refine mpvState_eq_sum_of_decomp
      (d := d) (toTensorFromBlocks μA A) A
      (N := N) (fun j : Fin rA => (μA j) ^ N) ?_
    intro σ
    simpa [smul_eq_mul] using
      mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μA) (A := A) σ
  have hBstate :
      mpvState (d := d) (toTensorFromBlocks μB B) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
    refine mpvState_eq_sum_of_decomp
      (d := d) (toTensorFromBlocks μB B) B
      (N := N) (fun k : Fin rB => (μB k) ^ N) ?_
    intro σ
    simpa [smul_eq_mul] using
      mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μB) (A := B) σ
  have hTotal :
      mpvState (d := d) (toTensorFromBlocks μA A) N =
        c • mpvState (d := d) (toTensorFromBlocks μB B) N := by
    apply PiLp.ext
    intro σ
    simpa [mpvState_apply, mpv, smul_eq_mul] using hN σ
  refine ⟨c, hc, ?_⟩
  calc
    (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        mpvState (d := d) (toTensorFromBlocks μA A) N := hAstate.symm
    _ = c • mpvState (d := d) (toTensorFromBlocks μB B) N := hTotal
    _ = c • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := by
      rw [hBstate]

/-- **A scalar sequence for proportional weighted MPV-state sums.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. The proof uses
one proportionality scalar at each chain length. This lemma packages those
lengthwise scalars into a single nonzero sequence so that later convergence
arguments can refer to the same scalar at each occurrence of the fixed length. -/
lemma exists_weighted_mpvState_eq_smul_sequence_of_nonzeroProportionalMPV₂_toTensorFromBlocks
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ c : ℕ → ℂ, (∀ N, c N ≠ 0) ∧
      ∀ N : ℕ,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := by
  classical
  have h :
      ∀ N : ℕ, ∃ c : ℂ, c ≠ 0 ∧
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) :=
    fun N =>
      exists_weighted_mpvState_eq_smul_of_nonzeroProportionalMPV₂_toTensorFromBlocks
        A B hProp N
  choose c hc hEq using h
  exact ⟨c, hc, hEq⟩

/-- **Weighted inner-product proportionality from proportional assembled block tensors.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. After expanding
the proportional assembled MPV states into weighted BNT block sums, the proof
projects the equality against a single block MPV. This lemma records that
projection for an arbitrary tensor `X`. -/
lemma exists_weighted_mpvInner_eq_mul_of_nonzeroProportionalMPV₂_toTensorFromBlocks
    {d rA rB D : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (X : MPSTensor d D) (N : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
        c * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) := by
  obtain ⟨c, hc, hstate⟩ :=
    exists_weighted_mpvState_eq_smul_of_nonzeroProportionalMPV₂_toTensorFromBlocks
      A B hProp N
  refine ⟨c, hc, ?_⟩
  have hinner :=
    congrArg (fun v : MPVSpace d N => ⟪mpvState (d := d) X N, v⟫_ℂ) hstate
  simpa [mpvInner, inner_sum, inner_smul_right] using hinner

/-- **A scalar sequence for proportional weighted MPV projections.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. This is the
projection form of the previous scalar-sequence lemma: after projecting the
weighted state sums against a fixed block MPV, the same nonzero scalar sequence
relates the projected weighted sums at every length. -/
lemma exists_weighted_mpvInner_eq_mul_sequence_of_nonzeroProportionalMPV₂_toTensorFromBlocks
    {d rA rB D : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (X : MPSTensor d D) :
    ∃ c : ℕ → ℂ, (∀ N, c N ≠ 0) ∧
      ∀ N : ℕ,
        (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
          c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) := by
  obtain ⟨c, hc, hstate⟩ :=
    exists_weighted_mpvState_eq_smul_sequence_of_nonzeroProportionalMPV₂_toTensorFromBlocks
      A B hProp
  refine ⟨c, hc, ?_⟩
  intro N
  have hinner :=
    congrArg (fun v : MPVSpace d N => ⟪mpvState (d := d) X N, v⟫_ℂ) (hstate N)
  simpa [mpvInner, inner_sum, inner_smul_right] using hinner

/-- **A scalar sequence for normalized proportional weighted projections.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. This packages
the projected weighted-sum identity supplied by proportional assembled tensors
in the normalized form used in the block-selection contradiction. The same
nonzero scalar sequence is corrected by the factor `(\nu/\mu)^N` after
division by the chosen nonzero weights. -/
lemma exists_normalized_weighted_mpvInner_eq_mul_adjusted_sequence_of_nonzeroProportionalMPV₂
    {d rA rB D : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (X : MPSTensor d D) (μ ν : ℂ) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    ∃ c : ℕ → ℂ, (∀ N, c N ≠ 0) ∧
      ∀ N : ℕ,
        (μ ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
          (c N * (ν / μ) ^ N) *
            ((ν ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)) := by
  obtain ⟨c, hc, hinner⟩ :=
    exists_weighted_mpvInner_eq_mul_sequence_of_nonzeroProportionalMPV₂_toTensorFromBlocks
      A B hProp X
  exact ⟨c, hc,
    normalized_weighted_mpvInner_eq_mul_adjusted_of_eq_mul A B X c μ ν hμ hν hinner⟩

end ProportionalExpansion

end MPSTensor
