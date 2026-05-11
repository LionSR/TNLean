/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
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
one proportionality scalar at each chain length. This lemma collects those
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

/-- **Nonzero proportionality from a weighted MPV-state scalar sequence.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. In the
block-selection proof, after expanding canonical-form tensors into weighted
BNT block sums, a lengthwise nonzero scalar identity of the weighted MPV-state
sums is exactly the corresponding projective proportionality of the assembled
tensors. This is the converse bookkeeping direction to
`exists_weighted_mpvState_eq_smul_sequence_of_nonzeroProportionalMPV₂_toTensorFromBlocks`. -/
lemma nonzeroProportionalMPV₂_toTensorFromBlocks_of_weighted_mpvState_eq_smul_sequence
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (hc : ∀ N : ℕ, c N ≠ 0)
    (hState : ∀ N : ℕ,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) :
    NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B) := by
  intro N
  refine ⟨c N, hc N, fun σ => ?_⟩
  have hAstate :
      mpvState (d := d) (toTensorFromBlocks μA A) N =
        ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N := by
    refine mpvState_eq_sum_of_decomp
      (d := d) (toTensorFromBlocks μA A) A
      (N := N) (fun j : Fin rA => (μA j) ^ N) ?_
    intro τ
    simpa [smul_eq_mul] using
      mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μA) (A := A) τ
  have hBstate :
      mpvState (d := d) (toTensorFromBlocks μB B) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
    refine mpvState_eq_sum_of_decomp
      (d := d) (toTensorFromBlocks μB B) B
      (N := N) (fun k : Fin rB => (μB k) ^ N) ?_
    intro τ
    simpa [smul_eq_mul] using
      mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μB) (A := B) τ
  have hN := congrArg (fun v : MPVSpace d N => v σ) (hState N)
  have hAcoeff :=
    mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μA) (A := A) σ
  have hBcoeff :=
    mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μB) (A := B) σ
  calc
    mpv (toTensorFromBlocks μA A) σ =
        ∑ j : Fin rA, (μA j) ^ N * mpv (A j) σ := by
          simpa [smul_eq_mul] using hAcoeff
    _ = c N * (∑ k : Fin rB, (μB k) ^ N * mpv (B k) σ) := by
      simpa [mpvState_apply, hAstate, hBstate, Pi.smul_apply, smul_eq_mul] using hN
    _ = c N * (∑ k : Fin rB, (μB k) ^ N • mpv (B k) σ) := by
      simp [smul_eq_mul]
    _ = c N * mpv (toTensorFromBlocks μB B) σ := by
      rw [← hBcoeff]

/-- **Subtracting a proportional dominant summand from weighted MPV-state sums.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. The proof removes
the already matched leading BNT component and continues with the remaining
blocks. This lemma isolates the linear algebra: if the total weighted MPV-state
sums are related by the scalar `c_N`, and the selected summands are related by
the same scalar, then the erased tails are related by the same scalar. -/
lemma weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (a0 : Fin rA) (b0 : Fin rB)
    (hState : ∀ N : ℕ,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (hSelected : ∀ N : ℕ,
      (μA a0) ^ N • mpvState (d := d) (A a0) N =
        c N • ((μB b0) ^ N • mpvState (d := d) (B b0) N)) :
    ∀ N : ℕ,
      ∑ j ∈ Finset.univ.erase a0, (μA j) ^ N • mpvState (d := d) (A j) N =
        c N •
          (∑ k ∈ Finset.univ.erase b0, (μB k) ^ N • mpvState (d := d) (B k) N) := by
  intro N
  have hN := hState N
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ b0), smul_add] at hN
  rw [hSelected N] at hN
  exact add_left_cancel hN

/-- **Reindexing a leading-erased weighted MPV-state tail.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. After removing
the already matched leading BNT component, the remaining components are viewed
again as a finite BNT family indexed by `Fin (r - 1)`. This lemma isolates the
finite reindexing of the corresponding weighted MPV-state sum. -/
lemma weighted_mpvState_sum_erase_zero_eq_sum_succ
    {d r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (hr : 0 < r) :
    ∀ N : ℕ,
      ∑ j ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r),
          (μ j) ^ N • mpvState (d := d) (A j) N =
        ∑ j : Fin (r - 1),
          (μ ⟨j.val + 1, by omega⟩) ^ N •
            mpvState (d := d) (A ⟨j.val + 1, by omega⟩) N := by
  intro N
  let succ : Fin (r - 1) → Fin r := fun j => ⟨j.val + 1, by omega⟩
  have succ_ne_zero : ∀ j, succ j ≠ (⟨0, hr⟩ : Fin r) := fun j => by
    simp [succ]
  have succ_inj : Function.Injective succ := fun j₁ j₂ h => by
    simp [succ, Fin.ext_iff] at h
    exact Fin.ext (by omega)
  have h_eq :
      Finset.univ.erase (⟨0, hr⟩ : Fin r) =
        (Finset.univ : Finset (Fin (r - 1))).image succ := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_erase] at hx
      have hx_ne : x ≠ (⟨0, hr⟩ : Fin r) := hx.1
      have hx_pos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx_ne (Fin.ext h))
      exact Finset.mem_image.mpr
        ⟨⟨x.val - 1, by omega⟩, Finset.mem_univ _,
          Fin.ext (by simp [succ]; omega)⟩
    · intro hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨succ_ne_zero j, Finset.mem_univ _⟩
  rw [h_eq, Finset.sum_image (fun j _ k _ h => succ_inj h)]

/-- **Projection of a fixed weighted MPV-state scalar sequence.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. Once the
proportionality scalars for the weighted assembled MPV-state sums have been
chosen, projecting against a fixed block MPV preserves the same scalar
sequence at every length. -/
lemma weighted_mpvInner_eq_mul_sequence_of_weighted_mpvState_eq_smul_sequence
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ)
    (hState : ∀ N : ℕ,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) :
    ∀ {D : ℕ} (X : MPSTensor d D) (N : ℕ),
      (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
        c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) := by
  intro D X N
  have hinner :=
    congrArg (fun v : MPVSpace d N => ⟪mpvState (d := d) X N, v⟫_ℂ) (hState N)
  simpa [mpvInner, inner_sum, inner_smul_right] using hinner

-- The fixed-length projection statement below is retained separately because
-- issue #1563 uses it before passing to the scalar sequence in the CPSV16
-- lines 1170--1192 block-selection contradiction.

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
  exact ⟨c, hc,
    weighted_mpvInner_eq_mul_sequence_of_weighted_mpvState_eq_smul_sequence
      A B c hstate X⟩

/-- **A scalar sequence for normalized proportional weighted projections.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. This records
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
