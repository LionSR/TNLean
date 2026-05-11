/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.BNT.Basic
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
open Filter

namespace MPSTensor

section ProportionalExpansion

/-- **Fixed-length weighted MPV-state proportionality from assembled block tensors.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. At a fixed length
`N`, proportionality of the two assembled tensors expands into proportionality
of the two weighted BNT block sums at that same length. This is the fixed-length
form used before passing to scalar sequences or eventual tail reductions. -/
lemma exists_weighted_mpvState_eq_smul_of_nonzeroProportional_at_length_toTensorFromBlocks
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (N : ℕ)
    (hN : ∃ c : ℂ, c ≠ 0 ∧
      ∀ σ : Fin N → Fin d,
        mpv (toTensorFromBlocks μA A) σ = c * mpv (toTensorFromBlocks μB B) σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := by
  rcases hN with ⟨c, hc, hN⟩
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
  exact exists_weighted_mpvState_eq_smul_of_nonzeroProportional_at_length_toTensorFromBlocks
    A B N (hProp N)

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

/-- **An eventual scalar sequence for eventually proportional weighted MPV-state sums.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182 uses Lemma
`Lem1`, hence only sufficiently large chain lengths enter the contradiction.
This lemma is the eventual version of the preceding scalar-sequence
bookkeeping: eventual nonzero proportionality of the assembled tensors gives an
eventual nonzero scalar sequence for the expanded weighted BNT block sums. -/
lemma exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ c : ℕ → ℂ, (∀ᶠ N in atTop, c N ≠ 0) ∧
      ∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := by
  classical
  let P : ℕ → Prop := fun N =>
    ∃ c : ℂ, c ≠ 0 ∧
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)
  have hWeighted : ∀ᶠ N in atTop, P N := by
    refine hProp.mono ?_
    intro N hN
    exact
      exists_weighted_mpvState_eq_smul_of_nonzeroProportional_at_length_toTensorFromBlocks
        A B N hN
  let c : ℕ → ℂ := fun N => if hN : P N then Classical.choose hN else 1
  refine ⟨c, ?_, ?_⟩
  · refine hWeighted.mono ?_
    intro N hN
    dsimp [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).1
  · refine hWeighted.mono ?_
    intro N hN
    dsimp [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).2

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

/-- **Eventual proportionality from an eventual weighted MPV-state scalar sequence.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. After a finite
number of leading BNT components has been removed, Lemma `Lem1` supplies
linear independence only for sufficiently large lengths. This bookkeeping lemma
turns an eventual weighted MPV-state identity into eventual nonzero
proportionality of the assembled tail tensors. -/
lemma eventuallyNonzeroProportionalMPV₂_toTensorFromBlocks_of_eventually_weighted_mpvState
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (hc : ∀ᶠ N in atTop, c N ≠ 0)
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) :
    EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B) := by
  refine (hc.and hState).mono ?_
  intro N hN
  rcases hN with ⟨hcN, hStateN⟩
  refine ⟨c N, hcN, fun σ => ?_⟩
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
  have hNσ := congrArg (fun v : MPVSpace d N => v σ) hStateN
  have hAcoeff :=
    mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μA) (A := A) σ
  have hBcoeff :=
    mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μB) (A := B) σ
  calc
    mpv (toTensorFromBlocks μA A) σ =
        ∑ j : Fin rA, (μA j) ^ N * mpv (A j) σ := by
          simpa [smul_eq_mul] using hAcoeff
    _ = c N * (∑ k : Fin rB, (μB k) ^ N * mpv (B k) σ) := by
      simpa [mpvState_apply, hAstate, hBstate, Pi.smul_apply, smul_eq_mul] using hNσ
    _ = c N * (∑ k : Fin rB, (μB k) ^ N • mpv (B k) σ) := by
      simp [smul_eq_mul]
    _ = c N * mpv (toTensorFromBlocks μB B) σ := by
      rw [← hBcoeff]

/-- **Selected coefficient extraction from an eventual two-family relation.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182 invokes Lemma
`Lem1`. Once the selected block on one side has been rewritten as a phase
multiple of the selected block on the other side, Lemma `Lem1` supplies
eventual linear independence for the remaining two-family list. This lemma is
the coefficient bookkeeping for that step: equality of the two finite linear
combinations forces the coefficient of the selected vector to agree
eventually. -/
lemma eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : ℕ → Type*} [∀ N, AddCommGroup (E N)] [∀ N, Module ℂ (E N)]
    (v : (N : ℕ) → ι → E N) (w : (N : ℕ) → κ → E N)
    (a : ℕ → ι → ℂ) (b₀ : ℕ → ℂ) (b : ℕ → κ → ℂ)
    (i₀ : ι)
    (hLI : ∀ᶠ N in atTop, LinearIndependent ℂ (Sum.elim (v N) (w N)))
    (hEq : ∀ᶠ N in atTop,
      ∑ i : ι, a N i • v N i =
        b₀ N • v N i₀ + ∑ k : κ, b N k • w N k) :
    ∀ᶠ N in atTop, a N i₀ = b₀ N := by
  classical
  let lhs : (N : ℕ) → Sum ι κ → ℂ := fun N =>
    Sum.elim (a N) (fun _ => 0)
  let rhs : (N : ℕ) → Sum ι κ → ℂ := fun N =>
    Sum.elim (fun i => if i = i₀ then b₀ N else 0) (b N)
  have hEqSum :
      ∀ᶠ N in atTop,
        ∑ x : Sum ι κ, lhs N x • Sum.elim (v N) (w N) x =
          ∑ x : Sum ι κ, rhs N x • Sum.elim (v N) (w N) x := by
    refine hEq.mono ?_
    intro N hN
    simp [lhs, rhs, Fintype.sum_sum_type, hN]
  have hCoeff :=
    coefficient_eventually_eq_of_eventually_linearIndependent
      (fun N => Sum.elim (v N) (w N)) lhs rhs hLI hEqSum
  refine hCoeff.mono ?_
  intro N hN
  simpa [lhs, rhs] using hN (Sum.inl i₀)

/-- **Selected weighted summand from phase and coefficient equality.**

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. After a
non-decaying block pair has supplied a phase relation between the two MPV
families, the coefficient comparison identifies the corresponding weighted
summands. This is only the algebraic bridge from the phase relation and the
eventual coefficient identity to the selected-summand identity used before
erasing matched blocks. -/
lemma eventually_selected_weighted_mpvState_eq_smul_of_phase_and_coeff
    {d DA DB : ℕ} {μA μB ζ : ℂ} {c : ℕ → ℂ}
    (A : MPSTensor d DA) (B : MPSTensor d DB)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) B N = ζ ^ N • mpvState (d := d) A N)
    (hCoeff : ∀ᶠ N in atTop, μA ^ N = c N * (μB * ζ) ^ N) :
    ∀ᶠ N in atTop,
      μA ^ N • mpvState (d := d) A N =
        c N • (μB ^ N • mpvState (d := d) B N) := by
  refine hCoeff.mono ?_
  intro N hN
  calc
    μA ^ N • mpvState (d := d) A N =
        (c N * (μB * ζ) ^ N) • mpvState (d := d) A N := by
          rw [hN]
    _ = c N • (μB ^ N • mpvState (d := d) B N) := by
      rw [hPhase N, mul_pow, smul_smul, smul_smul]
      congr 1
      ring

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

/-- **Eventual subtraction of a proportional selected summand.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. The recursive
block-selection argument uses Lemma `Lem1`, so tail identities produced after
coefficient extraction are needed only for sufficiently large lengths. This is
the eventual analogue of
`weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected`. -/
lemma eventually_weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (a0 : Fin rA) (b0 : Fin rB)
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (hSelected : ∀ᶠ N in atTop,
      (μA a0) ^ N • mpvState (d := d) (A a0) N =
        c N • ((μB b0) ^ N • mpvState (d := d) (B b0) N)) :
    ∀ᶠ N in atTop,
      ∑ j ∈ Finset.univ.erase a0, (μA j) ^ N • mpvState (d := d) (A j) N =
        c N •
          (∑ k ∈ Finset.univ.erase b0, (μB k) ^ N • mpvState (d := d) (B k) N) := by
  refine (hState.and hSelected).mono ?_
  intro N hN
  rcases hN with ⟨hStateN, hSelectedN⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ b0), smul_add] at hStateN
  rw [hSelectedN] at hStateN
  exact add_left_cancel hStateN

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

/-- **Reindexing an arbitrary erased weighted MPV-state tail.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. The proof may
remove a matched block pair that is not the leading pair, because the theorem
allows a permutation of BNT blocks. This lemma identifies the weighted
MPV-state sum over the complement of an arbitrary selected block with the
corresponding sum over `Fin n`, using `Fin.succAbove` to preserve the remaining
order. -/
lemma weighted_mpvState_sum_erase_eq_sum_succAbove
    {d n : ℕ} {dim : Fin (n + 1) → ℕ} {μ : Fin (n + 1) → ℂ}
    (A : (j : Fin (n + 1)) → MPSTensor d (dim j))
    (a0 : Fin (n + 1)) :
    ∀ N : ℕ,
      ∑ j ∈ Finset.univ.erase a0,
          (μ j) ^ N • mpvState (d := d) (A j) N =
        ∑ j : Fin n,
          (μ (a0.succAbove j)) ^ N •
            mpvState (d := d) (A (a0.succAbove j)) N := by
  intro N
  have h_eq :
      Finset.univ.erase a0 =
        (Finset.univ : Finset (Fin n)).image a0.succAbove := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_erase] at hx
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx.1
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    · intro hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne _ _, Finset.mem_univ _⟩
  rw [h_eq, Finset.sum_image (fun _ _ _ _ h => Fin.succAbove_right_injective h)]

/-- **Eventual proportionality of reindexed tails after removing the leading summand.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. After a leading
matched BNT component has been removed, the remaining components are reindexed
and the argument is repeated. This lemma packages that bookkeeping in eventual
form: an eventual total weighted-state identity, together with an eventual
selected-summand identity for the leading components, gives eventual nonzero
proportionality of the two reindexed tail tensors. -/
lemma eventuallyNonzeroProportionalMPV₂_tail_succ_of_total_and_selected
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (hrA : 0 < rA) (hrB : 0 < rB)
    (hc : ∀ᶠ N in atTop, c N ≠ 0)
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (hSelected : ∀ᶠ N in atTop,
      (μA (⟨0, hrA⟩ : Fin rA)) ^ N •
          mpvState (d := d) (A (⟨0, hrA⟩ : Fin rA)) N =
        c N •
          ((μB (⟨0, hrB⟩ : Fin rB)) ^ N •
            mpvState (d := d) (B (⟨0, hrB⟩ : Fin rB)) N)) :
    EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks
        (fun j : Fin (rA - 1) => μA ⟨j.val + 1, by omega⟩)
        (fun j : Fin (rA - 1) => A ⟨j.val + 1, by omega⟩))
      (toTensorFromBlocks
        (fun k : Fin (rB - 1) => μB ⟨k.val + 1, by omega⟩)
        (fun k : Fin (rB - 1) => B ⟨k.val + 1, by omega⟩)) := by
  let a0 : Fin rA := ⟨0, hrA⟩
  let b0 : Fin rB := ⟨0, hrB⟩
  have hTailErase :
      ∀ᶠ N in atTop,
        ∑ j ∈ Finset.univ.erase a0,
            (μA j) ^ N • mpvState (d := d) (A j) N =
          c N •
            (∑ k ∈ Finset.univ.erase b0,
              (μB k) ^ N • mpvState (d := d) (B k) N) := by
    exact eventually_weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected
      A B c a0 b0 hState (by simpa [a0, b0] using hSelected)
  have hTailReindex :
      ∀ᶠ N in atTop,
        (∑ j : Fin (rA - 1),
            (μA ⟨j.val + 1, by omega⟩) ^ N •
              mpvState (d := d) (A ⟨j.val + 1, by omega⟩) N) =
          c N •
            (∑ k : Fin (rB - 1),
              (μB ⟨k.val + 1, by omega⟩) ^ N •
                mpvState (d := d) (B ⟨k.val + 1, by omega⟩) N) := by
    refine hTailErase.mono ?_
    intro N hN
    rw [weighted_mpvState_sum_erase_zero_eq_sum_succ A hrA N] at hN
    rw [weighted_mpvState_sum_erase_zero_eq_sum_succ B hrB N] at hN
    exact hN
  exact
    eventuallyNonzeroProportionalMPV₂_toTensorFromBlocks_of_eventually_weighted_mpvState
      (fun j : Fin (rA - 1) => A ⟨j.val + 1, by omega⟩)
      (fun k : Fin (rB - 1) => B ⟨k.val + 1, by omega⟩)
      c hc hTailReindex

/-- **Eventual proportionality of reindexed tails after an arbitrary matched block.**

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. The
source proof permits a permutation of BNT blocks: after a block pair has been
matched and its weighted summands have been identified, one removes that pair
and repeats the argument on the two complements. This lemma packages only the
finite reindexing and eventual-proportionality bookkeeping for that step. -/
lemma eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_total_and_selected
    {d nA nB : ℕ}
    {dimA : Fin (nA + 1) → ℕ} {dimB : Fin (nB + 1) → ℕ}
    {μA : Fin (nA + 1) → ℂ} {μB : Fin (nB + 1) → ℂ}
    (A : (j : Fin (nA + 1)) → MPSTensor d (dimA j))
    (B : (k : Fin (nB + 1)) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (a0 : Fin (nA + 1)) (b0 : Fin (nB + 1))
    (hc : ∀ᶠ N in atTop, c N ≠ 0)
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin (nA + 1), (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N •
          (∑ k : Fin (nB + 1), (μB k) ^ N • mpvState (d := d) (B k) N))
    (hSelected : ∀ᶠ N in atTop,
      (μA a0) ^ N • mpvState (d := d) (A a0) N =
        c N • ((μB b0) ^ N • mpvState (d := d) (B b0) N)) :
    EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks
        (fun j : Fin nA => μA (a0.succAbove j))
        (fun j : Fin nA => A (a0.succAbove j)))
      (toTensorFromBlocks
        (fun k : Fin nB => μB (b0.succAbove k))
        (fun k : Fin nB => B (b0.succAbove k))) := by
  have hTailErase :
      ∀ᶠ N in atTop,
        ∑ j ∈ Finset.univ.erase a0,
            (μA j) ^ N • mpvState (d := d) (A j) N =
          c N •
            (∑ k ∈ Finset.univ.erase b0,
              (μB k) ^ N • mpvState (d := d) (B k) N) := by
    exact eventually_weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected
      A B c a0 b0 hState hSelected
  have hTailReindex :
      ∀ᶠ N in atTop,
        (∑ j : Fin nA,
            (μA (a0.succAbove j)) ^ N •
              mpvState (d := d) (A (a0.succAbove j)) N) =
          c N •
            (∑ k : Fin nB,
              (μB (b0.succAbove k)) ^ N •
                mpvState (d := d) (B (b0.succAbove k)) N) := by
    refine hTailErase.mono ?_
    intro N hN
    rw [weighted_mpvState_sum_erase_eq_sum_succAbove A a0 N] at hN
    rw [weighted_mpvState_sum_erase_eq_sum_succAbove B b0 N] at hN
    exact hN
  exact
    eventuallyNonzeroProportionalMPV₂_toTensorFromBlocks_of_eventually_weighted_mpvState
      (fun j : Fin nA => A (a0.succAbove j))
      (fun k : Fin nB => B (b0.succAbove k))
      c hc hTailReindex

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

/-- **Eventual projection of a weighted MPV-state scalar sequence.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. After Lemma
`Lem1` is used, the relevant weighted-state identity is only needed for all
sufficiently large lengths; projection against a fixed block MPV preserves the
same eventual scalar sequence. -/
lemma eventually_weighted_mpvInner_eq_mul_sequence_of_eventually_weighted_mpvState_eq_smul_sequence
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ)
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) :
    ∀ {D : ℕ} (X : MPSTensor d D),
      ∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
          c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) := by
  intro D X
  refine hState.mono ?_
  intro N hN
  have hinner :=
    congrArg (fun v : MPVSpace d N => ⟪mpvState (d := d) X N, v⟫_ℂ) hN
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

/-- **An eventual scalar sequence for proportional weighted MPV projections.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. This is the
projection form of the eventual weighted-state scalar sequence obtained after
applying the sufficiently-large-length linear-independence input `Lem1`. -/
lemma exists_eventually_weighted_mpvInner_eq_mul_sequence_of_eventuallyNonzeroProportionalMPV₂
    {d rA rB D : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (X : MPSTensor d D) :
    ∃ c : ℕ → ℂ, (∀ᶠ N in atTop, c N ≠ 0) ∧
      ∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
          c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N) := by
  obtain ⟨c, hc, hstate⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  exact ⟨c, hc,
    eventually_weighted_mpvInner_eq_mul_sequence_of_eventually_weighted_mpvState_eq_smul_sequence
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

/-- **An eventual scalar sequence for normalized proportional weighted projections.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. In the recursive
tail-reduction stage the proportionality of the assembled tail tensors is only
eventual. After choosing the eventual scalar sequence, the normalized projected
weighted sums are still related by the same adjusted scalar for all
sufficiently large lengths. -/
lemma exists_eventually_adjusted_weighted_mpvInner_sequence_of_eventuallyNonzeroProportionalMPV₂
    {d rA rB D : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (X : MPSTensor d D) (μ ν : ℂ) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    ∃ c : ℕ → ℂ, (∀ᶠ N in atTop, c N ≠ 0) ∧
      ∀ᶠ N in atTop,
        (μ ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
          (c N * (ν / μ) ^ N) *
            ((ν ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)) := by
  obtain ⟨c, hc, hinner⟩ :=
    exists_eventually_weighted_mpvInner_eq_mul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp X
  refine ⟨c, hc, ?_⟩
  refine hinner.mono ?_
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

end ProportionalExpansion

end MPSTensor
