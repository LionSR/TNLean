/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.Channel.PerronFrobenius.Existence
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Overlap.PeripheralToTransferMapGap
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank
import TNLean.MPS.Tactic.Basic

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Canonical form existence reductions from the source proofs

This file collects the arbitrary-tensor reductions toward the canonical-form construction for
MPS tensors from Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608.

The file contains the following reductions from arXiv:1606.00608 and the
translation-invariant canonical-form theorem of Pérez-García, Verstraete, Wolf,
and Cirac:

* arXiv:1606.00608, lines 201-219: iterated invariant-projection splitting gives an
  irreducible block decomposition.
* arXiv:1606.00608, lines 1058-1077: after canonical form has been obtained,
  the canonical-form-II gauge makes the associated maps trace-preserving and
  gives diagonal full-rank fixed points.
* Pérez-García, Verstraete, Wolf, and Cirac, proof of Theorem Th:TIcanonical,
  lines 765-770 and 827-832: the full-rank fixed-point gauge and the final
  dual fixed-point diagonalization.

We also keep a couple of formulations for already-normalized primitive / injective block families,
but those are **not** obtained from arbitrary input in this file.

Note: the Appendix-A CFII story is genuinely two-step:
first a generally non-unitary TP similarity from the adjoint Perron--Frobenius eigenvector,
then a unitary diagonalization **within** that TP gauge.

The reductions below are composed with finite-family weight normalization to
obtain the arbitrary-input positive-length PGVWC07 canonical form.  After a
positive global rescaling, the conclusion gives positive weights, unital blocks,
diagonal full-rank dual fixed points, scalar transfer-map fixed points, and the
bond-dimension bound.  If every positive-length MPV coefficient vanishes, the
nonzero-block family is empty.  The remaining all-zero direct summand $A_0$
separately records the length-zero dimension identity $D = D_0 + \sum_k D_k$.

The later Fundamental-Theorem reductions--TP gauge, period removal, common
blocking, and normal/BNT predicates--are subsequent consequences of the
canonical-form outputs, not missing conclusions of PGVWC07 Theorem
Th:TIcanonical.

Maintainer note: the blueprint cites
`MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty` in
`TNLean.MPS.CanonicalForm.NormalReduction.WeightNormalization`; the zero-tail
dimension identity is recorded by
`MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`
in `TNLean.MPS.CanonicalForm.NormalReduction.TPGauge`.  The audit boundary is
recorded in `docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`.
For Pérez-García, Verstraete, Wolf, and Cirac, the faithful proof order is the
one in `Papers/quant-ph_0608197/MPSarchive.tex`: lines 765–770 for
spectral-radius normalization and the full-rank fixed-point gauge, lines
771–815 for deriving the invariant support from a singular positive fixed point
and then splitting the trace, lines 816–826 for iteration and non-scalar
fixed-point splitting, and lines 827–832 for dual fixed-point diagonalization.

## External input — Quantum Wielandt strong irreducibility ⇒ full Kraus rank

This file imports `TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank`,
which supplies the hardest direction of the Quantum Wielandt primitivity equivalence:

> **Proposition 3(c)→(b) of arXiv:0909.5347 / Wolf Theorem 6.7 case (iii).**
> If `E_A` is **strongly irreducible** — the Kraus operators' word products
> eventually span the full matrix algebra `M_D(ℂ)` — then the fixed-point
> space of `E_A` has full Kraus rank: `dim S_1(A) = D` (the Kraus operators
> themselves span `M_D(ℂ)` at word-length `1`).

In MPS notation after blocking: `IsStronglyIrreducible A` (Kraus word products
eventually span `M_D(ℂ)`) implies `IsInjective A` (the single-site
Kraus operators `{A_i}` already span `M_D(ℂ)`).  This is a
step in the canonical-form existence argument: it upgrades the cumulative word
span to single-site injectivity, which then yields block injectivity at every
positive length.

The formal statement:

> `Wielandt.Primitivity.StronglyIrreducibleToFullRank` proves the implication
> `IsStronglyIrreduciblePaper A → krausRank A = D` (equivalently,
> `wordSpan A 1 = ⊤`).  This proves the hardest direction
> in the Sanz–Pérez-García–Wolf–Cirac primitivity equivalence.

## External input — invariant subspace decomposition in the canonical-form proof

The iterated invariant-projection splitting in arXiv:1606.00608, lines
201–219, is formalized in
`TNLean.MPS.Structure.InvariantSubspaceDecomp`.
This external input provides:

> **Pérez-García, Verstraete, Wolf, and Cirac, proof of Theorem
> Th:TIcanonical, lines 765–833.**
> An invariant orthogonal projection `P` on the bond space (satisfying
> `(1-P) A_i P = 0` for all `i`) yields an MPV-equivalent two-block direct-sum
> tensor with strictly smaller block dimensions.

The formal statement:

> `MPSTensor.exists_twoBlock_decomp_of_lowerZero` produces a two-block
> block-diagonal tensor MPV-equivalent to the original, with a strict dimension
> decrease (`exists_twoBlock_decomp_of_lowerZero_strict`).

## External input — Wolf spectral theory: Perron-Frobenius fixed point

The Appendix A PF/TP gauge step uses the Perron-Frobenius theorem for
completely positive maps (Wolf Chapter 6), formalized in
`TNLean.Channel.PerronFrobenius.Existence`:

> An irreducible CP map on `M_D(ℂ)` with spectral radius `1` has a
> positive-definite fixed point `ρ > 0`.  This provides the TP gauge
> transformation `A_i ↦ ρ^{1/2} A_i ρ^{-1/2}` that makes the
> tensor left-canonical.

The complementary transfer-map gap connection to peripheral primitivity is supplied by
`TNLean.MPS.Overlap.PeripheralToTransferMapGap` (Wolf Proposition 6.8).
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## (1) Irreducible block decomposition

We use `MPSTensor.exists_irreducible_blockDecomp` from `Reduction.lean` directly below.
-/


/-!
## (2) Perron–Frobenius / trace-preserving gauge for irreducible blocks

We use `MPSTensor.exists_tp_data_of_irreducible` from
`Channel/PerronFrobenius/Existence.lean` directly below.
-/


/-!
## (3) CFII normalization for irreducible trace-preserving blocks

We collect `exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor` together with the
fact that unitary conjugation preserves MPVs.

Important: this is the **second** half of the Appendix-A normalization story. The preceding
PF / TP-gauge step is generally a non-unitary similarity; the unitary appearing here acts only
after one has already moved into the one-sided TP gauge.
-/

/-- **CFII fixed-point normalization for irreducible trace-preserving blocks.**

For an irreducible tensor `A` in the TP gauge (`∑ Aᵢ†Aᵢ = I`) and with `0 < D`, there exist

* a unitary `U`,
* a diagonal positive-definite matrix `Λ`,

such that the unitary conjugate tensor
`B i := U† * A i * U` is still TP, has `Λ` as a fixed point of its transfer map, and is
`SameMPV₂`-equivalent to `A` (unitary gauge equivalence).

This is the formal analogue of bringing a block into **Canonical Form II** (CFII) *after*
one has already chosen a TP representative; it does not say that the original pre-TP-gauge tensor
is related to a CFII representative by a unitary similarity alone. -/
theorem exists_CFII_data_of_TP_of_isIrreducibleTensor
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hD : 0 < D) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ)
      (Λ : Matrix (Fin D) (Fin D) ℂ),
        let B : MPSTensor d D :=
          fun i =>
            (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ);
        SameMPV₂ A B ∧
        Λ.PosDef ∧ Λ.IsDiag ∧
        (∑ i : Fin d, (B i)ᴴ * (B i) = 1) ∧
        transferMap (d := d) (D := D) B Λ = Λ := by
  classical
  obtain ⟨U, Λ, hΛ_pd, hΛ_diag, hTP_conj, hΛ_fix⟩ :=
    exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor
      (d := d) (D := D) A hTP hIrr hD
  refine ⟨U, Λ, ?_⟩
  -- MPV is invariant under unitary conjugation.
  have hSame :
      SameMPV₂ A
        (fun i =>
          (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ)) := by
    intro N σ
    exact sameMPV_conj_unitary (d := d) (D := D) A U N σ
  -- Collect the statements under the `let B := ...` binder.
  exact ⟨hSame, hΛ_pd, hΛ_diag, hTP_conj, hΛ_fix⟩


/-!
## (4) Normality from primitive complementary-gap hypotheses

For overlap and canonical-form hypotheses involving primitive transfer maps, we use the results from
`PeripheralToTransferMapGap.lean` directly.
-/

/-!
## Zero-block vanishing at positive length

These are the first low-level facts needed for a complete treatment of zero blocks.
They show that an all-zero tensor contributes nothing on nonempty words, hence nothing to MPVs for
system sizes `N ≥ 1`. This still does **not** permit silently discarding zero scalar blocks under
`SameMPV₂`, because the `N = 0` sector continues to remember the total bond dimension.
-/

/-- An all-zero tensor evaluates to zero on every nonempty word. -/
theorem evalWord_eq_zero_of_all_zero (A : MPSTensor d D)
    (hzero : ∀ i : Fin d, A i = 0)
    (w : List (Fin d)) (hw : w ≠ []) :
    evalWord A w = 0 := by
  cases w with
  | nil =>
      exact (hw rfl).elim
  | cons i w =>
      simp only [evalWord, hzero i, zero_mul]

/-- An all-zero tensor contributes zero to the MPV for every positive system size. -/
theorem mpv_eq_zero_of_all_zero (A : MPSTensor d D)
    (hzero : ∀ i : Fin d, A i = 0)
    {N : ℕ} (σ : Fin N → Fin d) (hN : 0 < N) :
    mpv A σ = 0 := by
  have hw : List.ofFn σ ≠ [] := by
    intro hnil
    have hlen : N = 0 := by
      simpa [List.length_ofFn] using congrArg List.length hnil
    exact (Nat.ne_of_gt hN) hlen
  unfold mpv coeff
  rw [evalWord_eq_zero_of_all_zero (A := A) hzero (w := List.ofFn σ) hw]
  simp only [Matrix.trace_zero]

/-!
## Conditional reductions from arbitrary input

The arbitrary-input part of this file stops at the irreducible block decomposition and the
zero-block bookkeeping below. The irreducible-to-TP-gauge, CFII normalization, and
periodicity-removal theorems remain available for individual blocks satisfying their hypotheses,
but this file does not combine them into unconditional companions of the block decomposition.

The normal-canonical-form file starts from a primitive weighted block family with positive bond
dimensions and non-increasing nonzero weight moduli. This file does **not** construct that input
from an arbitrary tensor.

Remaining gap for a complete canonical-form existence theorem:

* Apply the irreducible-to-TP-gauge theorem blockwise through the irreducible block decomposition,
  with the length-zero contribution of possible zero blocks kept explicit.
* Apply the TP-irreducible-to-primitive blocking theorem and then perform the post-blocking cyclic
  sector bookkeeping and weight normalization needed for non-increasing nonzero weight moduli.
* Use the resulting data to reach the stronger normal / injective-by-blocking hypotheses needed by
  the normal-canonical-form lemmas and the `IsCanonicalForm` constructors.
-/

/-!
## Zero-block separation

The irreducible block decomposition may produce all-zero blocks. Because `SameMPV₂`
at `N = 0` includes the identity `trace(I_D) = D`, we cannot silently drop these.
Instead we accumulate them into a single **zero block** (called `zeroTailDim` in the
Lean formalization; the source paper says "there can be zero blocks" without assigning
a separate name). The zero-block dimension `zeroTailDim` is the sum of bond dimensions
of all zero blocks. The remaining **nonzero blocks** each have at least one nonzero
Kraus operator.

Key facts (matching the paper's canonical-form reduction, eq. II_Aiplusk1):
- For `N > 0`, all-zero blocks contribute `0` to the MPV (`mpv_eq_zero_of_all_zero`).
- For `N = 0`, each block of dimension `Dₖ` contributes `Dₖ` (the trace of the identity).

The all-zero blocks are not assembled into a separate tensor in the separation theorem
below: their total bond dimension is recorded as a plain natural number `zeroTailDim`, which
enters only through the length-zero dimension identity `D = zeroTailDim + ∑ k, dim k`.
-/

/-- **Zero-block separation.**

The paper states that in the canonical form $A^i = \oplus_{k=1}^r \mu_k A_k^i$, some blocks may
be zero: "there can be zero blocks." Every MPS tensor `A : MPSTensor d D` admits an irreducible
block decomposition that is faithfully partitioned into:

* a **zero-block dimension** `zeroTailDim`, equal to the sum of the bond dimensions of the
  all-zero irreducible blocks, and
* a family of **nonzero blocks** `blocks k : MPSTensor d (dim k)` for `k : Fin r`, each with at
  least one nonzero Kraus operator, positive bond dimension, and irreducibility.

The decomposition is recorded by two facts that together carry all the content:

* the positive-length equality `SameMPV₂Pos A (toTensorFromBlocks μ≡1 blocks)` (the all-zero
  blocks contribute nothing at positive length), and
* the length-zero dimension identity `D = zeroTailDim + ∑ k, dim k` (the empty-word coefficient
  is the bond dimension).

This separation is **exact**: the positive-length vectors see only the nonzero blocks, while the
length-zero identity D = D_0 + Σ_k D_k from the paper is preserved. -/
theorem exists_irreducible_blockDecomp_nonzeroBlocks (A : MPSTensor d D) :
    ∃ (zeroTailDim : ℕ) (r : ℕ) (dim : Fin r → ℕ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      (∀ k, ∃ i, blocks k i ≠ 0) ∧
      (∀ k, 0 < dim k) ∧
      SameMPV₂Pos A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) ∧
      D = zeroTailDim + ∑ k : Fin r, dim k := by
  classical
  -- Step 1: Obtain the irreducible block decomposition.
  obtain ⟨r₀, dim₀, blocks₀, hIrr₀, hSame₀⟩ :=
    exists_irreducible_blockDecomp (d := d) (D := D) A
  -- Step 2: Classify blocks as nonzero or zero.
  -- Name the nonzero-block predicate and the corresponding finite set.
  set isNonzero : Fin r₀ → Prop := fun k => ∃ i, blocks₀ k i ≠ 0 with isNonzero_def
  set nonzeroSet : Finset (Fin r₀) := Finset.univ.filter (fun k => isNonzero k)
    with nonzeroSet_def
  set zeroSet : Finset (Fin r₀) := Finset.univ.filter (fun k => ¬ isNonzero k)
    with zeroSet_def
  -- The all-zero summand dimension is the sum of bond dimensions of zero blocks.
  set zeroTailDim : ℕ := zeroSet.sum dim₀ with zeroTailDim_def
  -- Reindex nonzero blocks via a bijection with `Fin nonzeroSet.card`.
  set nonzeroEquiv : nonzeroSet ≃ Fin nonzeroSet.card := nonzeroSet.equivFin
    with nonzeroEquiv_def
  -- Define the new nonzero block family.
  set r := nonzeroSet.card with r_def
  set dim : Fin r → ℕ := fun j => dim₀ (nonzeroEquiv.symm j).1 with dim_def
  set newBlocks : (k : Fin r) → MPSTensor d (dim k) :=
    fun j => blocks₀ (nonzeroEquiv.symm j).1 with newBlocks_def
  -- The MPV of `A` decomposes into the nonzero-block direct sum plus the
  -- length-zero all-zero summand contribution.
  have key : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ =
        mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) newBlocks) σ +
          (if N = 0 then (zeroTailDim : ℂ) else 0) := by
    intro N σ
    -- Expand A's MPV via the original decomposition.
    have hA : mpv A σ = ∑ k : Fin r₀, mpv (blocks₀ k) σ := by
      have h := hSame₀ N σ
      rw [h, mpv_toTensorFromBlocks_eq_sum]
      simp only [one_pow, one_smul]
    -- Expand the nonzero-block toTensorFromBlocks.
    have hNonzero :
        mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) newBlocks) σ =
          ∑ j : Fin r, mpv (newBlocks j) σ := by
      rw [mpv_toTensorFromBlocks_eq_sum]
      simp only [one_pow, one_smul]
    -- Split the original sum into nonzero and zero parts.
    have hDisj : Disjoint nonzeroSet zeroSet := by
      simp only [nonzeroSet_def, zeroSet_def]
      exact Finset.disjoint_filter_filter_not _ _ _
    have hUnion : nonzeroSet ∪ zeroSet = Finset.univ := by
      simp only [nonzeroSet_def, zeroSet_def]
      ext k
      simp [Finset.mem_filter, Finset.mem_union, em]
    have hSplit : ∑ k : Fin r₀, mpv (blocks₀ k) σ =
        nonzeroSet.sum (fun k => mpv (blocks₀ k) σ) +
          zeroSet.sum (fun k => mpv (blocks₀ k) σ) := by
      rw [← Finset.sum_union hDisj, hUnion]
    -- The nonzero-block sum equals ∑ over the reindexed blocks.
    have hNonzeroSum : nonzeroSet.sum (fun k => mpv (blocks₀ k) σ) =
        ∑ j : Fin r, mpv (newBlocks j) σ := by
      rw [← nonzeroSet.sum_coe_sort (fun k => mpv (blocks₀ k) σ)]
      exact (nonzeroEquiv.symm.sum_comp
        (fun x : nonzeroSet => mpv (blocks₀ x.1) σ)).symm
    -- The zero sum: at N > 0, each zero block contributes 0; at N = 0, it contributes dim.
    have hZeroSum : zeroSet.sum (fun k => mpv (blocks₀ k) σ) =
        if N = 0 then (zeroTailDim : ℂ) else 0 := by
      split
      case isTrue hN =>
        subst hN
        -- Each block contributes `dim₀ k` at N=0 (trace of identity).
        have : zeroSet.sum (fun k => mpv (blocks₀ k) σ) =
            zeroSet.sum (fun k => (dim₀ k : ℂ)) :=
          Finset.sum_congr rfl (fun k _ => mpv_zero_length (blocks₀ k) σ)
        rw [this, ← Nat.cast_sum]
      case isFalse hN =>
        apply Finset.sum_eq_zero
        intro k hk
        have hkz : ∀ i, blocks₀ k i = 0 := by
          by_contra hne
          push Not at hne
          have hkNonzero : k ∈ nonzeroSet :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩
          exact absurd hkNonzero (Finset.disjoint_right.mp hDisj hk)
        exact mpv_eq_zero_of_all_zero (blocks₀ k) hkz σ (Nat.pos_of_ne_zero hN)
    -- Chain everything together.
    rw [hA, hSplit, hNonzeroSum, hZeroSum, hNonzero]
  -- Step 3: Prove all properties.
  refine ⟨zeroTailDim, r, dim, newBlocks, ?_, ?_, ?_, ?_, ?_⟩
  -- (a) Irreducibility of nonzero blocks.
  · intro k
    exact hIrr₀ (nonzeroEquiv.symm k).1
  -- (b) Each nonzero block has a nonzero Kraus operator.
  · intro k
    have hMem := (nonzeroEquiv.symm k).2
    -- Membership in `nonzeroSet` means `isNonzero`.
    have hNonzero : isNonzero (nonzeroEquiv.symm k).1 :=
      (Finset.mem_filter.mp hMem).2
    exact hNonzero
  -- (c) Each nonzero block has positive bond dimension.
  · intro k
    have hMem := (nonzeroEquiv.symm k).2
    have hNonzero : isNonzero (nonzeroEquiv.symm k).1 :=
      (Finset.mem_filter.mp hMem).2
    rcases hNonzero with ⟨i, hi⟩
    by_contra h
    push Not at h
    have hd0 : dim k = 0 := Nat.le_zero.mp h
    have hEmpty : IsEmpty (Fin (dim k)) := by rw [hd0]; infer_instance
    have hzero : newBlocks k i = 0 := by ext a b; exact (hEmpty.false a).elim
    exact hi hzero
  -- (d) Positive-length MPV relationship: the zero tail vanishes for `N > 0`.
  · intro N hN σ
    have hkey := key N σ
    rw [if_neg (Nat.ne_of_gt hN), add_zero] at hkey
    exact hkey
  -- (e) Length-zero dimension identity: the empty-word coefficient is the bond dimension.
  · have h0 := key 0 (Fin.elim0 : Fin 0 → Fin d)
    rw [if_pos rfl, mpv_zero_length, mpv_zero_length] at h0
    -- `h0 : (D : ℂ) = (∑ k, dim k : ℂ) + (zeroTailDim : ℂ)`
    have hnat : D = (∑ k : Fin r, dim k) + zeroTailDim := by exact_mod_cast h0
    omega

end MPSTensor
