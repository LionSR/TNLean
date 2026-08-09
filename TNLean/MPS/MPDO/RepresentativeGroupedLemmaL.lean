/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.MPS.MPDO.BiCFDerivation.Core
import TNLean.MPS.SharedInfra.SectorDecomposition

/-!
# Representative-grouped form of Lemma L

For a canonical-form decomposition with repeated copies of a basis normal
tensor, the first-site action identity is grouped by the representative
index.  At length `N`, all copies of representative `j` contribute the single
coefficient
`P.coeff N j = \sum_q (P.weight j q)^N`.

The fixed-length theorem below separates these grouped contributions using a
finite simultaneous word-tuple span for the representative family.  The
all-representative theorem combines an eventual family of such finite spans
with the bounded nonvanishing power-sum lemma.  It therefore follows the
argument of arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858, while
keeping the still-unformalized canonical-form-to-finite-span implication as an
explicit hypothesis.
-/

open scoped Matrix BigOperators

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

/-- The length-`L` simultaneous word tuples of the basis representatives span
their full product matrix algebra.

This is the representative-level separation condition in the proof of Lemma L
of arXiv:1606.00608, Appendix C.3, lines 1848--1857.  It is imposed only on
the basis tensors `P.basis j`, not on their repeated copies. -/
def RepresentativeWordTupleSpanAt (P : SectorDecomposition d) (L : ℕ) : Prop :=
  WordTupleSpanTop P.basis L

/-- Representative word tuples span the full product algebra at every
sufficiently large length.

**Scope restriction (finite representative span):** the source obtains this
property from block injectivity of a minimal basis of normal tensors.  That
implication is not yet available from the abstract `SectorDecomposition`
structure and is therefore stated explicitly.  See
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`. -/
def EventuallyRepresentativeWordTupleSpan (P : SectorDecomposition d) : Prop :=
  ∃ L₀ : ℕ, ∀ L ≥ L₀, P.RepresentativeWordTupleSpanAt L

/-- At one separating length, a nonzero grouped coefficient lets Lemma L
identify the insertion on the chosen basis representative.

The copies over `j` enter only through
`P.coeff (L + 1) j = ∑_q (P.weight j q)^(L+1)`.  Thus gauge-equivalent
copies are grouped before the word-tuple separation is applied.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1848--1858. -/
theorem insertedTensor_basis_eq_of_firstSiteActionAgree_of_coeff_ne_zero
    (P : SectorDecomposition d) {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree P.toTensor Y Z)
    {L : ℕ} (hSpan : P.RepresentativeWordTupleSpanAt L)
    (j₀ : Fin P.basisCount) (hcoeff : P.coeff (L + 1) j₀ ≠ 0) :
    insertedTensor Y (P.basis j₀) = insertedTensor Z (P.basis j₀) := by
  classical
  funext s
  let Δ : (j : Fin P.basisCount) →
      Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ := fun j ↦
    P.coeff (L + 1) j •
      (insertedTensor Y (P.basis j) s - insertedTensor Z (P.basis j) s)
  have hΔzero : ∀ j, Δ j = 0 := by
    apply block_matrices_eq_zero_of_wordTupleSpanTop_trace P.basis hSpan Δ
    intro w
    have hA := hAct L (Fin.cons s w)
    have hsimp : ∀ i : Fin d,
        (Fin.cons i ((Fin.cons s w : Fin (L + 1) → Fin d) ∘ Fin.succ) :
            Fin (L + 1) → Fin d) = Fin.cons i w :=
      fun i ↦ by simp [Function.comp_def, Fin.cons_succ]
    simp only [Fin.cons_zero, hsimp] at hA
    have htrans : ∀ W : Matrix (Fin d) (Fin d) ℂ,
        ∑ i : Fin d, W s i * P.toTensor.mpv
            (Fin.cons i w : Fin (L + 1) → Fin d) =
          ∑ j : Fin P.basisCount, Matrix.trace
            (P.coeff (L + 1) j • insertedTensor W (P.basis j) s *
              evalWord (P.basis j) (List.ofFn w)) := by
      intro W
      have hExp : ∀ i : Fin d,
          P.toTensor.mpv (Fin.cons i w : Fin (L + 1) → Fin d) =
            ∑ j : Fin P.basisCount, P.coeff (L + 1) j *
              Matrix.trace (P.basis j i * evalWord (P.basis j) (List.ofFn w)) := by
        intro i
        rw [P.mpv_toTensor_eq_sum_coeff]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hof : List.ofFn (Fin.cons i w : Fin (L + 1) → Fin d) =
            i :: List.ofFn w := by
          simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        simp only [MPSTensor.mpv, MPSTensor.coeff, hof, MPSTensor.evalWord_cons]
      simp_rw [hExp, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      calc
        ∑ i : Fin d, W s i *
              (P.coeff (L + 1) j *
                Matrix.trace (P.basis j i * evalWord (P.basis j) (List.ofFn w))) =
            P.coeff (L + 1) j * ∑ i : Fin d, W s i *
              Matrix.trace (P.basis j i * evalWord (P.basis j) (List.ofFn w)) := by
                simpa only [mul_comm, mul_left_comm, mul_assoc] using
                  Fintype.sum_mul_mul_eq_mul_sum_mul (P.coeff (L + 1) j) (W s)
                    (fun i => Matrix.trace
                      (P.basis j i * evalWord (P.basis j) (List.ofFn w)))
        _ = P.coeff (L + 1) j * ∑ i : Fin d, Matrix.trace
              ((W s i • P.basis j i) * evalWord (P.basis j) (List.ofFn w)) := by
                congr 1
                refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
        _ = P.coeff (L + 1) j * Matrix.trace
              (∑ i : Fin d, (W s i • P.basis j i) *
                evalWord (P.basis j) (List.ofFn w)) := by
                rw [Matrix.trace_sum]
        _ = P.coeff (L + 1) j * Matrix.trace
              ((∑ i : Fin d, W s i • P.basis j i) *
                evalWord (P.basis j) (List.ofFn w)) := by
                rw [Finset.sum_mul]
        _ = P.coeff (L + 1) j * Matrix.trace
              (insertedTensor W (P.basis j) s *
                evalWord (P.basis j) (List.ofFn w)) := rfl
        _ = Matrix.trace
              (P.coeff (L + 1) j • insertedTensor W (P.basis j) s *
                evalWord (P.basis j) (List.ofFn w)) := by
                rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [htrans Y, htrans Z] at hA
    have hsubtr : ∀ j : Fin P.basisCount,
        Matrix.trace (Δ j * evalWord (P.basis j) (List.ofFn w)) =
          Matrix.trace
              (P.coeff (L + 1) j • insertedTensor Y (P.basis j) s *
                evalWord (P.basis j) (List.ofFn w)) -
            Matrix.trace
              (P.coeff (L + 1) j • insertedTensor Z (P.basis j) s *
                evalWord (P.basis j) (List.ofFn w)) := by
      intro j
      change Matrix.trace
          ((P.coeff (L + 1) j •
              (insertedTensor Y (P.basis j) s - insertedTensor Z (P.basis j) s)) *
            evalWord (P.basis j) (List.ofFn w)) = _
      rw [smul_sub, sub_mul, Matrix.trace_sub]
    simp_rw [hsubtr]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hA
  have hj := hΔzero j₀
  have hdiff : insertedTensor Y (P.basis j₀) s -
      insertedTensor Z (P.basis j₀) s = 0 :=
    (smul_eq_zero.mp hj).resolve_left hcoeff
  exact sub_eq_zero.mp hdiff

/-- Representative-grouped Lemma L under an explicit eventual finite-span
hypothesis.

For each representative `j`, apply the bounded power-sum lemma to the powered
weights `(P.weight j q)^(L₀+1)`.  It supplies a positive `r` such that the
coefficient at `N = (L₀+1)r` is nonzero.  Since `N-1 ≥ L₀`, the
representative word tuples at the required tail length separate the grouped
insertion difference.

**Scope restriction (finite representative span):** the only hypothesis not
contained in the abstract sector decomposition is
`EventuallyRepresentativeWordTupleSpan P`.  It is the finite word-span input
supplied by the source's block-injectivity proposition for a minimal basis of
normal tensors; deriving it from the full canonical-form hypotheses remains
open.  See `docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858. -/
theorem insertedTensor_basis_eq_of_firstSiteActionAgree
    (P : SectorDecomposition d) {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hSpan : P.EventuallyRepresentativeWordTupleSpan)
    (hAct : FirstSiteActionAgree P.toTensor Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  classical
  obtain ⟨L₀, hSpan⟩ := hSpan
  intro j
  let M := L₀ + 1
  obtain ⟨r, hrpos, _hrle, hsum⟩ :=
    Matrix.exists_sum_pow_ne_zero_of_pos_card
      (P.copies j) (fun q ↦ (P.weight j q) ^ M) (P.copies_pos j)
      (fun q ↦ pow_ne_zero M (P.weight_ne_zero j q))
  let N := M * r
  have hNpos : 0 < N := Nat.mul_pos (by simp [M]) hrpos
  have hcoeffN : P.coeff N j ≠ 0 := by
    change (∑ q : Fin (P.copies j), (P.weight j q) ^ N) ≠ 0
    simpa only [N, pow_mul] using hsum
  let L := N - 1
  have hLadd : L + 1 = N := by
    exact Nat.sub_add_cancel hNpos
  have hMleN : M ≤ N := by
    exact Nat.le_mul_of_pos_right M hrpos
  have hL₀leL : L₀ ≤ L := by
    dsimp [L, M] at hMleN ⊢
    omega
  apply P.insertedTensor_basis_eq_of_firstSiteActionAgree_of_coeff_ne_zero
    hAct (hSpan L hL₀leL) j
  rwa [hLadd]

/-- Transported representative-grouped Lemma L for an original tensor with
the same positive-length MPV family as the sector decomposition.

The finite representative-span restriction is unchanged.  Since a first-site
identity concerns chains of length `N + 1`, no length-zero coefficient is
needed.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858. -/
theorem insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree
    {D : ℕ} (A : MPSTensor d D) (P : SectorDecomposition d)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAP : SameMPV₂Pos A P.toTensor)
    (hSpan : P.EventuallyRepresentativeWordTupleSpan)
    (hAct : FirstSiteActionAgree A Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  exact P.insertedTensor_basis_eq_of_firstSiteActionAgree hSpan
    (hAct.of_sameMPVPos hAP)

end MPSTensor.SectorDecomposition
