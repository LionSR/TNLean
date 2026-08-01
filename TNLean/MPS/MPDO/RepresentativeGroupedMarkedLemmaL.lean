/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.MPS.MPDO.PostBlockedRepresentativeSpan

/-!
# Representative-grouped separation with an arbitrary marked letter

A marked direct sum permits the first matrix in each representative chain to
be arbitrary, while every subsequent matrix comes from the unmarked sector
tensor.  Equality of such closed marked chains at every positive tail length separates the marked
matrices representative by representative.

The proof first treats one length at which the simultaneous representative
word tuples span the product matrix algebra.  A bounded nonvanishing power
sum then selects a sufficiently large separating length for each
representative.

Lemma L in arXiv:1606.00608, lines 1835--1858, is stated for matrices induced
by physical operators on the first site.  After the closed-chain identity has
been expanded, however, its separation calculation uses only the matrices in
the marked slot.  The theorems below record that algebraic extension.  They do
not assert that the paper states Lemma L for arbitrary marked matrices.  In
the application to Figures 7 and 8, the marks must still be constructed from
the actual grouped vertical corners.

## Main results

* `SectorDecomposition.markedTensor_basis_eq_of_trace_agree_of_coeff_ne_zero`:
  separation at one length with a nonzero grouped coefficient.
* `SectorDecomposition.markedTensor_basis_eq_of_trace_agree`: separation under
  eventual simultaneous representative word-tuple span.
* `IsBNTCanonicalForm.markedTensor_basis_eq_of_trace_agree`: separation from
  the BNT canonical-form hypotheses.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.3, lines 1835--1858, and Proposition 4.13, lines 1909--1919.
-/

open scoped Matrix BigOperators

namespace MPSTensor.SectorDecomposition

variable {d e : ℕ}

/-- At one separating tail length, a nonzero grouped coefficient identifies
an arbitrary marked letter on the chosen representative.

For marked families `C` and `E`, equality of their closed chains against the
same sector-decomposition tail gives
`P.coeff (L + 1) j • (C j s - E j s) = 0` for every representative `j`.
Representative word-tuple separation and a nonzero coefficient at `j₀` then
give `C j₀ = E j₀`.

This is the algebraic extension of the separation calculation in
arXiv:1606.00608, Appendix C.3, lines 1848--1858.  The source states the
physical-insertion case; the unrestricted marked matrices here are an
auxiliary consequence of the same calculation. -/
theorem markedTensor_basis_eq_of_trace_agree_of_coeff_ne_zero
    (P : SectorDecomposition d)
    (C E : (j : Fin P.basisCount) → MPSTensor e (P.basisDim j))
    {L : ℕ} (hSpan : P.RepresentativeWordTupleSpanAt L)
    (hTrace : ∀ (s : Fin e) (w : Fin L → Fin d),
      Matrix.trace (P.markedTensor C s * evalWord P.toTensor (List.ofFn w)) =
        Matrix.trace (P.markedTensor E s * evalWord P.toTensor (List.ofFn w)))
    (j₀ : Fin P.basisCount) (hcoeff : P.coeff (L + 1) j₀ ≠ 0) :
    C j₀ = E j₀ := by
  classical
  funext s
  let Δ : (j : Fin P.basisCount) →
      Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ := fun j ↦
    P.coeff (L + 1) j • (C j s - E j s)
  have hΔzero : ∀ j, Δ j = 0 := by
    apply block_matrices_eq_zero_of_wordTupleSpanTop_trace P.basis hSpan Δ
    intro w
    have h := hTrace s w
    rw [P.trace_markedTensor_mul_evalWord C s (List.ofFn w),
      P.trace_markedTensor_mul_evalWord E s (List.ofFn w)] at h
    simp only [List.length_ofFn] at h
    have hsubtr : ∀ j : Fin P.basisCount,
        Matrix.trace (Δ j * evalWord (P.basis j) (List.ofFn w)) =
          P.coeff (L + 1) j *
              Matrix.trace (C j s * evalWord (P.basis j) (List.ofFn w)) -
            P.coeff (L + 1) j *
              Matrix.trace (E j s * evalWord (P.basis j) (List.ofFn w)) := by
      intro j
      change Matrix.trace
          ((P.coeff (L + 1) j • (C j s - E j s)) *
            evalWord (P.basis j) (List.ofFn w)) = _
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul,
        Matrix.trace_sub, mul_sub]
    simp_rw [hsubtr]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact h
  have hj := hΔzero j₀
  have hdiff : C j₀ s - E j₀ s = 0 :=
    (smul_eq_zero.mp hj).resolve_left hcoeff
  exact sub_eq_zero.mp hdiff

/-- Equality of closed marked chains at every positive tail length identifies the marked tensor on
every representative under eventual representative word-tuple separation.

For each representative, the bounded nonvanishing power-sum theorem selects
a strictly positive, sufficiently large tail length at which its grouped coefficient is nonzero.
The fixed-length marked separation theorem then applies.

This is the algebraic extension of arXiv:1606.00608, Appendix C.3,
lines 1835--1858.  The source states the physical-insertion case; the
unrestricted marked matrices here are an auxiliary consequence of its
trace-separation proof. -/
theorem markedTensor_basis_eq_of_trace_agree
    (P : SectorDecomposition d)
    (C E : (j : Fin P.basisCount) → MPSTensor e (P.basisDim j))
    (hSpan : P.EventuallyRepresentativeWordTupleSpan)
    (hTrace : ∀ (L : ℕ), 0 < L → ∀ (s : Fin e) (w : Fin L → Fin d),
      Matrix.trace (P.markedTensor C s * evalWord P.toTensor (List.ofFn w)) =
        Matrix.trace (P.markedTensor E s * evalWord P.toTensor (List.ofFn w))) :
    ∀ j, C j = E j := by
  classical
  obtain ⟨L₀, hSpan⟩ := hSpan
  intro j
  let M := L₀ + 2
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
  have hLadd : L + 1 = N := Nat.sub_add_cancel hNpos
  have hMleN : M ≤ N := Nat.le_mul_of_pos_right M hrpos
  have hL₀leL : L₀ ≤ L := by
    dsimp [L, M] at hMleN ⊢
    omega
  have hLpos : 0 < L := by
    dsimp [L, M] at hMleN ⊢
    omega
  apply P.markedTensor_basis_eq_of_trace_agree_of_coeff_ne_zero C E
    (hSpan L hL₀leL) (hTrace L hLpos) j
  rwa [hLadd]

end MPSTensor.SectorDecomposition

namespace MPSTensor.IsBNTCanonicalForm

variable {d e : ℕ} {P : SectorDecomposition d}

/-- Equality of closed marked chains at every positive tail length identifies
arbitrary marked letters on every representative of a BNT canonical form.

The BNT hypotheses give eventual simultaneous representative word-tuple span.
The algebraic marked-letter extension of the representative-grouped
separation argument then separates the marked tensors.

The representative span is from arXiv:1606.00608, lines 318--344, and the
separation calculation is Appendix C.3, lines 1848--1858.  The source states
the latter for physical first-site insertions; the arbitrary marked matrices
are an auxiliary algebraic extension. -/
theorem markedTensor_basis_eq_of_trace_agree
    (hCF : IsBNTCanonicalForm P)
    (C E : (j : Fin P.basisCount) → MPSTensor e (P.basisDim j))
    (hTrace : ∀ (L : ℕ), 0 < L → ∀ (s : Fin e) (w : Fin L → Fin d),
      Matrix.trace (P.markedTensor C s * evalWord P.toTensor (List.ofFn w)) =
        Matrix.trace (P.markedTensor E s * evalWord P.toTensor (List.ofFn w))) :
    ∀ j, C j = E j := by
  exact P.markedTensor_basis_eq_of_trace_agree C E
    hCF.eventuallyRepresentativeWordTupleSpan hTrace

end MPSTensor.IsBNTCanonicalForm
