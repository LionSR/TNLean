/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion

/-!
# Weak existential non-decaying-overlap pair on the `_CFBNT` surface

This module records the issue #1678 **full combined-family Lem1** route on the
`IsCanonicalFormBNT` surface in its weakest existential form.  The result is
that under eventual nonzero proportionality of the assembled tensors, **some**
pair `(j, k)` of BNT blocks has a non-decaying overlap.

The proof is the canonical combined-family contradiction recommended by issue
#1678:

* the contrapositive assumption gives that **all** pairwise A–B overlaps decay
  to zero;
* the building block
  `eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal`
  (`TNLean.MPS.BNT.Basic`, line 195) then promotes the assembled families
  `{V^{(N)}(A_j)}_j ∪ {V^{(N)}(B_k)}_k` to **eventual linear independence**;
* the scalar sequence
  `exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂`
  (`TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion`) converts the
  proportionality identity into a single linear combination of the combined
  family that is eventually zero;
* `coefficient_eventually_eq_of_eventually_linearIndependent`
  (`TNLean.MPS.BNT.Basic`, line 172) forces every coefficient to vanish, and
  in particular forces `c N · (μ_B 0)^N = 0`, contradicting the nonzero scalar
  witness and the nonvanishing dominant `B`-weight.

The result here is the **weak existential** form `∃ j, ∃ k, ...`.  Promoting
this to the conjunction `(∀ j, ∃ k, ...) ∧ (∀ k, ∃ j, ...)` used by the
dispatcher `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` is a
separate exercise and is intentionally not done here.

## References

* Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and Boundary
  Theories*, arXiv:1606.00608 (2017), Theorem `thm1`, lines 1170--1192;
  Corollary `Lem1`, lines 1130--1133.
* Issue #1678 (TNLean repository): analysis of the combined-family Lem1 route
  for the proportional fundamental-theorem stage.

## Tags

matrix product states, fundamental theorem, BNT, linear independence,
coefficient comparison
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section CombinedLIWeakExistential

/-- **Weak non-decaying-overlap existence for proportional `_CFBNT` families.**

For two `IsCanonicalFormBNT` families whose assembled total tensors are
eventually nonzero-proportionally related (`EventuallyNonzeroProportionalMPV₂`),
there exists **some** pair `(j, k)` of BNT blocks whose pairwise overlap does
not decay to zero.

This is the natural conclusion of the issue #1678 combined-family Lem1 +
coefficient-comparison route.  The proof assumes — for contradiction — that
all pairwise A–B overlaps decay, then applies
`eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal`
(`TNLean.MPS.BNT.Basic`, line 195) to obtain eventual linear independence of
the combined family `{V^{(N)}(A_j)}_j ∪ {V^{(N)}(B_k)}_k`, packages the
proportionality identity from
`exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂`
as a single linear relation on that combined family, and uses
`coefficient_eventually_eq_of_eventually_linearIndependent`
(`TNLean.MPS.BNT.Basic`, line 172) to force every coefficient to vanish.
Specialising the coefficient comparison at the dominant `B`-block index
`⟨0, _⟩` and combining with the nonzero scalar sequence and nonvanishing
dominant weight `μ_B 0` yields a contradiction.

**Scope restriction (one-copy-per-sector).** The local hypothesis
`IsCanonicalFormBNT` is the already-grouped one-copy-per-sector canonical
form.  CPSV16 (arXiv:1606.00608) allows BNT multiplicities inside a sector.
This restriction is documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma exists_nondecaying_overlap_pair_of_nonzeroProportionalMPV₂_CFBNT
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
    ∃ j : Fin rA, ∃ k : Fin rB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  classical
  -- `hrA` is recorded in the statement for symmetry with the dispatcher hypothesis
  -- shape; only `hrB` (via `hrB_pos`) is needed in this proof.
  let _hrA_unused := hrA
  by_contra hcontra
  push Not at hcontra
  -- `hcontra : ∀ j k, Tendsto (overlap (A j) (B k)) → 0`.
  have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB
  -- Self-overlap and internal cross-overlap data from `IsCanonicalFormBNT`.
  have hA_self : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds 1) :=
    hA.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_self : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1) :=
    hB.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hA_off : ∀ i j : Fin rA, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0) :=
    hA.cross_overlap_tendsto_zero
  have hB_off : ∀ i j : Fin rB, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (B i) (B j) N) atTop (nhds 0) :=
    hB.cross_overlap_tendsto_zero
  -- Combined-family Lem1: eventual LI of `Sum.elim (mpvState A) (mpvState B)`.
  have hLI :
      ∀ᶠ N in atTop,
        LinearIndependent ℂ
          (Sum.elim
            (fun j : Fin rA => mpvState (d := d) (A j) N)
            (fun k : Fin rB => mpvState (d := d) (B k) N)) :=
    eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal
      A B hA_self hA_off hB_self hB_off hcontra
  -- Scalar sequence from eventual nonzero proportionality.
  obtain ⟨c, hc_ne, hState⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  -- Package the proportionality identity as a `Sum.elim`-shaped linear relation.
  let v : (N : ℕ) → Sum (Fin rA) (Fin rB) → MPVSpace d N := fun N =>
    Sum.elim
      (fun j : Fin rA => mpvState (d := d) (A j) N)
      (fun k : Fin rB => mpvState (d := d) (B k) N)
  let α : ℕ → Sum (Fin rA) (Fin rB) → ℂ := fun N =>
    Sum.elim (fun j : Fin rA => (μA j) ^ N) (fun _ : Fin rB => (0 : ℂ))
  let β : ℕ → Sum (Fin rA) (Fin rB) → ℂ := fun N =>
    Sum.elim (fun _ : Fin rA => (0 : ℂ)) (fun k : Fin rB => c N * (μB k) ^ N)
  -- The two assembled sums agree eventually.
  have hEq : ∀ᶠ N in atTop,
      ∑ x : Sum (Fin rA) (Fin rB), α N x • v N x =
        ∑ x : Sum (Fin rA) (Fin rB), β N x • v N x := by
    refine hState.mono ?_
    intro N hN
    have hLHS :
        ∑ x : Sum (Fin rA) (Fin rB), α N x • v N x =
          ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N := by
      simp [α, v, Fintype.sum_sum_type]
    have hRHS :
        ∑ x : Sum (Fin rA) (Fin rB), β N x • v N x =
          c N • ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
      have h1 :
          ∑ x : Sum (Fin rA) (Fin rB), β N x • v N x =
            ∑ k : Fin rB, (c N * (μB k) ^ N) • mpvState (d := d) (B k) N := by
        simp [β, v, Fintype.sum_sum_type]
      have h2 :
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) =
            ∑ k : Fin rB, (c N * (μB k) ^ N) • mpvState (d := d) (B k) N := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [smul_smul]
      rw [h1, h2]
    rw [hLHS, hRHS]
    exact hN
  -- Coefficient comparison: combined LI forces `α N = β N` eventually.
  have hcoeff :
      ∀ᶠ N in atTop, ∀ x : Sum (Fin rA) (Fin rB), α N x = β N x := by
    set_option maxRecDepth 2000 in
    exact coefficient_eventually_eq_of_eventually_linearIndependent
      (v := v) (a := α) (b := β) hLI hEq
  -- Pick a single length witnessing both coefficient equality and `c N ≠ 0`.
  obtain ⟨N, hcoeffN, hcNeN⟩ := (hcoeff.and hc_ne).exists
  -- Specialise at the dominant `B`-block index `inr ⟨0, hrB_pos⟩`.
  have hkey : α N (Sum.inr ⟨0, hrB_pos⟩) = β N (Sum.inr ⟨0, hrB_pos⟩) :=
    hcoeffN (Sum.inr ⟨0, hrB_pos⟩)
  -- LHS = 0; RHS = `c N · (μ_B 0)^N`.
  have hZero : c N * (μB ⟨0, hrB_pos⟩) ^ N = 0 := by
    have h : (0 : ℂ) = c N * (μB ⟨0, hrB_pos⟩) ^ N := by
      simpa [α, β] using hkey
    exact h.symm
  -- The nonzero scalar and nonvanishing dominant weight contradict that vanishing.
  have hμB_ne : μB ⟨0, hrB_pos⟩ ≠ 0 :=
    hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero ⟨0, hrB_pos⟩
  have hμB_pow_ne : (μB ⟨0, hrB_pos⟩) ^ N ≠ 0 := pow_ne_zero _ hμB_ne
  exact (mul_ne_zero hcNeN hμB_pow_ne) hZero

end CombinedLIWeakExistential

end MPSTensor

