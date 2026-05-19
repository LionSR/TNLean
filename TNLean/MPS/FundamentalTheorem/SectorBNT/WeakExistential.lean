/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Api

/-!
# Weak non-decaying-overlap existential for BNT canonical forms

This module proves the multi-copy weak existential for `IsBNTCanonicalForm`:
under eventual nonzero proportionality of the two assembled tensors, some pair
of basis blocks has a non-decaying cross-overlap.  The sector coefficient is
the raw power sum `P.coeff N j = ∑_q (P.weight j q)^N` of CPSV16 §II
(lines 287–301) — never a scalar power `(λ_j)^N` of a single per-sector
spectral level.

The proof is the canonical CPSV16 combined-family contradiction:

* contrapositive ⇒ every pairwise A–B overlap decays to zero;
* `eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal`
  (`TNLean.MPS.BNT.Basic`, line 195) — corollary `Lem1` of CPSV16 lines
  1121–1132 — assembles eventual linear independence of the joint family
  `{V^{(N)}(P.basis j)}_j ∪ {V^{(N)}(Q.basis k)}_k`;
* eventual nonzero proportionality of the assembled tensors yields a scalar
  sequence `c : ℕ → ℂ`, eventually nonzero, with weighted-state identity
  `∑_j P.coeff N j • V^{(N)}(P.basis j) = c N • ∑_k Q.coeff N k • V^{(N)}(Q.basis k)`
  eventually;
* `coefficient_eventually_eq_of_eventually_linearIndependent`
  (`TNLean.MPS.BNT.Basic`, line 172) forces every joint-family coefficient to
  vanish; specialising at the zeroth `Q`-block index gives
  `c N · Q.coeff N 0 = 0` eventually, hence `Q.coeff N 0 = 0` eventually;
* `IsBNTCanonicalForm.coeff_not_eventually_zero` from `SectorBNT/Basic.lean`
  rules this out, contradicting the contrapositive assumption.

The conclusion is the **weak existential**: there exist indices `j`, `k`
such that the cross-overlap does not decay to zero.  Promoting this to the
full pairwise conjunction `(∀ j, ∃ k, overlap does not decay) ∧ (∀ k, ∃ j,
overlap does not decay)` is a stronger statement that requires induction on
`P.basisCount + Q.basisCount`, mirroring CPSV16 §II_cor2's "fixed `k_0`
move-everything-else" argument (lines 1172–1192).

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and Boundary
  Theories*, arXiv:1606.00608.  Lines 287–301 (raw two-layer BNT display
  with coefficient `∑_q μ_{j,q}^N`), 1080–1091 (normal-tensor overlap
  dichotomy), 1121–1132 (corollary `Lem1`), 1184–1188 (multiplicity recovery
  via raw power-sum coefficient comparison), 1172–1192 (corollary `II_cor2`,
  fixed `k_0` move-everything-else argument).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix product states and projected entangled pair states*,
  arXiv:2011.12127.  Lines 1846–1884 (BNT and two-layer BNT decomposition
  with raw `μ_{j,q}`), 1891–1900 (proportional/equal MPV theorem-level
  targets).

## Tags

matrix product states, fundamental theorem, BNT, linear independence,
multi-copy coefficient comparison, raw power sum
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Eventual weighted-state identity from eventual proportionality

The next local lemma extracts a scalar sequence from
`EventuallyNonzeroProportionalMPV₂`: the assembled tensors are
`P.toTensor` and `Q.toTensor`, and the raw sector coefficient
`P.coeff N j = ∑_q (P.weight j q)^N` of CPSV16 lines 287–301 enters
as the coefficient in front of each basis MPV state. -/

private lemma exists_eventually_coeff_weighted_mpvState_eq_smul_sequence
    {P Q : SectorDecomposition d}
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ c : ℕ → ℂ, (∀ᶠ N in atTop, c N ≠ 0) ∧
      ∀ᶠ N in atTop,
        (∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N) =
          c N • (∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N) := by
  classical
  -- Per-`N` data: the proportionality scalar `c N` plus the weighted-state
  -- identity, expressed via the sector-coefficient expansion of
  -- `mpvState P.toTensor N` and `mpvState Q.toTensor N`.
  let Pred : ℕ → Prop := fun N =>
    ∃ c : ℂ, c ≠ 0 ∧
      (∑ j : Fin P.basisCount, P.coeff N j •
          mpvState (d := d) (P.basis j) N) =
        c • (∑ k : Fin Q.basisCount, Q.coeff N k •
          mpvState (d := d) (Q.basis k) N)
  have hPred : ∀ᶠ N in atTop, Pred N := by
    refine hProp.mono ?_
    intro N hN
    rcases hN with ⟨c, hc, hEq⟩
    refine ⟨c, hc, ?_⟩
    -- Replace each side by the corresponding `mpvState ·.toTensor N` via
    -- the raw two-layer expansion of CPSV16 lines 287–301 / CPSV21
    -- lines 1864–1884.
    have hPstate :
        mpvState (d := d) P.toTensor N =
          ∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) P.toTensor P.basis
        (N := N) (fun j => P.coeff N j) ?_
      intro σ
      simpa [smul_eq_mul] using P.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hQstate :
        mpvState (d := d) Q.toTensor N =
          ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := by
      refine mpvState_eq_sum_of_decomp (d := d) Q.toTensor Q.basis
        (N := N) (fun k => Q.coeff N k) ?_
      intro σ
      simpa [smul_eq_mul] using Q.mpv_toTensor_eq_sum_coeff (N := N) σ
    -- The proportionality identity holds pointwise on `mpv ·.toTensor σ`;
    -- translate to a `mpvState`-level identity.
    have hStateProp :
        mpvState (d := d) P.toTensor N =
          c • mpvState (d := d) Q.toTensor N := by
      apply PiLp.ext
      intro σ
      simpa [mpvState_apply, mpv, smul_eq_mul] using hEq σ
    -- Combine the three identities.
    calc
      (∑ j : Fin P.basisCount, P.coeff N j •
          mpvState (d := d) (P.basis j) N)
          = mpvState (d := d) P.toTensor N := hPstate.symm
      _ = c • mpvState (d := d) Q.toTensor N := hStateProp
      _ = c • (∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N) := by rw [hQstate]
  -- Pick the scalar from each eventual witness.
  let c : ℕ → ℂ := fun N => if hN : Pred N then Classical.choose hN else 1
  refine ⟨c, ?_, ?_⟩
  · refine hPred.mono ?_
    intro N hN
    dsimp [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).1
  · refine hPred.mono ?_
    intro N hN
    dsimp [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).2

/-! ### The weak existential -/

/-- **Weak non-decaying-overlap existence** for proportional families on the
BNT canonical-form surface (`IsBNTCanonicalForm`).

Given two `IsBNTCanonicalForm` families with eventual nonzero proportionality
of the assembled tensors, some pair `(j, k)` of basis blocks has a
non-decaying cross-overlap.

Paper anchors:

* CPSV16 lines 1121–1132 (corollary `Lem1`) — combined-family eventual
  linear-independence input;
* CPSV16 lines 1172–1192 (corollary `II_cor2`) — the contrapositive route
  via coefficient comparison after combined-family `Lem1`;
* CPSV16 lines 287–301 — raw sector coefficient
  `P.coeff N j = ∑_q (P.weight j q)^N`;
* CPSV16 lines 1184–1188 — raw power-sum coefficient comparison; combined
  with `coeff_not_eventually_zero` (`SectorBNT/Basic.lean`) to
  discharge the dominant block index.

This is the weak `∃-∃` form.  The full pairwise conjunction (∀ j, ∃ k,
overlap does not decay) ∧ (∀ k, ∃ j, overlap does not decay) is a stronger
statement requiring induction on `P.basisCount + Q.basisCount`. -/
theorem exists_nondecaying_overlap_pair_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hQ_pos : 0 < Q.basisCount)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ j : Fin P.basisCount, ∃ k : Fin Q.basisCount,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
          atTop (𝓝 0) := by
  classical
  by_contra hcontra
  push Not at hcontra
  -- `hcontra : ∀ j k, Tendsto (overlap (P.basis j) (Q.basis k)) → 0`.
  -- Same-family cross-overlap decay from `IsBNTCanonicalForm`.
  have hP_off :
      ∀ i j : Fin P.basisCount, i ≠ j →
        Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          atTop (𝓝 0) :=
    fun _ _ hij => hP.cross_overlap_basis_tendsto_zero hij
  have hQ_off :
      ∀ i j : Fin Q.basisCount, i ≠ j →
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis i) (Q.basis j) N)
          atTop (𝓝 0) :=
    fun _ _ hij => hQ.cross_overlap_basis_tendsto_zero hij
  -- Combined-family corollary `Lem1` (CPSV16 lines 1121–1132): eventual
  -- linear independence of the joint family.
  have hLI :
      ∀ᶠ N in atTop,
        LinearIndependent ℂ
          (Sum.elim
            (fun j : Fin P.basisCount => mpvState (d := d) (P.basis j) N)
            (fun k : Fin Q.basisCount => mpvState (d := d) (Q.basis k) N)) :=
    eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal
      (A := P.basis) (B := Q.basis)
      (hA_self := hP.basis_normalized_self_overlap)
      (hA_off := hP_off)
      (hB_self := hQ.basis_normalized_self_overlap)
      (hB_off := hQ_off)
      (hAB := hcontra)
  -- Scalar sequence from eventual nonzero proportionality.
  obtain ⟨c, hc_ne, hState⟩ :=
    exists_eventually_coeff_weighted_mpvState_eq_smul_sequence
      (P := P) (Q := Q) hProp
  -- Package the weighted-state identity as a `Sum.elim`-shaped linear
  -- relation on the combined family.
  let v : (N : ℕ) → Sum (Fin P.basisCount) (Fin Q.basisCount) → MPVSpace d N :=
    fun N =>
      Sum.elim
        (fun j : Fin P.basisCount => mpvState (d := d) (P.basis j) N)
        (fun k : Fin Q.basisCount => mpvState (d := d) (Q.basis k) N)
  let α : ℕ → Sum (Fin P.basisCount) (Fin Q.basisCount) → ℂ := fun N =>
    Sum.elim (fun j : Fin P.basisCount => P.coeff N j)
      (fun _ : Fin Q.basisCount => (0 : ℂ))
  let β : ℕ → Sum (Fin P.basisCount) (Fin Q.basisCount) → ℂ := fun N =>
    Sum.elim (fun _ : Fin P.basisCount => (0 : ℂ))
      (fun k : Fin Q.basisCount => c N * Q.coeff N k)
  have hEq : ∀ᶠ N in atTop,
      ∑ x : Sum (Fin P.basisCount) (Fin Q.basisCount), α N x • v N x =
        ∑ x : Sum (Fin P.basisCount) (Fin Q.basisCount), β N x • v N x := by
    refine hState.mono ?_
    intro N hN
    have hLHS :
        ∑ x : Sum (Fin P.basisCount) (Fin Q.basisCount), α N x • v N x =
          ∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N := by
      simp [α, v, Fintype.sum_sum_type]
    have hRHS :
        ∑ x : Sum (Fin P.basisCount) (Fin Q.basisCount), β N x • v N x =
          c N • ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := by
      have h1 :
          ∑ x : Sum (Fin P.basisCount) (Fin Q.basisCount), β N x • v N x =
            ∑ k : Fin Q.basisCount, (c N * Q.coeff N k) •
              mpvState (d := d) (Q.basis k) N := by
        simp [β, v, Fintype.sum_sum_type]
      have h2 :
          c N • (∑ k : Fin Q.basisCount, Q.coeff N k •
              mpvState (d := d) (Q.basis k) N) =
            ∑ k : Fin Q.basisCount, (c N * Q.coeff N k) •
              mpvState (d := d) (Q.basis k) N := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [smul_smul]
      rw [h1, h2]
    rw [hLHS, hRHS]
    exact hN
  -- Coefficient comparison: combined LI forces `α N = β N` eventually.
  have hcoeff :
      ∀ᶠ N in atTop, ∀ x : Sum (Fin P.basisCount) (Fin Q.basisCount),
        α N x = β N x := by
    set_option maxRecDepth 1024 in
    exact coefficient_eventually_eq_of_eventually_linearIndependent
      (v := v) (a := α) (b := β) hLI hEq
  -- Specialise at the dominant `Q`-block index `inr ⟨0, hQ_pos⟩`:
  -- `0 = c N * Q.coeff N ⟨0, hQ_pos⟩` eventually.
  have hZero : ∀ᶠ N in atTop, c N * Q.coeff N ⟨0, hQ_pos⟩ = 0 := by
    refine hcoeff.mono ?_
    intro N hN
    have h := hN (Sum.inr ⟨0, hQ_pos⟩)
    have hLHS0 : α N (Sum.inr ⟨0, hQ_pos⟩) = 0 := by
      simp [α]
    have hRHS : β N (Sum.inr ⟨0, hQ_pos⟩) = c N * Q.coeff N ⟨0, hQ_pos⟩ := by
      simp [β]
    rw [hLHS0] at h
    rw [hRHS] at h
    exact h.symm
  -- Combine with the eventually-nonzero scalar sequence to deduce that
  -- `Q.coeff N ⟨0, hQ_pos⟩` is eventually zero.
  have hQzero : ∀ᶠ N in atTop, Q.coeff N ⟨0, hQ_pos⟩ = 0 := by
    refine (hc_ne.and hZero).mono ?_
    intro N hN
    rcases hN with ⟨hcN, hMulN⟩
    rcases mul_eq_zero.mp hMulN with hzC | hzCoeff
    · exact (hcN hzC).elim
    · exact hzCoeff
  -- But `coeff_not_eventually_zero` (`SectorBNT/Basic.lean`)
  -- rules this out for any sector — in particular for the chosen
  -- `⟨0, hQ_pos⟩` of the `Q`-family.
  exact hQ.coeff_not_eventually_zero ⟨0, hQ_pos⟩ hQzero

end MPSTensor
