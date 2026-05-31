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
`P.basisCount + Q.basisCount`, mirroring the CPSV16 equal-MPV corollary's
"fixed `k_0` move-everything-else" argument (lines 1172–1192).

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and Boundary
  Theories*, arXiv:1606.00608.  Lines 287–301 (raw two-layer BNT display
  with coefficient `∑_q μ_{j,q}^N`), 1080–1091 (normal-tensor overlap
  dichotomy), 1121–1132 (combined-family linear-independence corollary),
  Appendix MPV proof line 1182 (BNT projection/matching step),
  Appendix MPV proof lines 1184–1188 (multiplicity recovery via raw power-sum
  coefficient comparison), and Appendix MPV proof lines 1172–1192
  (equal-MPV corollary, fixed `k_0` move-everything-else argument).
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

end MPSTensor
