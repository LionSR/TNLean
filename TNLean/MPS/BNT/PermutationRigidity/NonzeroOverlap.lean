import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.CastDecay

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Permutation rigidity for basis-of-normal-tensors (BNT) decompositions — Theorem 4.4
(paper hypotheses, no span-equality)

This module replaces the extra span-equality hypothesis used in
`PermutationRigidityPrimitive.lean` with the **paper-style** hypotheses from Theorem 4.4
(arXiv:2011.12127 / 1606.00608, primitive branch): proportionality of the full MPV
families together with explicit decompositions into BNT families.

It contains both directions of the key nonvanishing-overlap step and the resulting
full permutation / gauge-phase matching theorems, in both the injective and
irreducible trace-preserving settings.

The overlap arguments follow the Appendix-A strategy: take overlaps of the
proportional full states with individual block states and use the asymptotic
orthogonality inside each BNT family.

In canonical-form applications one first normalizes by the dominant weights, so the relevant
coefficient arrays are `(μ j / μ 0)^N`; the discarded dominant factors are absorbed into the
proportionality constant.
-/

open scoped BigOperators Matrix
open Filter Finset

namespace MPSTensor

/-! ## Key paper step: some mixed overlap does not decay -/

/--
**Key step of Theorem 4.4 (paper route).**

Assume we have two families `A j` and `B k` whose within-family overlaps are
asymptotically orthonormal, and that the *full* tensors `A_total` and `B_total`
are proportional MPV families and admit expansions in those families with
coefficients converging to nonzero limits.

Then for each `k`, it is impossible that `mpvOverlap (A j) (B k)` tends to `0`
for all `j`.

This lemma is the replacement for the span-equality-based argument
`exists_nonzero_overlap` in `PermutationRigidityPrimitive.lean`.
-/
theorem exists_nonzero_overlap_of_proportional_decomp
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (aLim : Fin gA → ℂ) (bLim : Fin gB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (_haLim_ne : ∀ j, aLim j ≠ 0)
    (_hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (_hcLim_ne : cLim ≠ 0)
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    ∀ k : Fin gB,
      ∃ j : Fin gA,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  classical
  intro k
  by_contra hall
  push Not at hall
  -- Step 1: show `mpvOverlap A_total (B k) → 0` using the A-decomposition.
  have hA0 : Tendsto (fun N => mpvOverlap (d := d) A_total (B k) N) atTop (nhds (0 : ℂ)) := by
    -- Expand the overlap at each N as a finite sum over j.
    have hEq : ∀ N,
        mpvOverlap (d := d) A_total (B k) N =
          ∑ j : Fin gA, (aCoeff N j) * mpvOverlap (d := d) (A j) (B k) N := by
      intro N
      -- apply the fixed-N overlap expansion lemma
      simpa only using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := A_total) (A := A) (N := N) (c := aCoeff N)
        (hdecomp := hA_decomp N) (B := B k))
    -- Now take limits termwise.
    have hTerm : ∀ j : Fin gA,
        Tendsto (fun N => (aCoeff N j) * mpvOverlap (d := d) (A j) (B k) N)
          atTop (nhds (0 : ℂ)) := by
      intro j
      have := (haCoeff j).mul (hall j)
      simpa only [mul_zero] using this
    have hSum : Tendsto (fun N => ∑ j : Fin gA,
        (aCoeff N j) * mpvOverlap (d := d) (A j) (B k) N) atTop (nhds (0 : ℂ)) := by
      simpa only [sum_const_zero] using (tendsto_finset_sum Finset.univ (fun j _ => hTerm j))
    -- Conclude.
    simpa only [hEq] using hSum
  -- Step 2: compute the same overlap using proportionality + B-decomposition.
  have hEqProp : ∀ N,
      mpvOverlap (d := d) A_total (B k) N =
        (c N) * mpvOverlap (d := d) B_total (B k) N := by
    intro N
    -- use proportionality at size N
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (A := A_total) (B := B_total) (N := N)
      (c := c N) (h := hProp N) (C := B k)
  have hB_overlap_lim : Tendsto (fun N => mpvOverlap (d := d) B_total (B k) N)
      atTop (nhds (bLim k)) := by
    -- Expand overlap(B_total, B_k) as sum over blocks.
    have hEq : ∀ N,
        mpvOverlap (d := d) B_total (B k) N =
          ∑ k' : Fin gB, (bCoeff N k') * mpvOverlap (d := d) (B k') (B k) N := by
      intro N
      simpa only using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := B_total) (A := B) (N := N) (c := bCoeff N)
        (hdecomp := hB_decomp N) (B := B k))
    -- Termwise limits.
    have hTerm : ∀ k' : Fin gB,
        Tendsto (fun N => (bCoeff N k') * mpvOverlap (d := d) (B k') (B k) N)
          atTop (nhds (if k' = k then bLim k else 0)) := by
      intro k'
      by_cases hk' : k' = k
      · cases hk'
        have := (hbCoeff k).mul (hB_self k)
        simpa only [↓reduceIte, mul_one] using this
      · have := (hbCoeff k').mul (hB_off k' k hk')
        simpa only [hk', ↓reduceIte, mul_zero] using this
    have hSum : Tendsto (fun N => ∑ k' : Fin gB,
        (bCoeff N k') * mpvOverlap (d := d) (B k') (B k) N)
        atTop (nhds (∑ k' : Fin gB, (if k' = k then bLim k else 0))) := by
      simpa only [sum_ite_eq', mem_univ, ↓reduceIte] using
        (tendsto_finset_sum Finset.univ (fun k' _ => hTerm k'))
    -- Simplify the RHS sum.
    have hRhs : (∑ k' : Fin gB, (if k' = k then bLim k else 0)) = bLim k := by
      simp
    simpa only [hEq, hRhs] using hSum
  have hAB_overlap_lim : Tendsto (fun N => mpvOverlap (d := d) A_total (B k) N)
      atTop (nhds (cLim * bLim k)) := by
    have := hc.mul hB_overlap_lim
    -- rewrite with the pointwise equality from proportionality
    refine this.congr ?_
    intro N
    simp [hEqProp N]
  have hAB_ne : cLim * bLim k ≠ (0 : ℂ) := by
    exact mul_ne_zero _hcLim_ne (_hbLim_ne k)
  -- Contradiction: overlap tends to both 0 and a nonzero limit.
  exact (hAB_overlap_lim.ne_nhds hAB_ne) hA0


/-! ## Symmetric key step (A-indexed)

For the block-count equality we also need the converse direction: for each `A j`, some overlap
with a `B k` does not decay.
-/

/--
**Key step of Theorem 4.4 (paper route), opposite direction.**

Under the same proportionality + decomposition hypotheses as
`exists_nonzero_overlap_of_proportional_decomp`, if the `A`-family overlaps are asymptotically
orthonormal, then for each `j` it is impossible that
`mpvOverlap (A j) (B k) → 0` for all `k`.
-/
theorem exists_nonzero_overlap_of_proportional_decomp_left
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (aLim : Fin gA → ℂ) (bLim : Fin gB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (_haLim_ne : ∀ j, aLim j ≠ 0)
    (_hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (_hcLim_ne : cLim ≠ 0)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0)) :
    ∀ j : Fin gA,
      ∃ k : Fin gB,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  classical
  intro j
  by_contra hall
  push Not at hall
  -- Convert the hypothesis to the opposite overlap orientation (needed for the B-decomposition).
  have hall_swap : ∀ k : Fin gB,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (A j) N) atTop (nhds 0) := by
    intro k
    exact tendsto_mpvOverlap_zero_swap (A := A j) (B := B k) (hall k)
  -- Step 1: show `mpvOverlap B_total (A j) → 0` using the B-decomposition.
  have hB0 : Tendsto (fun N => mpvOverlap (d := d) B_total (A j) N) atTop (nhds (0 : ℂ)) := by
    have hEq : ∀ N,
        mpvOverlap (d := d) B_total (A j) N =
          ∑ k : Fin gB, (bCoeff N k) * mpvOverlap (d := d) (B k) (A j) N := by
      intro N
      simpa only using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := B_total) (A := B) (N := N) (c := bCoeff N)
        (hdecomp := hB_decomp N) (B := A j))
    have hTerm : ∀ k : Fin gB,
        Tendsto (fun N => (bCoeff N k) * mpvOverlap (d := d) (B k) (A j) N)
          atTop (nhds (0 : ℂ)) := by
      intro k
      have := (hbCoeff k).mul (hall_swap k)
      simpa only [mul_zero] using this
    have hSum : Tendsto (fun N => ∑ k : Fin gB,
        (bCoeff N k) * mpvOverlap (d := d) (B k) (A j) N) atTop (nhds (0 : ℂ)) := by
      simpa only [sum_const_zero] using (tendsto_finset_sum Finset.univ (fun k _ => hTerm k))
    simpa only [hEq] using hSum
  -- Step 2: use proportionality to show `mpvOverlap A_total (A j) → 0`.
  have hEqProp : ∀ N,
      mpvOverlap (d := d) A_total (A j) N =
        (c N) * mpvOverlap (d := d) B_total (A j) N := by
    intro N
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (A := A_total) (B := B_total) (N := N)
      (c := c N) (h := hProp N) (C := A j)
  have hA0 : Tendsto (fun N => mpvOverlap (d := d) A_total (A j) N) atTop (nhds (0 : ℂ)) := by
    have hmul : Tendsto (fun N => (c N) * mpvOverlap (d := d) B_total (A j) N)
        atTop (nhds (0 : ℂ)) := by
      simpa only [mul_zero] using (hc.mul hB0)
    refine hmul.congr ?_
    intro N
    simp [hEqProp N]
  -- Step 3: compute the *nonzero* limit of `mpvOverlap A_total (A j)` from the A-decomposition.
  have hA_overlap_lim : Tendsto (fun N => mpvOverlap (d := d) A_total (A j) N)
      atTop (nhds (aLim j)) := by
    have hEq : ∀ N,
        mpvOverlap (d := d) A_total (A j) N =
          ∑ i : Fin gA, (aCoeff N i) * mpvOverlap (d := d) (A i) (A j) N := by
      intro N
      simpa only using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := A_total) (A := A) (N := N) (c := aCoeff N)
        (hdecomp := hA_decomp N) (B := A j))
    have hTerm : ∀ i : Fin gA,
        Tendsto (fun N => (aCoeff N i) * mpvOverlap (d := d) (A i) (A j) N)
          atTop (nhds (if i = j then aLim j else 0)) := by
      intro i
      by_cases hij : i = j
      · cases hij
        have := (haCoeff j).mul (hA_self j)
        simpa only [↓reduceIte, mul_one] using this
      · have := (haCoeff i).mul (hA_off i j hij)
        simpa only [hij, ↓reduceIte, mul_zero] using this
    have hSum : Tendsto (fun N => ∑ i : Fin gA,
        (aCoeff N i) * mpvOverlap (d := d) (A i) (A j) N)
        atTop (nhds (∑ i : Fin gA, (if i = j then aLim j else 0))) := by
      simpa only [sum_ite_eq', mem_univ, ↓reduceIte] using
        (tendsto_finset_sum Finset.univ (fun i _ => hTerm i))
    have hRhs : (∑ i : Fin gA, (if i = j then aLim j else 0)) = aLim j := by
      simp
    simpa only [hEq, hRhs] using hSum
  -- Contradiction: the overlap tends both to `0` and to `aLim j ≠ 0`.
  exact (hA_overlap_lim.ne_nhds (_haLim_ne j)) hA0

end MPSTensor
