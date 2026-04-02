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
# Permutation rigidity for basis-of-normal-tensors (BNT) decompositions — Thm 4.4
(paper hypotheses, no span-equality)

This module replaces the extra span-equality hypothesis used in
`BNTPermutationSimple.lean` with the **paper-style** hypotheses from Thm 4.4
(arXiv:2011.12127 / 1606.00608, primitive branch): proportionality of the *full*
MPV families together with explicit decompositions into BNT families.

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

/-! ## Overlap algebra for decompositions -/

/-- If `V(A_total)` expands in a finite family `A j`, then the overlap with `B` expands
with the same coefficients.

Intended for reuse by canonical-form bridge arguments (e.g. the equal-norm
nondecay proof in `EqualNormBridge`). -/
lemma mpvOverlap_eq_sum_of_decomp_left
    {d : ℕ} {Dtot : ℕ} {g : ℕ} {dim : Fin g → ℕ}
    (A_total : MPSTensor d Dtot)
    (A : (j : Fin g) → MPSTensor d (dim j))
    {N : ℕ} (c : Fin g → ℂ)
    (hdecomp : ∀ (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin g, c j * mpv (A j) σ)
    {D' : ℕ} (B : MPSTensor d D') :
    mpvOverlap (d := d) A_total B N =
      ∑ j : Fin g, c j * mpvOverlap (d := d) (A j) B N := by
  classical
  -- Expand `mpvOverlap` and commute the finite sums over configurations and block indices.
  calc
    mpvOverlap (d := d) A_total B N =
        ∑ σ : Cfg d N, (∑ j : Fin g, c j * mpv (A j) σ) * star (mpv B σ) := by
          simp only [mpvOverlap]
          congr 1; ext σ; rw [hdecomp σ]
    _ = ∑ σ : Cfg d N, ∑ j : Fin g, c j * (mpv (A j) σ * star (mpv B σ)) := by
          congr 1; ext σ; rw [Finset.sum_mul]; congr 1; ext j; ring
    _ = ∑ j : Fin g, ∑ σ : Cfg d N, c j * (mpv (A j) σ * star (mpv B σ)) := by
          -- Swap the two finite sums.
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset (Cfg d N)))
              (t := (Finset.univ : Finset (Fin g)))
              (f := fun σ j => c j * (mpv (A j) σ * star (mpv B σ))))
    _ = ∑ j : Fin g, c j * ∑ σ : Cfg d N, mpv (A j) σ * star (mpv B σ) := by
          -- Factor out the scalar `c j` from each inner sum.
          refine Finset.sum_congr rfl ?_
          intro j _
          -- `Finset.mul_sum` is stated with an explicit membership binder; `simp` removes it.
          simpa [mul_assoc] using
            (Finset.mul_sum (s := (Finset.univ : Finset (Cfg d N)))
              (f := fun σ : Cfg d N => mpv (A j) σ * star (mpv B σ)) (a := c j)).symm
    _ = ∑ j : Fin g, c j * mpvOverlap (d := d) (A j) B N := by
          simp [mpvOverlap]

/-- Proportionality of MPVs at a fixed system size upgrades to proportionality of overlaps. -/
private lemma mpvOverlap_eq_mul_of_mpv_eq_mul
    {d : ℕ} {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {N : ℕ} (c : ℂ) (h : ∀ (σ : Fin N → Fin d), mpv A σ = c * mpv B σ)
    {D' : ℕ} (C : MPSTensor d D') :
    mpvOverlap (d := d) A C N = c * mpvOverlap (d := d) B C N := by
  classical
  -- Factor out the scalar `c` from the overlap sum.
  simp only [mpvOverlap]
  rw [Finset.mul_sum]
  congr 1; ext σ; rw [h σ]; ring

/-! ## Key paper step: some mixed overlap does not decay -/

/--
**Key step of Thm 4.4 (paper route).**

Assume we have two families `A j` and `B k` whose within-family overlaps are
asymptotically orthonormal, and that the *full* tensors `A_total` and `B_total`
are proportional MPV families and admit expansions in those families with
coefficients converging to nonzero limits.

Then for each `k`, it is impossible that `mpvOverlap (A j) (B k)` tends to `0`
for all `j`.

This lemma is the replacement for the span-equality-based argument
`exists_nonzero_overlap` in `BNTPermutationSimple.lean`.
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
  push_neg at hall
  -- Step 1: show `mpvOverlap A_total (B k) → 0` using the A-decomposition.
  have hA0 : Tendsto (fun N => mpvOverlap (d := d) A_total (B k) N) atTop (nhds (0 : ℂ)) := by
    -- Expand the overlap at each N as a finite sum over j.
    have hEq : ∀ N,
        mpvOverlap (d := d) A_total (B k) N =
          ∑ j : Fin gA, (aCoeff N j) * mpvOverlap (d := d) (A j) (B k) N := by
      intro N
      -- apply the fixed-N overlap expansion lemma
      simpa using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := A_total) (A := A) (N := N) (c := aCoeff N)
        (hdecomp := hA_decomp N) (B := B k))
    -- Now take limits termwise.
    have hTerm : ∀ j : Fin gA,
        Tendsto (fun N => (aCoeff N j) * mpvOverlap (d := d) (A j) (B k) N)
          atTop (nhds (0 : ℂ)) := by
      intro j
      have := (haCoeff j).mul (hall j)
      simpa using this
    have hSum : Tendsto (fun N => ∑ j : Fin gA,
        (aCoeff N j) * mpvOverlap (d := d) (A j) (B k) N) atTop (nhds (0 : ℂ)) := by
      simpa using (tendsto_finset_sum Finset.univ (fun j _ => hTerm j))
    -- Conclude.
    simpa [hEq] using hSum
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
      simpa using (mpvOverlap_eq_sum_of_decomp_left (d := d)
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
        simpa using this
      · have := (hbCoeff k').mul (hB_off k' k hk')
        simpa [hk'] using this
    have hSum : Tendsto (fun N => ∑ k' : Fin gB,
        (bCoeff N k') * mpvOverlap (d := d) (B k') (B k) N)
        atTop (nhds (∑ k' : Fin gB, (if k' = k then bLim k else 0))) := by
      simpa using (tendsto_finset_sum Finset.univ (fun k' _ => hTerm k'))
    -- Simplify the RHS sum.
    have hRhs : (∑ k' : Fin gB, (if k' = k then bLim k else 0)) = bLim k := by
      simp
    simpa [hEq, hRhs] using hSum
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

/-- Conjugate symmetry for `mpvOverlap`. -/
private lemma mpvOverlap_star_swap {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (N : ℕ) :
    star (mpvOverlap (d := d) A B N) = mpvOverlap (d := d) B A N := by
  classical
  -- Take `star` of the defining sum and simplify termwise.
  simp [mpvOverlap, star_sum, star_mul]

/--
**Key step of Thm 4.4 (paper route), opposite direction.**

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
  push_neg at hall
  -- Convert the hypothesis to the opposite overlap orientation (needed for the B-decomposition).
  have hall_swap : ∀ k : Fin gB,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (A j) N) atTop (nhds 0) := by
    intro k
    have hstar : Tendsto (fun N => star (mpvOverlap (d := d) (A j) (B k) N))
        atTop (nhds (0 : ℂ)) := by
      simpa using (hall k).star
    refine hstar.congr ?_
    intro N
    simpa using (mpvOverlap_star_swap (d := d) (A := A j) (B := B k) N)
  -- Step 1: show `mpvOverlap B_total (A j) → 0` using the B-decomposition.
  have hB0 : Tendsto (fun N => mpvOverlap (d := d) B_total (A j) N) atTop (nhds (0 : ℂ)) := by
    have hEq : ∀ N,
        mpvOverlap (d := d) B_total (A j) N =
          ∑ k : Fin gB, (bCoeff N k) * mpvOverlap (d := d) (B k) (A j) N := by
      intro N
      simpa using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := B_total) (A := B) (N := N) (c := bCoeff N)
        (hdecomp := hB_decomp N) (B := A j))
    have hTerm : ∀ k : Fin gB,
        Tendsto (fun N => (bCoeff N k) * mpvOverlap (d := d) (B k) (A j) N)
          atTop (nhds (0 : ℂ)) := by
      intro k
      have := (hbCoeff k).mul (hall_swap k)
      simpa using this
    have hSum : Tendsto (fun N => ∑ k : Fin gB,
        (bCoeff N k) * mpvOverlap (d := d) (B k) (A j) N) atTop (nhds (0 : ℂ)) := by
      simpa using (tendsto_finset_sum Finset.univ (fun k _ => hTerm k))
    simpa [hEq] using hSum
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
      simpa using (hc.mul hB0)
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
      simpa using (mpvOverlap_eq_sum_of_decomp_left (d := d)
        (A_total := A_total) (A := A) (N := N) (c := aCoeff N)
        (hdecomp := hA_decomp N) (B := A j))
    have hTerm : ∀ i : Fin gA,
        Tendsto (fun N => (aCoeff N i) * mpvOverlap (d := d) (A i) (A j) N)
          atTop (nhds (if i = j then aLim j else 0)) := by
      intro i
      by_cases hij : i = j
      · cases hij
        have := (haCoeff j).mul (hA_self j)
        simpa using this
      · have := (haCoeff i).mul (hA_off i j hij)
        simpa [hij] using this
    have hSum : Tendsto (fun N => ∑ i : Fin gA,
        (aCoeff N i) * mpvOverlap (d := d) (A i) (A j) N)
        atTop (nhds (∑ i : Fin gA, (if i = j then aLim j else 0))) := by
      simpa using (tendsto_finset_sum Finset.univ (fun i _ => hTerm i))
    have hRhs : (∑ i : Fin gA, (if i = j then aLim j else 0)) = aLim j := by
      simp
    simpa [hEq, hRhs] using hSum
  -- Contradiction: the overlap tends both to `0` and to `aLim j ≠ 0`.
  exact (hA_overlap_lim.ne_nhds (_haLim_ne j)) hA0


/-! ## Full permutation/phase matching (paper hypotheses, no span-equality)

We now combine the two non-vanishing-overlap lemmas with the existing overlap-decay dichotomy
(`mpvOverlap_tendsto_zero` / `mpvOverlap_tendsto_zero_of_dim_ne`) to obtain the full permutation
statement, without assuming span equality.
-/

/-! ### Shared matching kernels -/

private lemma eq_dim_of_not_tendsto_zero_mpvOverlap
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {j : Fin gA} {k : Fin gB}
    (h_nonzero :
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0))
    (h_zero_of_dim_ne :
      dimA j ≠ dimB k →
        Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    dimA j = dimB k := by
  by_contra hdim
  exact h_nonzero (h_zero_of_dim_ne hdim)

private lemma gaugePhaseEquiv_of_not_tendsto_zero_mpvOverlap
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {j : Fin gA} {k : Fin gB}
    (hdim : dimA j = dimB k)
    (h_nonzero :
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0))
    (h_zero_of_not_gauge :
      ¬ GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (A j))
          (B k) →
        Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) (A j))
      (B k) := by
  by_contra hNot
  exact h_nonzero (h_zero_of_not_gauge hNot)

private lemma tendsto_norm_selfOverlap_one
    {d D : ℕ} (A : MPSTensor d D)
    (hSelf :
      Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ))) :
    Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
  convert hSelf.norm using 1
  simp

private lemma tendsto_norm_mpvOverlap_one_of_scaled_self
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (s : ℕ → ℂ)
    (hSelf :
      Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) atTop (nhds 1))
    (hs_norm : ∀ N, ‖s N‖ = 1)
    (hScale :
      ∀ N, mpvOverlap (d := d) A B N = s N * mpvOverlap (d := d) B B N) :
    Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) atTop (nhds 1) := by
  have heq :
      (fun N => ‖mpvOverlap (d := d) A B N‖) =
        fun N => ‖s N‖ * ‖mpvOverlap (d := d) B B N‖ := by
    ext N
    rw [hScale N, norm_mul]
  rw [heq]
  have heq' :
      (fun N => ‖s N‖ * ‖mpvOverlap (d := d) B B N‖) =
        fun N => 1 * ‖mpvOverlap (d := d) B B N‖ := by
    ext N
    simp [hs_norm N]
  rw [heq']
  simpa using hSelf

private lemma ne_zero_of_norm_eq_one (ζ : ℂ) (hζ_norm : ‖ζ‖ = 1) : ζ ≠ 0 := by
  intro h0
  have hnorm : (‖ζ‖ : ℝ) = 0 := by simp [h0]
  rw [hζ_norm] at hnorm
  exact one_ne_zero hnorm

private lemma rightMatching_injective_of_gaugePhaseEquiv
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (f : Fin gB → Fin gA)
    (hf_dim : ∀ k : Fin gB, dimA (f k) = dimB k)
    (hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    Function.Injective f := by
  intro k1 k2 hk
  by_contra hne
  have h_cross : Tendsto (fun N => mpvOverlap (d := d) (B k1) (B k2) N) atTop (nhds 0) :=
    hB_off k1 k2 hne
  have h_cross_norm_zero : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖)
      atTop (nhds 0) := by
    simpa using h_cross.norm
  obtain ⟨X1, ζ1, _, hX1⟩ := hf_gauge k1
  obtain ⟨X2, ζ2, _, hX2⟩ := hf_gauge k2
  have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k1) σ = ζ1 ^ N * mpv (A (f k1)) σ := by
    intro N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hf_dim k1)) (A (f k1)))
      (B := B k1) X1 ζ1 hX1 N σ,
      mpv_cast_dim (hf_dim k1) (A (f k1)) N σ]
  have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k2) σ = ζ2 ^ N * mpv (A (f k1)) σ := by
    intro N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hf_dim k2)) (A (f k2)))
      (B := B k2) X2 ζ2 hX2 N σ,
      mpv_cast_dim (hf_dim k2) (A (f k2)) N σ,
      hk.symm]
  have hAA_norm_tendsto :
      Tendsto (fun N => ‖mpvOverlap (d := d) (A (f k1)) (A (f k1)) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A := A (f k1)) (hSelf := hA_self (f k1))
  have hBB1_norm : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k1) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A := B k1) (hSelf := hB_self k1)
  have hBB2_norm : Tendsto (fun N => ‖mpvOverlap (d := d) (B k2) (B k2) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A := B k2) (hSelf := hB_self k2)
  have hζ1_norm : ‖ζ1‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB1_norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A (f k1)) (B := B k1) (ζ := ζ1) hmpv1)
  have hζ2_norm : ‖ζ2‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB2_norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A (f k1)) (B := B k2) (ζ := ζ2) hmpv2)
  have hζ2 : ζ2 ≠ 0 := ne_zero_of_norm_eq_one ζ2 hζ2_norm
  have hmpv_rel : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k1) σ = (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpv (B k2) σ := by
    intro N σ
    have hζ2N : ζ2 ^ N ≠ 0 := pow_ne_zero N hζ2
    calc
      mpv (B k1) σ = ζ1 ^ N * mpv (A (f k1)) σ := hmpv1 N σ
      _ = (ζ1 ^ N * (ζ2 ^ N)⁻¹) * (ζ2 ^ N * mpv (A (f k1)) σ) := by
        have : (ζ1 ^ N * (ζ2 ^ N)⁻¹) * (ζ2 ^ N * mpv (A (f k1)) σ) =
            ζ1 ^ N * mpv (A (f k1)) σ := by
          calc
            (ζ1 ^ N * (ζ2 ^ N)⁻¹) * (ζ2 ^ N * mpv (A (f k1)) σ)
                = ζ1 ^ N * ((ζ2 ^ N)⁻¹ * ζ2 ^ N) * mpv (A (f k1)) σ := by ring
            _ = ζ1 ^ N * 1 * mpv (A (f k1)) σ := by simp [inv_mul_cancel₀ hζ2N]
            _ = ζ1 ^ N * mpv (A (f k1)) σ := by ring
        exact this.symm
      _ = (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpv (B k2) σ := by
        rw [hmpv2 N σ]
  have hCross_eq : ∀ N : ℕ,
      mpvOverlap (d := d) (B k1) (B k2) N =
        (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpvOverlap (d := d) (B k2) (B k2) N := by
    intro N
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (A := B k1) (B := B k2) (N := N)
      (c := ζ1 ^ N * (ζ2 ^ N)⁻¹) (h := hmpv_rel N) (C := B k2)
  have hs_norm : ∀ N, ‖ζ1 ^ N * (ζ2 ^ N)⁻¹‖ = 1 := by
    intro N
    simp [norm_pow, norm_inv, hζ1_norm, hζ2_norm]
  have hCross_norm_one : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖)
      atTop (nhds 1) :=
    tendsto_norm_mpvOverlap_one_of_scaled_self
      (d := d)
      (A := B k1) (B := B k2)
      (s := fun N => ζ1 ^ N * (ζ2 ^ N)⁻¹)
      (hSelf := hBB2_norm)
      (hs_norm := hs_norm)
      (hScale := hCross_eq)
  exact (hCross_norm_one.ne_nhds one_ne_zero) h_cross_norm_zero

private lemma leftMatching_injective_of_gaugePhaseEquiv
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (g : Fin gA → Fin gB)
    (hg_dim : ∀ j : Fin gA, dimA j = dimB (g j))
    (hg_gauge : ∀ j : Fin gA,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hg_dim j)) (A j))
        (B (g j)))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ))) :
    Function.Injective g := by
  intro j1 j2 hj
  by_contra hne
  have h_cross : Tendsto (fun N => mpvOverlap (d := d) (A j1) (A j2) N) atTop (nhds 0) :=
    hA_off j1 j2 hne
  have h_cross_norm_zero : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖)
      atTop (nhds 0) := by
    simpa using h_cross.norm
  obtain ⟨X1, ζ1, _, hX1⟩ := hg_gauge j1
  obtain ⟨X2, ζ2, _, hX2⟩ := hg_gauge j2
  have hmpvB1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B (g j1)) σ = ζ1 ^ N * mpv (A j1) σ := by
    intro N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hg_dim j1)) (A j1))
      (B := B (g j1)) X1 ζ1 hX1 N σ,
      mpv_cast_dim (hg_dim j1) (A j1) N σ]
  have hmpvB2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B (g j1)) σ = ζ2 ^ N * mpv (A j2) σ := by
    intro N σ
    have htmp : mpv (B (g j2)) σ = ζ2 ^ N * mpv (A j2) σ := by
      rw [mpv_eq_pow_mul_of_gaugePhase
        (A := cast (congr_arg (MPSTensor d) (hg_dim j2)) (A j2))
        (B := B (g j2)) X2 ζ2 hX2 N σ,
        mpv_cast_dim (hg_dim j2) (A j2) N σ]
    exact Eq.ndrec
      (motive := fun k : Fin gB => mpv (B k) σ = ζ2 ^ N * mpv (A j2) σ)
      htmp hj.symm
  have hB_norm_tendsto :
      Tendsto (fun N => ‖mpvOverlap (d := d) (B (g j1)) (B (g j1)) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A := B (g j1)) (hSelf := hB_self (g j1))
  have hA1_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j1) N‖)
      atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A := A j1) (hSelf := hA_self j1)
  have hA2_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A j2) (A j2) N‖)
      atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A := A j2) (hSelf := hA_self j2)
  have hζ1_norm : ‖ζ1‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hA1_norm_tendsto hB_norm_tendsto
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A j1) (B := B (g j1)) (ζ := ζ1) hmpvB1)
  have hζ2_norm : ‖ζ2‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hA2_norm_tendsto hB_norm_tendsto
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A j2) (B := B (g j1)) (ζ := ζ2) hmpvB2)
  have hζ1 : ζ1 ≠ 0 := ne_zero_of_norm_eq_one ζ1 hζ1_norm
  have hmpv_rel : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (A j1) σ = (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpv (A j2) σ := by
    intro N σ
    have hζ1N : ζ1 ^ N ≠ 0 := pow_ne_zero N hζ1
    have hInv : (ζ1 ^ N)⁻¹ * mpv (B (g j1)) σ = mpv (A j1) σ := by
      rw [hmpvB1 N σ, inv_mul_cancel_left₀ hζ1N]
    calc
      mpv (A j1) σ = (ζ1 ^ N)⁻¹ * mpv (B (g j1)) σ := hInv.symm
      _ = (ζ1 ^ N)⁻¹ * (ζ2 ^ N * mpv (A j2) σ) := by rw [hmpvB2 N σ]
      _ = (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpv (A j2) σ := by ring
  have hCross_eq : ∀ N : ℕ,
      mpvOverlap (d := d) (A j1) (A j2) N =
        (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpvOverlap (d := d) (A j2) (A j2) N := by
    intro N
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (A := A j1) (B := A j2) (N := N)
      (c := ζ2 ^ N * (ζ1 ^ N)⁻¹) (h := hmpv_rel N) (C := A j2)
  have hs_norm : ∀ N, ‖ζ2 ^ N * (ζ1 ^ N)⁻¹‖ = 1 := by
    intro N
    simp [norm_pow, norm_inv, hζ1_norm, hζ2_norm]
  have hCross_norm_one : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖)
      atTop (nhds 1) :=
    tendsto_norm_mpvOverlap_one_of_scaled_self
      (d := d)
      (A := A j1) (B := A j2)
      (s := fun N => ζ2 ^ N * (ζ1 ^ N)⁻¹)
      (hSelf := hA2_norm_tendsto)
      (hs_norm := hs_norm)
      (hScale := hCross_eq)
  exact (hCross_norm_one.ne_nhds one_ne_zero) h_cross_norm_zero

private theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_rightMatching
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (f : Fin gB → Fin gA)
    (hf_inj : Function.Injective f)
    (hle_AB : gA ≤ gB)
    (hf_dim : ∀ k : Fin gB, dimA (f k) = dimB k)
    (hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k)) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  have hle_BA : gB ≤ gA := by
    simpa using (Fintype.card_le_of_injective f hf_inj)
  have hg : gA = gB := Nat.le_antisymm hle_AB hle_BA
  have hcard : Fintype.card (Fin gB) = Fintype.card (Fin gA) := by
    simp [hg]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  let e : Fin gB ≃ Fin gA := Equiv.ofBijective f hf_bij
  refine ⟨hg, e.symm, ?_⟩
  intro j
  have hfe : f (e.symm j) = j :=
    Equiv.ofBijective_apply_symm_apply f hf_bij j
  have hdim : dimA j = dimB (e.symm j) := by
    simpa [hfe] using hf_dim (e.symm j)
  refine ⟨hdim, ?_⟩
  simpa [hdim] using
    (gaugePhaseEquiv_cast_idx_left
      (A := A) (B := B) (i₁ := f (e.symm j)) (i₂ := j)
      (k := e.symm j) hfe (hf_dim (e.symm j)) (hf_gauge (e.symm j)))

private theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_core
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
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
    (h_zero_of_dim_ne : ∀ {j : Fin gA} {k : Fin gB},
      dimA j ≠ dimB k →
        Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0))
    (h_zero_of_not_gauge :
      ∀ {j : Fin gA} {k : Fin gB} (hdim : dimA j = dimB k),
        ¬ GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B k) →
          Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  have hExistsB : ∀ k : Fin gB,
      ∃ j : Fin gA,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) :=
    exists_nonzero_overlap_of_proportional_decomp
      (A := A) (B := B) (A_total := A_total) (B_total := B_total)
      (aCoeff := aCoeff) (bCoeff := bCoeff) (aLim := aLim) (bLim := bLim)
      (c := c) (cLim := cLim)
      (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
      (haCoeff := haCoeff) (hbCoeff := hbCoeff)
      (_haLim_ne := _haLim_ne) (_hbLim_ne := _hbLim_ne)
      (hProp := hProp) (hc := hc) (_hcLim_ne := _hcLim_ne)
      (hB_self := hB_self) (hB_off := hB_off)
  let f : Fin gB → Fin gA := fun k => (hExistsB k).choose
  have hf_spec : ∀ k : Fin gB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A (f k)) (B k) N) atTop (nhds 0) :=
    fun k => (hExistsB k).choose_spec
  have hf_dim : ∀ k : Fin gB, dimA (f k) = dimB k := by
    intro k
    exact eq_dim_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (h_nonzero := hf_spec k)
      (h_zero_of_dim_ne := fun hne => h_zero_of_dim_ne (j := f k) (k := k) hne)
  have hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k) := by
    intro k
    exact gaugePhaseEquiv_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (hdim := hf_dim k)
      (h_nonzero := hf_spec k)
      (h_zero_of_not_gauge :=
        fun hNot => h_zero_of_not_gauge (j := f k) (k := k) (hf_dim k) hNot)
  have hf_inj : Function.Injective f :=
    rightMatching_injective_of_gaugePhaseEquiv
      (A := A) (B := B) (f := f) (hf_dim := hf_dim) (hf_gauge := hf_gauge)
      (hA_self := hA_self) (hB_self := hB_self) (hB_off := hB_off)
  have hExistsA : ∀ j : Fin gA,
      ∃ k : Fin gB,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) :=
    exists_nonzero_overlap_of_proportional_decomp_left
      (A := A) (B := B) (A_total := A_total) (B_total := B_total)
      (aCoeff := aCoeff) (bCoeff := bCoeff) (aLim := aLim) (bLim := bLim)
      (c := c) (cLim := cLim)
      (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
      (haCoeff := haCoeff) (hbCoeff := hbCoeff)
      (_haLim_ne := _haLim_ne) (_hbLim_ne := _hbLim_ne)
      (hProp := hProp) (hc := hc) (_hcLim_ne := _hcLim_ne)
      (hA_self := hA_self) (hA_off := hA_off)
  let g : Fin gA → Fin gB := fun j => (hExistsA j).choose
  have hg_spec : ∀ j : Fin gA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B (g j)) N) atTop (nhds 0) :=
    fun j => (hExistsA j).choose_spec
  have hg_dim : ∀ j : Fin gA, dimA j = dimB (g j) := by
    intro j
    exact eq_dim_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (h_nonzero := hg_spec j)
      (h_zero_of_dim_ne := fun hne => h_zero_of_dim_ne (j := j) (k := g j) hne)
  have hg_gauge : ∀ j : Fin gA,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hg_dim j)) (A j))
        (B (g j)) := by
    intro j
    exact gaugePhaseEquiv_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (hdim := hg_dim j)
      (h_nonzero := hg_spec j)
      (h_zero_of_not_gauge :=
        fun hNot => h_zero_of_not_gauge (j := j) (k := g j) (hg_dim j) hNot)
  have hg_inj : Function.Injective g :=
    leftMatching_injective_of_gaugePhaseEquiv
      (A := A) (B := B) (g := g) (hg_dim := hg_dim) (hg_gauge := hg_gauge)
      (hA_self := hA_self) (hA_off := hA_off) (hB_self := hB_self)
  have hle_AB : gA ≤ gB := by
    simpa using (Fintype.card_le_of_injective g hg_inj)
  exact exists_eq_numBlocks_and_equiv_gaugePhase_of_rightMatching
    (A := A) (B := B) (f := f) hf_inj hle_AB hf_dim hf_gauge

/--
**Permutation rigidity for basis-of-normal-tensors (BNT) decompositions, primitive branch,
paper hypothesis set.**

Two BNT-like families `A j` and `B k` with asymptotically orthonormal overlaps, together with
explicit decompositions of proportional full MPV families `A_total`, `B_total`, agree blockwise up
to a permutation, dimension equality, and gauge-phase equivalence.

In canonical-form applications the coefficient arrays are obtained after dominant-weight
normalization, so the relevant data are `(μ j / μ 0)^N` and the discarded dominant factors are
absorbed into the proportionality constant.

This is the span-equality-free analogue of
`exists_eq_numBlocks_and_equiv_gaugePhase_of_overlapOrtho`.
-/
theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_inj : ∀ j, IsInjective (A j))
    (hB_inj : ∀ k, IsInjective (B k))
    (hA_norm : ∀ j, (∑ i : Fin d, (A j i)ᴴ * (A j i)) = 1)
    (hB_norm : ∀ k, (∑ i : Fin d, (B k i)ᴴ * (B k i)) = 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
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
    (_hcLim_ne : cLim ≠ 0) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  classical
  refine exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_core
    (A := A) (B := B)
    (hA_self := hA_self) (hA_off := hA_off)
    (hB_self := hB_self) (hB_off := hB_off)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (aLim := aLim) (bLim := bLim)
    (c := c) (cLim := cLim)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (haCoeff := haCoeff) (hbCoeff := hbCoeff)
    (_haLim_ne := _haLim_ne) (_hbLim_ne := _hbLim_ne)
    (hProp := hProp) (hc := hc) (_hcLim_ne := _hcLim_ne)
    ?_ ?_
  · intro j k hne
    exact mpvOverlap_tendsto_zero_of_dim_ne
      (A j) (B k) (hA_inj j) (hB_inj k) (hA_norm j) (hB_norm k) hne
  · intro j k hdim hNot
    exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      (hdim := hdim) (A := A j) (B := B k)
      (hA_inj := hA_inj j) (hB_inj := hB_inj k)
      (hA_norm := hA_norm j) (hB_norm := hB_norm k)
      hNot

/-- NT / irreducible version of
`exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp`.

This is the same permutation-matching argument, but the two contradiction steps that formerly
used injective overlap decay are replaced by the NT lemmas
`mpvOverlap_tendsto_zero_of_irreducible_TP` and
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`. -/
theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_of_irreducible_TP
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_irr : ∀ j, IsIrreducibleTensor (A j))
    (hB_irr : ∀ k, IsIrreducibleTensor (B k))
    (hA_norm : ∀ j, (∑ i : Fin d, (A j i)ᴴ * (A j i)) = 1)
    (hB_norm : ∀ k, (∑ i : Fin d, (B k i)ᴴ * (B k i)) = 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
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
    (_hcLim_ne : cLim ≠ 0) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  classical
  refine exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_core
    (A := A) (B := B)
    (hA_self := hA_self) (hA_off := hA_off)
    (hB_self := hB_self) (hB_off := hB_off)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (aLim := aLim) (bLim := bLim)
    (c := c) (cLim := cLim)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (haCoeff := haCoeff) (hbCoeff := hbCoeff)
    (_haLim_ne := _haLim_ne) (_hbLim_ne := _hbLim_ne)
    (hProp := hProp) (hc := hc) (_hcLim_ne := _hcLim_ne)
    ?_ ?_
  · intro j k hne
    exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
      (A j) (B k) (hA_irr j) (hB_irr k) (hA_norm j) (hB_norm k) hne
  · intro j k hdim hNot
    exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := B k)
      (hA_irr := hA_irr j) (hB_irr := hB_irr k)
      (hA_norm := hA_norm j) (hB_norm := hB_norm k)
      hNot

end MPSTensor
