import MPSLean.MPS.FundamentalTheoremProportional
import MPSLean.Spectral.SpectralGapRect
import MPSLean.MPS.MPVOverlap
import MPSLean.MPS.CastLemmas

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# BNT permutation rigidity — Thm 4.4 (paper hypotheses, no span-equality)

This module is intended to replace the extra span-equality hypothesis used in
`BNTPermutationSimple.lean` with the **paper-style** hypotheses from Thm 4.4
(arXiv:2011.12127 / 1606.00608, primitive branch): proportionality of the *full*
MPV families together with explicit BNT decompositions.

At the moment we expose a self-contained lemma which proves the key paper step:
for each BNT block `B k`, it cannot happen that all mixed overlaps
`mpvOverlap (A j) (B k)` tend to `0`.

The proof follows the Appendix-A argument: take overlaps of the proportional
full states with the individual block state `B k` and use the asymptotic
orthogonality inside each BNT family.

The rest of the permutation/gauge-phase matching can then follow the same chain
as in `BNTPermutationSimple.lean`.
-/

open scoped BigOperators Matrix
open Filter Finset

namespace MPSTensor

/-! ## Overlap algebra for decompositions -/

/-- If `V(A_total)` expands in a finite family `A j`, then the overlap with `B` expands
with the same coefficients. -/
private lemma mpvOverlap_eq_sum_of_decomp_left
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
          simp [mpvOverlap, hdecomp]
    _ = ∑ σ : Cfg d N, ∑ j : Fin g, c j * (mpv (A j) σ * star (mpv B σ)) := by
          simp [Finset.sum_mul, mul_assoc]
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
  simp [mpvOverlap, h, Finset.mul_sum, mul_assoc]

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
  have : (cLim * bLim k) = (0 : ℂ) :=
    tendsto_nhds_unique hAB_overlap_lim hA0
  exact hAB_ne this


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
  have : (aLim j) = (0 : ℂ) :=
    tendsto_nhds_unique hA_overlap_lim hA0
  exact _haLim_ne j this


/-! ## Full permutation/phase matching (paper hypotheses, no span-equality)

We now combine the two non-vanishing-overlap lemmas with the existing overlap-decay dichotomy
(`mpvOverlap_tendsto_zero` / `mpvOverlap_tendsto_zero_of_dim_ne`) to obtain the full permutation
statement, without assuming span equality.
-/

/-! ### Helper: norm of phase from self-overlap scaling -/

/-- If `mpvOverlap B B N = (ζ * star ζ)^N * mpvOverlap A A N` and both self-overlaps have
norm → 1, then `‖ζ‖ = 1`. -/
private lemma norm_eq_one_of_selfOverlap_scale
    {d D D' : ℕ} {A : MPSTensor d D} {B : MPSTensor d D'} {ζ : ℂ}
    (hAA : Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1))
    (hBB : Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) atTop (nhds 1))
    (hSelf : ∀ N : ℕ,
      mpvOverlap (d := d) B B N =
      (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N) :
    ‖ζ‖ = 1 := by
  have hAA_ne : ∀ᶠ N in atTop, ‖mpvOverlap (d := d) A A N‖ ≠ 0 :=
    hAA.eventually_ne one_ne_zero
  have hRatio : Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖ /
      ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
    rw [show (1 : ℝ) = 1 / 1 from (one_div_one).symm]
    exact hBB.div hAA one_ne_zero
  have hRatioEq : ∀ᶠ N in atTop,
      ‖mpvOverlap (d := d) B B N‖ / ‖mpvOverlap (d := d) A A N‖ = (‖ζ‖ ^ 2) ^ N := by
    filter_upwards [hAA_ne] with N hN
    rw [hSelf N, norm_mul, norm_pow, show ‖ζ * starRingEnd ℂ ζ‖ = ‖ζ‖ ^ 2 from by
      rw [norm_mul, RCLike.norm_conj, sq]]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact mul_div_cancel_of_imp (fun h => absurd h hN)
  have hPow : Tendsto (fun N => (‖ζ‖ ^ 2) ^ N) atTop (nhds 1) :=
    hRatio.congr' hRatioEq
  have h1 : ‖ζ‖ ^ 2 = 1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact zero_ne_one (tendsto_nhds_unique
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h) hPow)
    · have hlt2 : ∀ᶠ n in atTop, (‖ζ‖ ^ 2) ^ n < 2 :=
        hPow.eventually (Iio_mem_nhds (by norm_num : (1:ℝ) < 2))
      rcases ((tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt h) 2).and hlt2).exists
        with ⟨n, hn1, hn2⟩
      exact not_lt_of_ge hn1 hn2
  nlinarith [norm_nonneg ζ]

set_option maxHeartbeats 800000 in
-- Heartbeat bump: the injectivity/permutation proof below triggers heavy term rewriting and can
-- otherwise exceed the default limit.
/--
**BNT permutation rigidity (primitive branch), paper hypothesis set.**

Two BNT-like families `A j` and `B k` with asymptotically orthonormal overlaps, together with
explicit decompositions of proportional full MPV families `A_total`, `B_total`, agree blockwise up
to a permutation, dimension equality, and gauge-phase equivalence.

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
  -- Step 1: build a matching `f : Fin gB → Fin gA` from the B-indexed non-vanishing overlap.
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
    by_contra hne
    exact hf_spec k (mpvOverlap_tendsto_zero_of_dim_ne (A (f k)) (B k)
      (hA_inj (f k)) (hB_inj k) (hA_norm (f k)) (hB_norm k) hne)
  have hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k) := by
    intro k
    by_contra hNot
    have hdim := hf_dim k
    have hAcst_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A (f k))) :=
      (isInjective_cast_dim hdim (A (f k))).mpr (hA_inj (f k))
    have hAcst_norm : ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) (A (f k)) i)ᴴ *
        (cast (congr_arg (MPSTensor d) hdim) (A (f k)) i) = 1 :=
      (dsGauge_cast_dim hdim (A (f k))).mpr (hA_norm (f k))
    have hto0 := mpvOverlap_tendsto_zero
      (cast (congr_arg (MPSTensor d) hdim) (A (f k))) (B k)
      hAcst_inj (hB_inj k) hAcst_norm (hB_norm k) hNot
    exact hf_spec k (hto0.congr fun N => mpvOverlap_cast_dim_left hdim (A (f k)) (B k) N)
  have hf_inj : Function.Injective f := by
    intro k1 k2 hk
    by_contra hne
    have h_cross : Tendsto (fun N => mpvOverlap (d := d) (B k1) (B k2) N) atTop (nhds 0) :=
      hB_off k1 k2 hne
    have h_cross_norm_zero : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖)
        atTop (nhds 0) := by
      simpa using h_cross.norm
    obtain ⟨X1, ζ1, hX1⟩ := hf_gauge k1
    obtain ⟨X2, ζ2, hX2⟩ := hf_gauge k2
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
    have overlap_self_scale : ∀ (Dk : ℕ) (Bk : MPSTensor d Dk) (ζ : ℂ)
        (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv Bk σ = ζ ^ N * mpv (A (f k1)) σ),
        ∀ N : ℕ, mpvOverlap (d := d) Bk Bk N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) (A (f k1)) (A (f k1)) N := by
      intro Dk Bk ζ hmpv N
      simp only [mpvOverlap]
      simp_rw [hmpv N, star_mul, star_pow]
      simp_rw [show star ζ = starRingEnd ℂ ζ from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ζ ^ N * mpv (A (f k1)) x *
            (star (mpv (A (f k1)) x) * (starRingEnd ℂ ζ) ^ N) =
          ζ ^ N * (starRingEnd ℂ ζ) ^ N *
            (mpv (A (f k1)) x * star (mpv (A (f k1)) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    have hAA_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A (f k1)) (A (f k1)) N‖)
        atTop (nhds 1) := by
      convert (hA_self (f k1)).norm using 1
      simp
    have hBB1_norm : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k1) N‖) atTop (nhds 1) := by
      convert (hB_self k1).norm using 1
      simp
    have hBB2_norm : Tendsto (fun N => ‖mpvOverlap (d := d) (B k2) (B k2) N‖) atTop (nhds 1) := by
      convert (hB_self k2).norm using 1
      simp
    have hζ1_norm : ‖ζ1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB1_norm
        (overlap_self_scale _ (B k1) ζ1 hmpv1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB2_norm
        (overlap_self_scale _ (B k2) ζ2 hmpv2)
    have hζ2 : ζ2 ≠ 0 := by
      intro h0
      have hnorm : (‖ζ2‖ : ℝ) = 0 := by simp [h0]
      rw [hζ2_norm] at hnorm
      exact one_ne_zero hnorm
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
          simp [hmpv2 N σ, mul_assoc]
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (B k1) (B k2) N =
          (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpvOverlap (d := d) (B k2) (B k2) N := by
      intro N
      exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
        (A := B k1) (B := B k2) (N := N)
        (c := ζ1 ^ N * (ζ2 ^ N)⁻¹) (h := hmpv_rel N) (C := B k2)
    have hCross_norm_one : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖)
        atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) =
          fun N => ‖ζ1 ^ N * (ζ2 ^ N)⁻¹‖ * ‖mpvOverlap (d := d) (B k2) (B k2) N‖ := by
        ext N
        rw [hCross_eq, norm_mul]
      rw [heq]
      have heq' : (fun N => ‖ζ1 ^ N * (ζ2 ^ N)⁻¹‖ * ‖mpvOverlap (d := d) (B k2) (B k2) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (B k2) (B k2) N‖ := by
        ext N
        simp [norm_pow, norm_inv, hζ1_norm, hζ2_norm]
      rw [heq']
      simpa using hBB2_norm
    exact zero_ne_one (tendsto_nhds_unique h_cross_norm_zero hCross_norm_one)
  have hle_BA : gB ≤ gA := by
    simpa using (Fintype.card_le_of_injective f hf_inj)
  -- Step 2: build a matching `g : Fin gA → Fin gB` from the A-indexed non-vanishing overlap.
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
    by_contra hne
    exact hg_spec j (mpvOverlap_tendsto_zero_of_dim_ne (A j) (B (g j))
      (hA_inj j) (hB_inj (g j)) (hA_norm j) (hB_norm (g j)) hne)
  have hg_gauge : ∀ j : Fin gA,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hg_dim j)) (A j))
        (B (g j)) := by
    intro j
    by_contra hNot
    have hdim := hg_dim j
    have hAcst_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) :=
      (isInjective_cast_dim hdim (A j)).mpr (hA_inj j)
    have hAcst_norm : ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) (A j) i)ᴴ *
        (cast (congr_arg (MPSTensor d) hdim) (A j) i) = 1 :=
      (dsGauge_cast_dim hdim (A j)).mpr (hA_norm j)
    have hto0 := mpvOverlap_tendsto_zero
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (B (g j))
      hAcst_inj (hB_inj (g j)) hAcst_norm (hB_norm (g j)) hNot
    exact hg_spec j (hto0.congr fun N => mpvOverlap_cast_dim_left hdim (A j) (B (g j)) N)
  have hg_inj : Function.Injective g := by
    intro j1 j2 hj
    by_contra hne
    have h_cross : Tendsto (fun N => mpvOverlap (d := d) (A j1) (A j2) N) atTop (nhds 0) :=
      hA_off j1 j2 hne
    have h_cross_norm_zero : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖)
        atTop (nhds 0) := by
      simpa using h_cross.norm
    obtain ⟨X1, ζ1, hX1⟩ := hg_gauge j1
    obtain ⟨X2, ζ2, hX2⟩ := hg_gauge j2
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
    have overlap_self_scaleA : ∀ (Dk : ℕ) (Bk : MPSTensor d Dk) {D : ℕ} (Aj : MPSTensor d D) (ζ : ℂ)
        (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv Bk σ = ζ ^ N * mpv Aj σ),
        ∀ N : ℕ, mpvOverlap (d := d) Bk Bk N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) Aj Aj N := by
      intro Dk Bk D Aj ζ hmpv N
      simp only [mpvOverlap]
      simp_rw [hmpv N, star_mul, star_pow]
      simp_rw [show star ζ = starRingEnd ℂ ζ from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ζ ^ N * mpv Aj x * (star (mpv Aj x) * (starRingEnd ℂ ζ) ^ N) =
          ζ ^ N * (starRingEnd ℂ ζ) ^ N * (mpv Aj x * star (mpv Aj x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    have hB_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (B (g j1)) (B (g j1)) N‖)
        atTop (nhds 1) := by
      convert (hB_self (g j1)).norm using 1
      simp
    have hA1_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j1) N‖)
        atTop (nhds 1) := by
      convert (hA_self j1).norm using 1
      simp
    have hA2_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A j2) (A j2) N‖)
        atTop (nhds 1) := by
      convert (hA_self j2).norm using 1
      simp
    have hζ1_norm : ‖ζ1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hA1_norm_tendsto hB_norm_tendsto
        (overlap_self_scaleA _ (Bk := B (g j1)) (Aj := A j1) ζ1 hmpvB1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hA2_norm_tendsto hB_norm_tendsto
        (overlap_self_scaleA _ (Bk := B (g j1)) (Aj := A j2) ζ2 hmpvB2)
    have hζ1 : ζ1 ≠ 0 := by
      intro h0
      have hnorm : (‖ζ1‖ : ℝ) = 0 := by simp [h0]
      rw [hζ1_norm] at hnorm
      exact one_ne_zero hnorm
    have hmpv_rel : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (A j1) σ = (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpv (A j2) σ := by
      intro N σ
      have hζ1N : ζ1 ^ N ≠ 0 := pow_ne_zero N hζ1
      have hInv : (ζ1 ^ N)⁻¹ * mpv (B (g j1)) σ = mpv (A j1) σ := by
        simpa [hmpvB1 N σ] using (inv_mul_cancel_left₀ hζ1N (mpv (A j1) σ))
      calc
        mpv (A j1) σ = (ζ1 ^ N)⁻¹ * mpv (B (g j1)) σ := by simpa using hInv.symm
        _ = (ζ1 ^ N)⁻¹ * (ζ2 ^ N * mpv (A j2) σ) := by simp [hmpvB2 N σ]
        _ = (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpv (A j2) σ := by ring
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (A j1) (A j2) N =
          (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpvOverlap (d := d) (A j2) (A j2) N := by
      intro N
      exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
        (A := A j1) (B := A j2) (N := N)
        (c := ζ2 ^ N * (ζ1 ^ N)⁻¹) (h := hmpv_rel N) (C := A j2)
    have hCross_norm_one : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖)
        atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) =
          fun N => ‖ζ2 ^ N * (ζ1 ^ N)⁻¹‖ * ‖mpvOverlap (d := d) (A j2) (A j2) N‖ := by
        ext N
        rw [hCross_eq, norm_mul]
      rw [heq]
      have heq' : (fun N => ‖ζ2 ^ N * (ζ1 ^ N)⁻¹‖ * ‖mpvOverlap (d := d) (A j2) (A j2) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (A j2) (A j2) N‖ := by
        ext N
        simp [norm_pow, norm_inv, hζ1_norm, hζ2_norm]
      rw [heq']
      simpa using hA2_norm_tendsto
    exact zero_ne_one (tendsto_nhds_unique h_cross_norm_zero hCross_norm_one)
  have hle_AB : gA ≤ gB := by
    simpa using (Fintype.card_le_of_injective g hg_inj)
  have hg : gA = gB := Nat.le_antisymm hle_AB hle_BA
  have hcard : Fintype.card (Fin gB) = Fintype.card (Fin gA) := by
    simp [hg]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  let e : Fin gB ≃ Fin gA := Equiv.ofBijective f hf_bij
  refine ⟨hg, e.symm, ?_⟩
  intro j
  have hfe : f (e.symm j) = j := Equiv.ofBijective_apply_symm_apply f hf_bij j
  have hdim : dimA j = dimB (e.symm j) :=
    Eq.ndrec (motive := fun x : Fin gA => dimA x = dimB (e.symm j)) (hf_dim (e.symm j)) hfe
  refine ⟨hdim, ?_⟩
  simpa [hdim] using
    (gaugePhaseEquiv_cast_idx_left (A := A) (B := B) (i₁ := f (e.symm j)) (i₂ := j)
      (k := e.symm j) hfe (hf_dim (e.symm j)) (hf_gauge (e.symm j)))

end MPSTensor
