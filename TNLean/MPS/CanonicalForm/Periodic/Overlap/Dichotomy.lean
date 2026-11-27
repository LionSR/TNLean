/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Periodic.Overlap.SectorMatchPropagation

/-!
# Periodic overlap dichotomy: main statement

This module contains the statement of the source proposition
`equal-or-orthogonal-generalized` and its eventual linear-independence corollary.

## Main declarations

* `periodicOverlapDichotomy`
* `periodicFamily_eventuallyLinearlyIndependent_of_cross_overlap_tendsto_zero`
* `periodicBasis_eventuallyLinearlyIndependent`
* `MPSTensor.periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent`: independence of the
  non-zero members of a basis of periodic vectors.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, proposition `equal-or-orthogonal-generalized`
  and Appendix A.
-/

open MPTensor

section Dichotomy

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix
open Kraus (blockPhysDim)

namespace MPSTensor

variable {d : ℕ}

/-! ## Main dichotomy from `equal-or-orthogonal-generalized` -/

/-- **Periodic overlap dichotomy** (arXiv:1708.00029,
proposition `equal-or-orthogonal-generalized`).

For two periodic tensors `A` and `B` with periods `m_a` and `m_b` in
irreducible form II, either their overlap decays to zero, or `D_a = D_b` and
they are related by a gauge transformation up to a unit-modulus phase (which
forces m_a = m_b).

This is the core technical result of the paper: all subsequent theorems
(proportional FT, equal FT with Z-gauge, symmetry corollary) depend on it.

Source: arXiv:1708.00029, Proposition equal-or-orthogonal-generalized
(statement, lines 589--609; appendix proof, lines 903--1118). -/
theorem periodicOverlapDichotomy
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0)
      ∨ ∃ (hdim : D₁ = D₂),
          RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- APPENDIX CASE SPLIT (arXiv:1708.00029 lines 915--1117):
  --   * m_a ≠ m_b            → `periodicOverlap_tendsto_zero_of_ne_period`
  --   * m_a = m_b, D₁ ≠ D₂ → `periodicOverlap_tendsto_zero_of_ne_dim`
  --   * same period/dim, no sector match
  --                            → `periodicOverlap_tendsto_zero_of_no_sector_match`
  --   * same period/dim, a sector match
  --                            → `periodicOverlap_gaugeEquiv_of_sector_match`
  -- Each branch theorem is proved.  In the sector-match branch,
  -- `sectorTensor_proportional_of_blockedMatch` supplies the full-cycle contraction
  -- and phase assembly before `periodicOverlap_gaugeEquiv_of_sector_match` returns
  -- the repeated-block relation.
  classical
  by_cases hm : m_a = m_b
  · subst hm
    have : NeZero m_a := ⟨hA.period_pos.ne'⟩
    by_cases hD : D₁ = D₂
    · subst hD
      obtain ⟨dimA, blocksA, PA, φA, hA_blocks_lc, hA_mpv, hPAproj, hPAsum,
        hAShift', hAComm, hATrace, hAIntertwine, hAMul, hAStar, hNondegA,
        hA_letter⟩ :=
        exists_cyclic_sector_decomp_with_letter_after_blocking_of_isPeriodic A hA
      obtain ⟨dimB, blocksB, PB, φB, hB_blocks_lc, hB_mpv, hPBproj, hPBsum,
        hBShift', hBComm, hBTrace, hBIntertwine, hBMul, hBStar, hNondegB,
        hB_letter⟩ :=
        exists_cyclic_sector_decomp_with_letter_after_blocking_of_isPeriodic B hB
      have hAShift :
          ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D₁) (fun i => (A i)ᴴ) (PA (k + 1)) =
            PA k := by
        intro k
        simpa [cyclicNextOfPos, Fin.add_def] using hAShift' k
      have hBShift :
          ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D₁) (fun i => (B i)ᴴ) (PB (k + 1)) =
            PB k := by
        intro k
        simpa [cyclicNextOfPos, Fin.add_def] using hBShift' k
      have hA_cyclic_with : IsCyclicSectorDecompWith A blocksA PA φA :=
        ⟨hPAproj, hPAsum, hAShift, hAComm, hATrace, hAIntertwine, hAMul,
          hAStar⟩
      have hB_cyclic_with : IsCyclicSectorDecompWith B blocksB PB φB :=
        ⟨hPBproj, hPBsum, hBShift, hBComm, hBTrace, hBIntertwine, hBMul,
          hBStar⟩
      have hA_cyclic : IsCyclicSectorDecomp A blocksA :=
        ⟨PA, φA, hA_cyclic_with⟩
      have hB_cyclic : IsCyclicSectorDecomp B blocksB :=
        ⟨PB, φB, hB_cyclic_with⟩
      by_cases hmatch : ∃ (u₀ v₀ : Fin m_a) (hdim : dimA u₀ = dimB v₀),
          GaugePhaseEquiv
            (cast (congr_arg (MPSTensor (blockPhysDim d m_a)) hdim) (blocksA u₀))
            (blocksB v₀)
      · refine Or.inr ⟨rfl, ?_⟩
        simpa using
          periodicOverlap_gaugeEquiv_of_sector_match A B hA hB blocksA blocksB
            hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic_with
            hB_cyclic_with hA_letter hB_letter hNondegA hmatch
      · refine Or.inl ?_
        refine periodicOverlap_tendsto_zero_of_no_sector_match A B hA hB blocksA blocksB
          hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hNondegA hNondegB ?_
        intro u v hdim _ hgpe
        exact hmatch ⟨u, v, hdim, hgpe⟩
    · exact Or.inl (periodicOverlap_tendsto_zero_of_ne_dim A B hA hB hD)
  · exact Or.inl (periodicOverlap_tendsto_zero_of_ne_period A B hA hB hm)

/-- A finite periodic family is eventually linearly independent along a common
period when every cross overlap tends to zero.

This is the Gram-matrix argument used in the independence consequence of
arXiv:1708.00029, lines 604--608: the self-overlaps tend to the positive
periods, while the cross overlaps tend to zero. -/
theorem periodicFamily_eventuallyLinearlyIndependent_of_cross_overlap_tendsto_zero
    {ι : Type*} [Finite ι]
    {dim : ι → ℕ}
    (A : (k : ι) → MPSTensor d (dim k))
    (period : ι → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (p : ℕ) [NeZero p]
    (hDiv : ∀ k, period k ∣ p)
    (hCross : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (A i) (A j) N) atTop (nhds 0)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k => mpvState (A k) (p * N)) := by
  -- Lem1t-style Gram argument (arXiv:1708.00029 lines 511--519, 604--608): the
  -- states `mpvState (A k) (p·N)` have Gram matrix converging to the
  -- nondegenerate diagonal `diag(period k)` — the diagonal from
  -- `periodicSelfOverlap_tendsto`, the off-diagonal from `hCross` — so they are
  -- eventually linearly independent by
  -- `eventually_linearIndependent_of_gram_tendsto_nondegenerate`.
  classical
  let : Fintype ι := Fintype.ofFinite ι
  set V := lp (fun N : ℕ => MPVSpace d N) 2 with hV
  set v : ι → ℕ → V :=
    fun k N => lp.single 2 (p * N) (mpvState (d := d) (A k) (p * N)) with hv
  set L : Matrix ι ι ℂ := Matrix.diagonal (fun k => (period k : ℂ)) with hLdef
  have hLdet : L.det ≠ 0 := by
    rw [hLdef, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (hPer k).period_pos.ne'
  have hGram : ∀ i j, Tendsto (fun N => ⟪v i N, v j N⟫_ℂ) atTop (nhds (L i j)) := by
    intro i j
    have hreduce : (fun N => ⟪v i N, v j N⟫_ℂ)
        = fun N => star (mpvOverlap (α := Fin d) (A i) (A j) (p * N)) := by
      funext N
      simp only [hv]
      rw [lp.inner_single_left, lp.single_apply_self, mpvOverlap_eq_star_mpvInner, star_star]
      rfl
    rw [hreduce]
    by_cases hij : i = j
    · subst hij
      have hLii : L i i = (period i : ℂ) := by simp [hLdef]
      rw [hLii]
      obtain ⟨c, hc⟩ := hDiv i
      have hcpos : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h0 | h
        · rw [h0, Nat.mul_zero] at hc; exact absurd hc (NeZero.ne p)
        · exact h
      have hmap : Tendsto (fun N : ℕ => c * N) atTop atTop :=
        tendsto_atTop_mono (fun n => le_mul_of_one_le_left (Nat.zero_le n) hcpos) tendsto_id
      have hcomp : Tendsto (fun N => mpvOverlap (α := Fin d) (A i) (A i) (p * N)) atTop
          (nhds (period i : ℂ)) :=
        ((periodicSelfOverlap_tendsto (A i) (hPer i)).comp hmap).congr fun N => by
          simp only [Function.comp]; rw [hc, mul_assoc]
      simpa using hcomp.star
    · have hLij : L i j = 0 := by simp [hLdef, Matrix.diagonal_apply_ne _ hij]
      rw [hLij]
      have hmap : Tendsto (fun N : ℕ => p * N) atTop atTop :=
        tendsto_atTop_mono (fun n => le_mul_of_one_le_left (Nat.zero_le n)
          (NeZero.pos p)) tendsto_id
      simpa using ((hCross i j hij).comp hmap).star
  have hLI : ∀ᶠ N in atTop, LinearIndependent ℂ (fun k : ι => v k N) :=
    eventually_linearIndependent_of_gram_tendsto_nondegenerate (v := v) L hLdet hGram
  rw [Filter.eventually_atTop] at hLI
  obtain ⟨N₀, hN₀⟩ := hLI
  refine ⟨N₀, fun N hN => ?_⟩
  let fN : MPVSpace d (p * N) →ₗ[ℂ] V :=
    lp.lsingle (𝕜 := ℂ) (E := fun N : ℕ => MPVSpace d N) 2 (p * N)
  have hN' : LinearIndependent ℂ (fun k : ι => fN (mpvState (d := d) (A k) (p * N))) := by
    convert hN₀ N hN using 1
    ext k L i
    rfl
  exact LinearIndependent.of_comp fN hN'

/-- **Eventual linear independence** (independence half of the consequence of
Proposition equal-or-orthogonal-generalized):
Given a family of periodic tensors `{A_j}` whose periods all divide a common
period `p`, there exists `N₀` such that for all `N ≥ N₀` that are multiples
of `p`, the vectors {|V_N(A_j)⟩} are linearly independent.

The common-period restriction ensures all `mpvState (A k) N` are nonzero
simultaneously (a zero vector would prevent `LinearIndependent` from holding).

**Scope restriction (independence only, no spanning):** the paper's consequence
(arXiv:1708.00029, lines 604--608) states *both* that the non-zero members of
{|V_N(A_j)⟩} are linearly independent *and* that they span |V_N(A)⟩ — the
spanning half is what "justifies the name basis of periodic vectors" (line 611).
Only the independence half is stated here. In addition the paper derives it from
Lem1t (the ε-almost-orthonormal ⇒ independent lemma, lines 511--519) applied to
the self-overlap limit and the cross-overlap decay; here the basis condition is
encoded directly as the pairwise non-repetition hypothesis `hNonrep`.
The spanning clause is proved separately by
`SectorDecomposition.mpvState_mem_span_nonzero` in `Overlap/Spanning.lean`.
The distinction between this common-period statement and the complete
source consequence is recorded in
`docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex`. -/
theorem periodicBasis_eventuallyLinearlyIndependent
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (p : ℕ) [NeZero p]
    (hDiv : ∀ k, period k ∣ p)
    (hNonrep : ∀ i j, i ≠ j →
      ∀ (hdim : dim i = dim j),
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (A i)) (A j)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k => mpvState (A k) (p * N)) := by
  refine periodicFamily_eventuallyLinearlyIndependent_of_cross_overlap_tendsto_zero
    A period hPer p hDiv ?_
  intro i j hij
  rcases periodicOverlapDichotomy (A i) (A j) (hPer i) (hPer j) with hdecay | ⟨hdim, hrep⟩
  · exact hdecay
  · exact absurd hrep (hNonrep i j hij hdim)

end MPSTensor

end Dichotomy

section NonzeroSubfamily

/-!
## Independence of the non-zero members of a basis of periodic vectors

The consequence of the periodic overlap dichotomy recorded in
arXiv:1708.00029, lines 604--608 asserts that beyond some chain length the
*non-zero* members of the family of matrix-product vectors generated by a basis
of periodic tensors are linearly independent. A member is non-zero exactly at
those chain lengths that its period divides, so the assertion is about the
subfamily indexed by the blocks whose period divides the length, and it holds at
every sufficiently large length rather than only at common multiples of all the
periods.

### Main declarations

* `MPSTensor.periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent`

### References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, proposition `equal-or-orthogonal-generalized`,
  lines 604--608, and its use in theorem `thm:bdequal`, lines 677--679.
-/

open scoped BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **Independence of the non-zero members of a basis of periodic vectors.**

For a pairwise non-repeated family of periodic tensors there is a chain length
beyond which, at every single length `N`, the matrix-product vectors of those
members whose period divides `N` are linearly independent.

This is the form of the independence consequence of proposition
`equal-or-orthogonal-generalized` that the proof of theorem `thm:bdequal` uses:
there the coefficient comparison is made at each large `N` separately, and only
the members with `m_j ∣ N` survive, the remaining ones generating the zero
vector.

The proof runs the common-multiple statement
`periodicFamily_eventuallyLinearlyIndependent_of_cross_overlap_tendsto_zero`
once for each of the finitely many subfamilies, at the least common multiple of
the periods occurring in that subfamily, and then takes the largest of the
finitely many thresholds obtained, scaled by the least common multiple of all
the periods. At a length `N` past that threshold the subfamily of members whose
period divides `N` has its own least common multiple dividing `N`, and the
quotient is past that subfamily's own threshold.

Source: arXiv:1708.00029, proposition `equal-or-orthogonal-generalized`,
lines 604--608; used at lines 677--679. -/
theorem periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent
    {g : ℕ} {dim : Fin g → ℕ}
    (A : (j : Fin g) → MPSTensor d (dim j))
    (period : Fin g → ℕ)
    (hPer : ∀ j, IsPeriodic (period j) (A j))
    (hNonrep : ∀ i j, i ≠ j →
      ∀ (hdim : dim i = dim j),
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (A i)) (A j)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ
        (fun j : {j : Fin g // period j ∣ N} => mpvState (d := d) (A ↑j) N) := by
  classical
  -- Positive bond dimensions, needed as instances by the overlap dichotomy.
  -- Every period is positive, so every least common multiple of periods is.
  have hlcmPos : ∀ S : Finset (Fin g), 0 < S.lcm period := by
    intro S
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨x, _, hx⟩ := Finset.lcm_eq_zero_iff.mp h0
    exact (hPer x).period_pos.ne' hx
  -- One threshold per subfamily, from the common-multiple statement.
  have key : ∀ S : Finset (Fin g), ∃ M : ℕ, ∀ n ≥ M,
      LinearIndependent ℂ
        (fun k : {j : Fin g // j ∈ S} =>
          mpvState (d := d) (A ↑k) (S.lcm period * n)) := by
    intro S
    have : NeZero (S.lcm period) := ⟨(hlcmPos S).ne'⟩
    refine periodicFamily_eventuallyLinearlyIndependent_of_cross_overlap_tendsto_zero
      (fun k : {j : Fin g // j ∈ S} => A ↑k) (fun k => period ↑k)
      (fun k => hPer ↑k) (S.lcm period) (fun k => Finset.dvd_lcm k.2) ?_
    intro i j hij
    have hij' : (i : Fin g) ≠ (j : Fin g) := fun h => hij (Subtype.ext h)
    rcases periodicOverlapDichotomy (A ↑i) (A ↑j) (hPer ↑i) (hPer ↑j) with
      hdecay | ⟨hdim, hrep⟩
    · exact hdecay
    · exact absurd hrep (hNonrep ↑i ↑j hij' hdim)
  choose M hM using key
  have hLPos : 0 < (Finset.univ : Finset (Fin g)).lcm period := hlcmPos _
  refine ⟨(Finset.univ : Finset (Finset (Fin g))).sup
    (fun S => (Finset.univ : Finset (Fin g)).lcm period * M S), fun N hN => ?_⟩
  set S : Finset (Fin g) := {j | period j ∣ N} with hSdef
  have hmem : ∀ x : Fin g, x ∈ S ↔ period x ∣ N := by
    intro x; simp [hSdef]
  obtain ⟨n, hn⟩ : S.lcm period ∣ N := Finset.lcm_dvd fun b hb => (hmem b).mp hb
  have hple : S.lcm period ≤ (Finset.univ : Finset (Fin g)).lcm period :=
    Nat.le_of_dvd hLPos (Finset.lcm_mono (Finset.subset_univ S))
  have hMS : M S ≤ n := by
    have h1 : (Finset.univ : Finset (Fin g)).lcm period * M S ≤ N :=
      le_trans (Finset.le_sup (f := fun S : Finset (Fin g) =>
        (Finset.univ : Finset (Fin g)).lcm period * M S) (Finset.mem_univ S)) hN
    rw [hn] at h1
    exact Nat.le_of_mul_le_mul_left
      (le_trans h1 (Nat.mul_le_mul_right n hple)) hLPos
  have hLI := hM S n hMS
  rw [← hn] at hLI
  exact hLI.comp (Equiv.subtypeEquivRight fun x => (hmem x).symm)
    (Equiv.subtypeEquivRight fun x => (hmem x).symm).injective

end MPSTensor

end NonzeroSubfamily
