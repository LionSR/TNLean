import MPSLean.MPS.BNTPermutationSimple
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Fundamental Theorem — Thm 4.4, permutation/phase step (span-equality formulation)

This module packages the BNT permutation rigidity lemma
(`MPSTensor.exists_perm_dimEq_gaugePhaseEquiv_of_overlapOrtho` from
`BNTPermutationSimple.lean`) into a more general **paper-style** statement
where the two BNT families may have **different** numbers of blocks (`gA ≠ gB`).

The key new ingredient is a proof that the equal-span hypothesis forces
`gA = gB` via eventual linear independence and `finrank_span_eq_card`.

## Main result

* `MPSTensor.exists_eq_numBlocks_and_equiv_gaugePhase_of_overlapOrtho`:
  If two BNT-like families with `gA` and `gB` blocks respectively are both
  injective, normalised, and have asymptotically orthonormal overlaps, and they
  span the same MPV subspace at every system size, then
  1. `gA = gB`,
  2. there is a permutation `perm : Fin gA ≃ Fin gB`, and
  3. each block `A j` is gauge-phase equivalent to `B (perm j)` (with matching
     bond dimension).

## Reference

Theorem 4.4 (primitive/BNT branch) of
Cirac–Pérez-García–Schuch–Verstraete, *Matrix product states and projected
entangled pair states*, Rev. Mod. Phys. **93** (2021) 045003; arXiv:2011.12127.
-/

open scoped BigOperators Matrix
open Filter

namespace MPSTensor

/--
**Thm 4.4 (primitive/BNT permutation step), span-equality formulation.**

Two BNT-like families with possibly different numbers of blocks `gA`, `gB`
that are injective, normalised, asymptotically orthonormal, and span the same
MPV subspace at every system size must have `gA = gB` and agree blockwise up to
a permutation, dimension equality, and gauge-phase equivalence.
-/
theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_overlapOrtho
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ j, NeZero (dimB j)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (j : Fin gB) → MPSTensor d (dimB j))
    (hA_inj : ∀ j, IsInjective (A j))
    (hB_inj : ∀ j, IsInjective (B j))
    (hA_norm : ∀ j, (∑ i : Fin d, (A j i)ᴴ * (A j i)) = 1)
    (hB_norm : ∀ j, (∑ i : Fin d, (B j i)ᴴ * (B j i)) = 1)
    (hA_self : ∀ j, Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ j, Tendsto (fun N => mpvOverlap (d := d) (B j) (B j) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (B i) (B j) N) atTop (nhds 0))
    (hspan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin gA => mpvState (d := d) (A j) N))
        =
      Submodule.span ℂ (Set.range (fun j : Fin gB => mpvState (d := d) (B j) N))) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 1: Both families are eventually linearly independent.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hA_li :=
    eventually_linearIndependent_of_overlap_tendsto_orthonormal A hA_self hA_off
  have hB_li :=
    eventually_linearIndependent_of_overlap_tendsto_orthonormal B hB_self hB_off
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 2: Pick N where both are linearly independent.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hBoth : ∀ᶠ N in atTop,
      LinearIndependent ℂ (fun j : Fin gA => mpvState (d := d) (A j) N) ∧
      LinearIndependent ℂ (fun j : Fin gB => mpvState (d := d) (B j) N) := by
    filter_upwards [hA_li, hB_li] with N hA hB
    exact ⟨hA, hB⟩
  obtain ⟨N, hA_N, hB_N⟩ := hBoth.exists
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 3: Deduce gA = gB via finrank_span_eq_card.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hfA := finrank_span_eq_card hA_N
  have hfB := finrank_span_eq_card hB_N
  -- Both finranks refer to the same submodule by hspan.
  have hfAB : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range
      (fun j : Fin gA => mpvState (d := d) (A j) N))) =
    Module.finrank ℂ ↥(Submodule.span ℂ (Set.range
      (fun j : Fin gB => mpvState (d := d) (B j) N))) := by
    rw [hspan N]
  have hcard : Fintype.card (Fin gA) = Fintype.card (Fin gB) := by
    rw [← hfA, hfAB, hfB]
  simp only [Fintype.card_fin] at hcard
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 4: Substitute gA = gB and apply the equal-block-count theorem.
  -- ═══════════════════════════════════════════════════════════════════════════
  refine ⟨hcard, ?_⟩
  subst hcard
  -- Now gA = gB, so we can apply the existing same-count theorem.
  have hperm :=
    exists_perm_dimEq_gaugePhaseEquiv_of_overlapOrtho
      A B hA_inj hB_inj hA_norm hB_norm hA_self hA_off hB_self hB_off hspan
  obtain ⟨perm, hperm⟩ := hperm
  exact ⟨perm, hperm⟩

end MPSTensor
