/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumUniqueness

/-!
# BNT input for the equal-size direct-sum branch

This file connects the same-dimension BNT separation hypothesis to the
parent-Hamiltonian uniqueness input for David--Perez-Garcia--Schuch--Wolf,
Lemma `lem:direct-sum`.

The statement deliberately keeps the direct-sum hypotheses explicit:
`BlocksNotGaugePhaseEquiv` gives the long-chain non-proportional MPV witness,
while injectivity and length-`L` block injectivity are still separate inputs to
the parent-Hamiltonian argument.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d L : ℕ}

/-- Same-dimension BNT-separated blocks give the equal-size direct-sum
directness conclusion once the direct-sum injectivity hypotheses are supplied.

This is the BNT-facing form of the equal-size branch of
David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`.  The theorem does
not infer injectivity or transport non-equivalence through blocking; those
inputs remain explicit. -/
theorem groundSpace_inf_eq_bot_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k)
    (hAj_blk : IsNBlkInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) L)
    (hAk_blk : IsNBlkInjective (A k) L)
    (hAj_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)))
    (hAk_inj : IsInjective (A k))
    (hL : 1 < L) :
    groundSpace (cast (congr_arg (MPSTensor d) hdim) (A j)) (L + (L + L)) ⊓
        groundSpace (A k) (L + (L + L)) = ⊥ := by
  obtain ⟨N, hNmin, hSep⟩ :=
    exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
      A hIrr hLeft hOverlap hBlocks hjk hdim (max 2 L)
  have hN : 2 ≤ N := le_trans (Nat.le_max_left 2 L) hNmin
  have hLN : L ≤ N := le_trans (Nat.le_max_right 2 L) hNmin
  exact groundSpace_inf_eq_bot_of_exists_not_forall_mpv_eq_mul_of_dim_ge
    hAj_blk hAk_blk hAj_inj hAk_inj le_rfl hL ⟨N, hN, hLN, hSep⟩

/-- Same-dimension BNT-separated blocks give homogeneous pair trace separation
at the three-block length once the direct-sum injectivity hypotheses are
supplied.

This is the pair-trace form consumed by selector and word-span constructions.
The theorem still does not infer block injectivity at either length; those
remain explicit direct-sum inputs. -/
theorem pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k)
    (hAj_blk : IsNBlkInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) L)
    (hAk_blk : IsNBlkInjective (A k) L)
    (hAj_blk3 : IsNBlkInjective
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (L + (L + L)))
    (hAk_blk3 : IsNBlkInjective (A k) (L + (L + L)))
    (hAj_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)))
    (hAk_inj : IsInjective (A k))
    (hL : 1 < L) :
    PairTraceSeparatingAt
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k) (L + (L + L)) := by
  obtain ⟨N, hNmin, hSep⟩ :=
    exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
      A hIrr hLeft hOverlap hBlocks hjk hdim (max 2 L)
  have hN : 2 ≤ N := le_trans (Nat.le_max_left 2 L) hNmin
  have hLN : L ≤ N := le_trans (Nat.le_max_right 2 L) hNmin
  exact pairTraceSeparatingAt_threeBlock_of_exists_not_forall_mpv_eq_mul_of_dim_ge
    hAj_blk hAk_blk hAj_blk3 hAk_blk3 hAj_inj hAk_inj le_rfl hL
    ⟨N, hN, hLN, hSep⟩

end MPSTensor
