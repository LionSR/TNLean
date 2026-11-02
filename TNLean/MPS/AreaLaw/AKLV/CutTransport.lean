/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.WindowFrequencyRank
import TNLean.MPS.AreaLaw.IntervalSymmDiff
import QICLean.Algebra.OperatorSchmidtPartition

/-!
# Transport of an AKLV frequency estimate to another chain cut

The same operator is compared at two actual prefix cuts. Moving the cut by `d` sites
costs at most `q ^ (2 * d)` in operator Schmidt rank. Applied to the actual window
coefficient family, this gives its rank at the central cut without selecting a new
operator or assuming a representation there.

**Local fix (count):** The inherited fixed-frequency estimate uses the corrected
commuting-gap binomial coefficient recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 651--654.
The low-frequency partition and the final optimized polynomial estimate are separate.
-/

open Matrix
open scoped BigOperators symmDiff

namespace TNLean.MPS.AreaLaw

/-- Moving a prefix cut costs at most the square of the Hilbert-space dimension of the
changed sites. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 651--654. -/
theorem operatorSchmidtRank_cutOperator_le_pow_dist_mul {L q : ℕ} (hq : 1 ≤ q)
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (i j : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L j) K) ≤
      q ^ (2 * Nat.dist i j) *
        operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K) := by
  have hleft (k : ℕ) : leftBlock L k = interval L 0 k := by
    ext v
    simp only [mem_leftBlock, mem_interval, Nat.zero_le, true_and]
  have hcard : ((leftBlock L i) ∆ (leftBlock L j)).card ≤ Nat.dist i j := by
    simpa only [hleft, Nat.dist_self, Nat.zero_add] using
      (card_interval_symmDiff_le_dist (L := L) 0 i 0 j)
  exact (Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le
    q (leftBlock L i) (leftBlock L j) K).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq (Nat.mul_le_mul_left 2 hcard)))

open Classical in
/-- The fixed-frequency window estimate at any target cut, for the same actual weighted
operator. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 651--662. -/
theorem operatorSchmidtRank_aklv_window_one_marker_target_le {L q a s : ℕ}
    (hq : 1 ≤ q) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L)) (u : Fin s) (t k target : ℕ) :
    let I := {j : Fin s ⊕ Fin 2 // j ≠ Sum.inl u}
    let E := @Finset.piAntidiag I ℕ (Classical.decEq I) _ _ _ Finset.univ t
    let ordinary := fun j : I ↦ aklvWindowFamily H HL HR j.val
    ∀ weight : E → ℂ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L target)
        (∑ α : E, weight α •
          WordMultiplicity.oneMarkerCoefficient ordinary (H u) t k α.val)) ≤
      (t + s).choose s * (t + 2 * k + 1).choose (2 * k + 1) *
        q ^ (2 * k + 2 * Nat.dist (a + u.val + 1) target) := by
  intro I E ordinary weight
  have hrank := operatorSchmidtRank_aklv_window_one_marker_le
    hq hspace H hH HL HR hL hR u t k weight
  have hmove := operatorSchmidtRank_cutOperator_le_pow_dist_mul hq
    (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient ordinary (H u) t k α.val)
    (a + u.val + 1) target
  refine (hmove.trans (Nat.mul_le_mul_left _ hrank)).trans_eq ?_
  rw [pow_add]
  ac_rfl

end TNLean.MPS.AreaLaw
