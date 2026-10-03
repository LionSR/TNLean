/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KrausSpanRank
import TNLean.MPS.Periodic.RootWordSpan
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Refinement from an invertible element in a root word span

An invertible element of the length-\(p-1\) word span of a tensor root
forces its Kraus rank to be at most the Kraus rank of its \(p\)-th power.
This gives a sufficient condition for the reverse direction of
arXiv:1708.00029, Theorem 4.1, converse paragraph, lines 812--818.

**Scope restriction (selected root):** The chosen root has an invertible
element in its length-\(p-1\) word span. The existence of such a root is
not asserted by channel divisibility alone; see
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix

namespace MPSTensor

variable {d r D : ℕ}

/-- An invertible element of a selected root's length-\(p-1\) word span
bounds the root's Choi rank by the Choi rank of the target transfer map.
Source context: arXiv:1708.00029, Theorem 4.1, converse, lines 812--818. -/
theorem choiRank_transferMap_le_of_isUnit_mem_root_wordSpan_pred
    (B : MPSTensor d D) (A : MPSTensor r D) {p : ℕ} (hp : 0 < p)
    (hpow : Kraus.transferMap B = (Kraus.transferMap A) ^ p)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan A (p - 1)) (hUnit : IsUnit X) :
    Channel.choiRank (Kraus.transferMap A) ≤
      Channel.choiRank (Kraus.transferMap B) := by
  have hBblock : Kraus.transferMap B = Kraus.transferMap (blockTensor A p) := by
    rw [transferMap_blockTensor]
    exact hpow
  calc
    Channel.choiRank (Kraus.transferMap A) =
        Module.finrank ℂ (Kraus.wordSpan A 1) :=
      Channel.choiRank_mapLM_eq_finrank_wordSpan_one A
    _ ≤ Module.finrank ℂ (Kraus.wordSpan A p) :=
      Kraus.wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_pred A hp hX hUnit
    _ = Module.finrank ℂ (Kraus.wordSpan (blockTensor A p) 1) := by
      rw [Kraus.wordSpan_blockTensor_one]
    _ = Channel.choiRank (Kraus.transferMap (blockTensor A p)) :=
      (Channel.choiRank_mapLM_eq_finrank_wordSpan_one (blockTensor A p)).symm
    _ = Channel.choiRank (Kraus.transferMap B) := by
      rw [hBblock]

/-- A tensor root on any finite alphabet gives a \(p\)-refinement when its
length-\(p-1\) word span contains an invertible matrix.
Source context: arXiv:1708.00029, Theorem 4.1, converse, lines 812--818;
the additional root condition is recorded in
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`. -/
theorem isPRefinable_of_root_isUnit_mem_wordSpan_pred
    (B : MPSTensor d D) (A : MPSTensor r D) {p : ℕ} (hp : 0 < p)
    (hpow : Kraus.transferMap B = (Kraus.transferMap A) ^ p)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan A (p - 1)) (hUnit : IsUnit X) :
    IsPRefinable B p := by
  have hRankA : Channel.choiRank (Kraus.transferMap A) ≤ d :=
    (choiRank_transferMap_le_of_isUnit_mem_root_wordSpan_pred B A hp hpow hX hUnit).trans
      (Channel.choiRank_le_of_hasKrausCard
        (T := Kraus.transferMap B) (r := d)
        ⟨B, by intro Y; simp⟩)
  have hCP : IsKrausCP (Kraus.transferMap A) :=
    ⟨r, A, by intro Y; simp⟩
  have hBound : Channel.HasKrausRankLE (Kraus.transferMap A) d :=
    ⟨Channel.choiRank (Kraus.transferMap A), hRankA,
      Channel.hasKrausCard_choiRank_of_cp hCP⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE
    B hp (Kraus.transferMap A) hpow hBound

end MPSTensor
