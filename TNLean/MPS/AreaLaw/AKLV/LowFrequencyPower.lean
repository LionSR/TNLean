/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.FullFrequencyRank
import QICLean.Algebra.OneWindowWordPartition
import Mathlib.Algebra.BigOperators.Fin

/-!
# The actual low-frequency decomposition at the central AKLV cut

The actual full-frequency coefficients are partitioned by a minimum-frequency middle
interaction and its occurrence count. Each resulting operator is estimated using the
fixed-frequency bound and transported to the central cut. The same selected operator
is retained throughout; no suitable marker or coefficient-rank estimate is assumed.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--662.
**Local fix (count):** The commuting-gap binomial coefficient uses the correction at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
The subsequent binomial estimates and optimization are separate results.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

open Classical in
/-- A power of the actual window Hamiltonian is a sum of low-frequency pieces with
explicit rank bounds at the central cut. AKLV, arXiv:1301.1162v1, Lemma 4.2,
lines 604--662. The source interaction index is `u.val + 1`. -/
theorem exists_aklv_low_frequency_power_decomposition {L q a s : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L)) (ell : ℕ) :
    ∃ Q : Fin s × Fin (ell / s + 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (HL + (∑ j, H j) + HR) ^ ell = ∑ b, Q b ∧
      ∀ b, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (a + s / 2)) (Q b)) ≤
        (ell - b.2.val + s).choose s * (ell + b.2.val + 1).choose (2 * b.2.val + 1) *
          q ^ (2 * b.2.val + 2 * Nat.dist (b.1.val + 1) (s / 2)) := by
  let A := Fin s ⊕ Fin 2
  let : DecidableEq A := Classical.decEq A
  let emb : Fin s ↪ A := ⟨Sum.inl, Sum.inl_injective⟩
  let S : Finset A := Finset.univ.map emb
  have hS : S.Nonempty := ⟨Sum.inl ⟨0, hs⟩,
    Finset.mem_map.mpr ⟨⟨0, hs⟩, Finset.mem_univ _, rfl⟩⟩
  have hScard : S.card = s := by simp only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  obtain ⟨pick, _, hpartition⟩ :=
    Fintype.exists_one_window_word_coefficient_partition_of_le
      (R := Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) S hS
  let E := @Finset.piAntidiag A ℕ (Classical.decEq A) _ _ _ Finset.univ ell
  let selected (β : A → ℕ) : A := pick (fun u : S ↦ β u)
  let label (β : A → ℕ) : A × ℕ := (selected β, β (selected β))
  let piece (b : A × ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    ∑ β ∈ E with label β = b,
      WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) ell β
  let bin (u : Fin s) (k : ℕ) := piece (Sum.inl u, k)
  let Q (b : Fin s × Fin (ell / s + 1)) := bin b.1 b.2.val
  refine ⟨Q, ?_, ?_⟩
  · have hpart := hpartition (aklvWindowFamily H HL HR) ell ell (le_refl ell)
    change (∑ j, aklvWindowFamily H HL HR j) ^ ell =
      ∑ b ∈ S.product (Finset.range (ell / S.card + 1)), piece b at hpart
    rw [sum_aklvWindowFamily, hScard] at hpart
    refine hpart.trans ?_
    calc
      _ = ∑ u ∈ S, ∑ k ∈ Finset.range (ell / s + 1), piece (u, k) :=
        Finset.sum_product S (Finset.range (ell / s + 1)) piece
      _ = _ := by
        simp only [S, Finset.sum_map, Function.Embedding.coeFn_mk, emb]
        simp only [Q, bin, Fintype.sum_prod_type, Finset.sum_range]
  · intro b
    have hk : b.2.val ≤ ell :=
      (Nat.le_of_lt_succ b.2.isLt).trans (Nat.div_le_self ell s)
    have hdegree : ell - b.2.val + b.2.val = ell := Nat.sub_add_cancel hk
    let weight (β : A → ℕ) : ℂ := if selected β = Sum.inl b.1 then 1 else 0
    have hbin : Q b =
        ∑ β ∈ E.filter (fun β ↦ β (Sum.inl b.1) = b.2.val),
          weight β • WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) ell β := by
      simp only [Q, bin, piece, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro β _
      by_cases hsel : selected β = Sum.inl b.1
      · simp only [label, hsel, Prod.mk.injEq, true_and, weight, ite_true, one_smul]
      · have hlabel : label β ≠ (Sum.inl b.1, b.2.val) :=
          fun h ↦ hsel (congrArg Prod.fst h)
        simp only [hlabel, ite_false, weight, hsel, zero_smul]
        split_ifs <;> rfl
    have hrank := operatorSchmidtRank_aklv_full_frequency_slice_target_le
      hq hspace H hH HL HR hL hR b.1 (ell - b.2.val) b.2.val (a + s / 2) weight
    change operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (a + s / 2))
        (∑ β ∈ (@Finset.piAntidiag A ℕ (Classical.decEq A) _ _ _ Finset.univ
          (ell - b.2.val + b.2.val)).filter (fun β ↦ β (Sum.inl b.1) = b.2.val),
          weight β • WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR)
            (ell - b.2.val + b.2.val) β)) ≤ _ at hrank
    rw [hdegree, ← hbin] at hrank
    have hchoose : ell - b.2.val + 2 * b.2.val + 1 = ell + b.2.val + 1 := by omega
    simpa only [hchoose, Nat.add_assoc, Nat.dist_add_add_left] using hrank

/-- The resulting explicit finite-sum rank bound for a power of the physical window
Hamiltonian. AKLV, arXiv:1301.1162v1, Lemma 4.2, before the binomial estimates and
choice of the window width. -/
theorem operatorSchmidtRank_aklv_power_le_sum {L q a s : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L)) (ell : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (a + s / 2)) ((HL + (∑ j, H j) + HR) ^ ell)) ≤
      ∑ b : Fin s × Fin (ell / s + 1),
        (ell - b.2.val + s).choose s * (ell + b.2.val + 1).choose (2 * b.2.val + 1) *
          q ^ (2 * b.2.val + 2 * Nat.dist (b.1.val + 1) (s / 2)) := by
  obtain ⟨Q, hQ, hrank⟩ := exists_aklv_low_frequency_power_decomposition
    hq hs hspace H hH HL HR hL hR ell
  rw [hQ]
  have hcut : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (a + s / 2))
      (∑ b, Q b) = ∑ b, Entropy.cutOperator (n := fun _ : Fin L ↦ q)
        (leftBlock L (a + s / 2)) (Q b) := by
    ext x y
    simp only [Entropy.cutOperator, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [hcut]
  exact (operatorSchmidtRank_sum_le Finset.univ _).trans
    (Finset.sum_le_sum fun b _ ↦ hrank b)

end TNLean.MPS.AreaLaw
