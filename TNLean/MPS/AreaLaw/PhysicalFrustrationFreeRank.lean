/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalParityProductRank

/-!
# Corrected cut rank of the actual regional truncation

The actual exterior sum and the two actual parity products give a uniform
operator Schmidt rank bound `q²+3`. No decomposition, rank, positivity or
projection hypothesis is supplied.

**Local fix (false additive constant):** The printed `q²+2` in ALVV,
arXiv:1602.08828v2, `thm:FF-tH`, lines 1543--1568, is false on
nondegenerate frustration-free data. The corrected bound here retains
both exterior sums and the noncrossing parity product. The counterexample
and correction are recorded in `docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`.
-/

open ManyBody (card_interval_le interval mem_interval)

open Matrix
open scoped BigOperators Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
local notation "C" => fun k ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L k)

private noncomputable def outsidePiece
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ)
    (P : Fin (L - 1) → Prop) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := by
  classical
  exact ∑ i, if ¬ (a ≤ i.val ∧ i.val + 1 < b) ∧ P i then Φ.term i else 0

private theorem isSupportedOn_outsidePiece
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ)
    (P : Fin (L - 1) → Prop) (S : Finset (Fin L))
    (hside : ∀ i, P i → interval L i.val (i.val + 2) ⊆ S) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (outsidePiece Φ a b P) S := by
  change _ ∈ ManyBody.supportedOperators _ _
  classical
  unfold outsidePiece
  apply sum_mem
  intro i _
  split_ifs with hi
  · exact ((Φ.mem i).mono (hside i hi.2))
  · exact zero_mem _

private theorem outside_sum_split
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ) :
    (∑ i, if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i) =
      outsidePiece Φ a b (fun i ↦ i.val + 1 < k) +
      outsidePiece Φ a b (fun i ↦ k ≤ i.val) +
      outsidePiece Φ a b (fun i ↦ i.val + 1 = k) := by
  classical
  unfold outsidePiece
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all <;> omega

private theorem outside_crossing_eq_zero
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ)
    (hno : ¬ ∃ i : Fin (L - 1), ¬ (a ≤ i.val ∧ i.val + 1 < b) ∧ i.val + 1 = k) :
    outsidePiece Φ a b (fun i ↦ i.val + 1 = k) = 0 := by
  classical
  unfold outsidePiece
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun hi ↦ hno ⟨i, hi⟩)

private theorem outside_crossing_eq_term
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ)
    (i : Fin (L - 1)) (hout : ¬ (a ≤ i.val ∧ i.val + 1 < b)) (hcross : i.val + 1 = k) :
    outsidePiece Φ a b (fun j ↦ j.val + 1 = k) = Φ.term i := by
  classical
  unfold outsidePiece
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left ⟨hout, hcross⟩
  · intro j _ hji
    apply ite_eq_right
    intro hj
    exact hji (Fin.ext (by omega))
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem outside_left_supported
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (outsidePiece Φ a b (fun i ↦ i.val + 1 < k)) (leftBlock L k) := by
  apply isSupportedOn_outsidePiece Φ a b _ _
  intro i hi v hv
  simp only [mem_interval, mem_leftBlock] at *
  omega

private theorem outside_right_supported
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (outsidePiece Φ a b (fun i ↦ k ≤ i.val)) (leftBlock L k)ᶜ := by
  apply isSupportedOn_outsidePiece Φ a b _ _
  intro i hi v hv
  simp only [Finset.mem_compl, mem_interval, mem_leftBlock] at *
  omega

/-- The actual regional truncation has operator Schmidt rank at most
`q²+3` at every site cut in positive local dimension. This corrects the
false additive constant in ALVV `thm:FF-tH`; see the module note. -/
private theorem physicalFrustrationFreeTruncation_rank_le_of_pos (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ) :
    operatorSchmidtRank (C k (physicalFrustrationFreeTruncation Φ a b)) ≤ q ^ 2 + 3 := by
  classical
  let cut := reindexAlgEquiv ℂ ℂ (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock L k))
  let HL := outsidePiece Φ a b (fun i ↦ i.val + 1 < k)
  let HR := outsidePiece Φ a b (fun i ↦ k ≤ i.val)
  let HC := outsidePiece Φ a b (fun i ↦ i.val + 1 = k)
  let Q := fun p ↦ (T).symm (physicalParityProduct
    ⟨intervalBondRestriction a b Φ, intervalBondRestriction_supported a b Φ⟩ p)
  let U := ManyBody.supportedOperators (fun _ ↦ Fin q) (leftBlock L k : Finset (Fin L))
  let V := ManyBody.supportedOperators (fun _ ↦ Fin q) ((leftBlock L k)ᶜ : Finset (Fin L))
  have hHL : HL ∈ U :=
    (outside_left_supported Φ a b k)
  have hHR : HR ∈ V :=
    (outside_right_supported Φ a b k)
  have hU1 : (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ∈ U :=
    (one_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) (leftBlock L k)))
  have hV1 : (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ∈ V :=
    (one_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) (leftBlock L k)ᶜ))
  have hdisjoint : Disjoint (leftBlock L k)ᶜ (leftBlock L k) :=
    Finset.disjoint_left.mpr (fun _ hv hw ↦ (Finset.mem_compl.mp hv) hw)
  have heq : physicalFrustrationFreeTruncation Φ a b =
      HL + HR + HC + 1 + 1 - Q 0 - Q 1 := by
    simp only [physicalFrustrationFreeTruncation, outside_sum_split Φ a b k, map_sub, map_one]
    change HL + HR + HC + (1 - Q 0) + (1 - Q 1) = _
    abel
  change operatorSchmidtRank (cut (physicalFrustrationFreeTruncation Φ a b)) ≤ q ^ 2 + 3
  by_cases hcross : ∃ i : Fin (L - 1), ¬ (a ≤ i.val ∧ i.val + 1 < b) ∧ i.val + 1 = k
  · obtain ⟨i, hout, hik⟩ := hcross
    have hside : b ≤ k ∨ k ≤ a := by omega
    have hQleft (hb : b ≤ k) (p : ℕ) : Q p ∈ U := by
      apply (isSupportedOn_regionalParityProduct Φ a b p).mono
      intro v hv
      simp only [mem_interval, mem_leftBlock] at *
      omega
    have hQright (ha : k ≤ a) (p : ℕ) : Q p ∈ V := by
      apply (isSupportedOn_regionalParityProduct Φ a b p).mono
      intro v hv
      simp only [Finset.mem_compl, mem_interval, mem_leftBlock] at *
      omega
    let X := if b ≤ k then HL + 1 + 1 - Q 0 - Q 1 else HL
    let Y := if b ≤ k then HR else HR + 1 + 1 - Q 0 - Q 1
    have hX : X ∈ U := by
      dsimp only [X]
      split_ifs with hb
      · exact sub_mem (sub_mem (add_mem (add_mem hHL hU1) hU1)
          (hQleft hb 0)) (hQleft hb 1)
      · exact hHL
    have hY : Y ∈ V := by
      dsimp only [Y]
      split_ifs with hb
      · exact hHR
      · have ha : k ≤ a := by omega
        exact sub_mem (sub_mem (add_mem (add_mem hHR hV1) hV1)
          (hQright ha 0)) (hQright ha 1)
    have hXrank : operatorSchmidtRank (cut X) ≤ 1 :=
      ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one (A := leftBlock L k)
        hX
        (Or.inl (Finset.Subset.refl _))
    have hYrank : operatorSchmidtRank (cut Y) ≤ 1 :=
      ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one (A := leftBlock L k)
        hY
        (Or.inr hdisjoint)
    have hterm : operatorSchmidtRank (cut (Φ.term i)) ≤ q ^ 2 :=
      (Φ.mem i).operatorSchmidtRank_cutOperator_le_pow_card (A := leftBlock L k) hq |>.trans
        (Nat.pow_le_pow_right hq ((card_interval_le _ _).trans (by omega)))
    have hdecomp : physicalFrustrationFreeTruncation Φ a b = X + Y + Φ.term i := by
      rw [heq, show HC = Φ.term i from outside_crossing_eq_term Φ a b k i hout hik]
      dsimp only [X, Y]
      split_ifs <;> abel
    rw [hdecomp, map_add, map_add]
    have h := (operatorSchmidtRank_add_le (cut X + cut Y) (cut (Φ.term i))).trans
      (Nat.add_le_add_right (operatorSchmidtRank_add_le (cut X) (cut Y)) _)
    omega
  · have hQ := sum_operatorSchmidtRank_physicalParityProduct_le hq
      ⟨intervalBondRestriction a b Φ, intervalBondRestriction_supported a b Φ⟩ k
    change operatorSchmidtRank (cut (Q 0)) + operatorSchmidtRank (cut (Q 1)) ≤ q ^ 2 + 1 at hQ
    let X := HL + 1 + 1
    have hX : X ∈ U := add_mem (add_mem hHL hU1) hU1
    have hXrank : operatorSchmidtRank (cut X) ≤ 1 :=
      ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one (A := leftBlock L k)
        hX
        (Or.inl (Finset.Subset.refl _))
    have hHRrank : operatorSchmidtRank (cut HR) ≤ 1 :=
      ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one (A := leftBlock L k)
        hHR
        (Or.inr hdisjoint)
    have hdecomp : cut (physicalFrustrationFreeTruncation Φ a b) =
        cut X + cut HR + (-1 : ℂ) • cut (Q 0) + (-1 : ℂ) • cut (Q 1) := by
      rw [heq, show HC = 0 from outside_crossing_eq_zero Φ a b k hcross]
      simp only [map_add, map_sub, map_zero, map_one, neg_one_smul]
      dsimp only [X]
      rw [map_add, map_add, map_one]
      abel
    rw [hdecomp]
    have hneg0 := operatorSchmidtRank_smul_le (-1 : ℂ) (cut (Q 0))
    have hneg1 := operatorSchmidtRank_smul_le (-1 : ℂ) (cut (Q 1))
    have hbase := operatorSchmidtRank_add_le (cut X) (cut HR)
    have hadd0 := operatorSchmidtRank_add_le (cut X + cut HR) ((-1 : ℂ) • cut (Q 0))
    have hadd1 := operatorSchmidtRank_add_le
      (cut X + cut HR + (-1 : ℂ) • cut (Q 0)) ((-1 : ℂ) • cut (Q 1))
    omega

/-- The actual regional frustration-free truncation has cut rank at most
`q²+3`, including empty intervals, endpoint cuts, zero local dimension
and the empty chain. All bounds are derived from the actual supported
terms and parity products; no decomposition or rank premise is supplied.
This is the corrected rank assertion of ALVV `thm:FF-tH`, as recorded
in `docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`. -/
theorem operatorSchmidtRank_physicalFrustrationFreeTruncation_le
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ) :
    operatorSchmidtRank (C k (physicalFrustrationFreeTruncation Φ a b)) ≤ q ^ 2 + 3 := by
  classical
  by_cases hq : 1 ≤ q
  · exact physicalFrustrationFreeTruncation_rank_le_of_pos hq Φ a b k
  have hq0 : q = 0 := by omega
  subst q
  have hzero : physicalFrustrationFreeTruncation Φ a b = 0 := by
    by_cases hL : L = 0
    · subst L
      simp [physicalFrustrationFreeTruncation, physicalParityProduct,
        ContinuousLinearMap.complementProd_zero]
    · have hLpos : 0 < L := by omega
      let : IsEmpty (Fin L → Fin 0) := ⟨fun σ ↦ Fin.elim0 (σ ⟨0, hLpos⟩)⟩
      exact Subsingleton.elim _ _
  rw [hzero]
  have hz : ManyBody.IsSupportedOn (X := fun _ ↦ Fin 0)
      (0 : Matrix (Fin L → Fin 0) (Fin L → Fin 0) ℂ) ∅ := by
    change _ ∈ ManyBody.supportedOperators _ _
    exact (zero_mem _)
  exact (hz.operatorSchmidtRank_cutOperator_le_one (A := leftBlock L k)
    (Or.inl (Finset.empty_subset _))).trans (by decide : 1 ≤ 0 ^ 2 + 3)

end TNLean.MPS.AreaLaw
