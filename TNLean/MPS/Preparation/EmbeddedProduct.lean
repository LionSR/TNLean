/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SiteEmbedding
import Mathlib.Data.Finset.NoncommProd

/-!
# Products of operators placed on disjoint sets of sites

For injective maps `e_k : Fin m → Fin n` with pairwise disjoint ranges and operators `X_k` on
`m` sites, the operators `X_k ⊗ 1` placed by `e_k` commute, and their product has the matrix
elements
`⟨x| ∏_k (X_k ⊗ 1) |y⟩ = ∏_k ⟨x ∘ e_k| X_k |y ∘ e_k⟩` when `x` and `y` agree outside the ranges,
and `0` otherwise (`MPSPreparation.noncommProd_embedOp_apply`). This is the tensor product
`⊗_k X_k` of the layers of arXiv:2307.01696, eqs. (10)–(12).
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d m n : ℕ}

theorem commute_embedOp_of_disjoint {e e' : Fin m → Fin n} (he : Function.Injective e)
    (he' : Function.Injective e') (h : Disjoint (Set.range e) (Set.range e'))
    (X X' : Matrix (Cfg d m) (Cfg d m) ℂ) : Commute (embedOp e X) (embedOp e' X') :=
  commute_of_mem_supportedOperators h (embedOp_mem_supportedOperators he X)
    (embedOp_mem_supportedOperators he' X')

/-- **Matrix elements of a product of placed operators.** -/
theorem noncommProd_embedOp_apply {ι : Type*} [DecidableEq ι] (e : ι → Fin m → Fin n)
    (he : ∀ k, Function.Injective (e k)) (X : ι → Matrix (Cfg d m) (Cfg d m) ℂ) :
    ∀ (s : Finset ι) (hdisj : (s : Set ι).PairwiseDisjoint fun k => Set.range (e k))
      (hcomm : (s : Set ι).Pairwise (Function.onFun Commute fun k => embedOp (e k) (X k)))
      (x y : Cfg d n),
      s.noncommProd (fun k => embedOp (e k) (X k)) hcomm x y =
        if ∀ i, (∀ k ∈ s, ∀ j, e k j ≠ i) → x i = y i then
          ∏ k ∈ s, X k (x ∘ e k) (y ∘ e k) else 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ x y
    simp only [Finset.noncommProd_empty, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, forall_const, Finset.prod_empty, one_apply]
    by_cases h : x = y
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (funext h')]
  | insert a s ha ih =>
    intro hdisj hcomm x y
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, mul_apply]
    have hdisj' : (s : Set ι).PairwiseDisjoint fun k => Set.range (e k) :=
      hdisj.subset (by simp)
    have hsa : ∀ k ∈ s, ∀ j j', e k j ≠ e a j' := fun k hk j j' h => by
      have hka : k ≠ a := fun h' => ha (h' ▸ hk)
      exact Set.disjoint_left.mp (hdisj (by simp [hk]) (by simp) hka) ⟨j, rfl⟩ ⟨j', h.symm⟩
    simp_rw [ih hdisj' (hcomm.mono (by simp))]
    set z₀ : Cfg d n := Function.extend (e a) (y ∘ e a) x with hz₀
    rw [Finset.sum_eq_single z₀]
    · have hag : AgreeOff (e a) x z₀ := fun i hi => by
        rw [hz₀, Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj]
      rw [embedOp_apply, ite_eq_left hag,
        show z₀ ∘ e a = y ∘ e a from Function.extend_comp (he a) _ _]
      have hz₀s : ∀ k ∈ s, z₀ ∘ e k = x ∘ e k := fun k hk => funext fun j => by
        simp only [Function.comp_apply, hz₀]
        rw [Function.extend_apply' _ _ _ fun ⟨j', hj'⟩ => hsa k hk j j' hj'.symm]
      have hprod : ∏ k ∈ s, X k (z₀ ∘ e k) (y ∘ e k) = ∏ k ∈ s, X k (x ∘ e k) (y ∘ e k) :=
        Finset.prod_congr rfl fun k hk => by rw [hz₀s k hk]
      rw [hprod, Finset.prod_insert ha]
      have hcond : (∀ i, (∀ k ∈ s, ∀ j, e k j ≠ i) → z₀ i = y i) ↔
          ∀ i, (∀ k ∈ insert a s, ∀ j, e k j ≠ i) → x i = y i := by
        constructor
        · intro h i hi
          have := h i fun k hk => hi k (Finset.mem_insert_of_mem hk)
          rwa [hz₀, Function.extend_apply' _ _ _ fun ⟨j, hj⟩ =>
            hi a (Finset.mem_insert_self a s) j hj] at this
        · intro h i hi
          by_cases hia : ∃ j, e a j = i
          · obtain ⟨j, rfl⟩ := hia
            rw [hz₀, (he a).extend_apply]; rfl
          · rw [hz₀, Function.extend_apply' _ _ _ hia]
            refine h i fun k hk j => ?_
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact fun hj => hia ⟨j, hj⟩
            · exact hi k hk j
      by_cases h : ∀ i, (∀ k ∈ insert a s, ∀ j, e k j ≠ i) → x i = y i
      · rw [ite_eq_left (hcond.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (hcond.mp h')), ite_eq_right h, mul_zero]
    · intro z _ hz
      rw [embedOp_apply]
      by_cases h1 : AgreeOff (e a) x z
      · by_cases h2 : ∀ i, (∀ k ∈ s, ∀ j, e k j ≠ i) → z i = y i
        · exfalso
          apply hz
          funext i
          by_cases hia : ∃ j, e a j = i
          · obtain ⟨j, rfl⟩ := hia
            rw [hz₀, (he a).extend_apply, Function.comp_apply]
            exact h2 _ fun k hk j' => hsa k hk j' j
          · rw [hz₀, Function.extend_apply' _ _ _ hia]
            exact (h1 i fun j hj => hia ⟨j, hj⟩).symm
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    · simp

end MPSPreparation
