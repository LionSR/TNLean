/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import Mathlib.Data.Finset.NoncommProd

/-!
# Products of operators placed on disjoint sets of sites

For injective maps `e_k : Fin m_k → Fin n` with pairwise disjoint ranges and operators `X_k` on
`m_k` sites, the operators `X_k ⊗ 1` placed by `e_k` commute, and their product has the matrix
elements
`⟨x| ∏_k (X_k ⊗ 1) |y⟩ = ∏_k ⟨x ∘ e_k| X_k |y ∘ e_k⟩` when `x` and `y` agree outside the ranges,
and `0` otherwise (`QuantumCircuit.noncommProd_embedOp_apply`). This is the tensor product
`⊗_k X_k` of the layers of arXiv:2307.01696, eqs. (10)–(12).

The configuration `QuantumCircuit.placeCfg W c` carries the contents `c p` on pairwise disjoint
windows `W p` and `0` elsewhere. If matrices `Y_p` on the windows `W_p` act on the inputs
`ι_p(c)` as matrices `V_p` with injective outputs `o_p(e)`, then the product of the placed
matrices maps the configuration carrying `ι_p(c_p)` on the window `p` and `0` elsewhere to
`∑_e ∏_p V_p(e_p, c_p) |o_p(e_p) on the windows, 0 elsewhere⟩`
(`QuantumCircuit.list_prod_embedOp_placeCfg`).
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d m n : ℕ}

theorem commute_embedOp_of_disjoint {m' : ℕ} {e : Fin m → Fin n} {e' : Fin m' → Fin n}
    (he : Function.Injective e) (he' : Function.Injective e')
    (h : Disjoint (Set.range e) (Set.range e')) (X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (X' : Matrix (Fin m' → Fin d) (Fin m' → Fin d) ℂ) : Commute (embedOp e X) (embedOp e' X') :=
  commute_of_mem_supportedOperators h (embedOp_mem_supportedOperators he X)
    (embedOp_mem_supportedOperators he' X')

/-- **Matrix elements of a product of placed operators.** -/
theorem noncommProd_embedOp_apply {ι : Type*} {m : ι → ℕ} (e : ∀ k, Fin (m k) → Fin n)
    (he : ∀ k, Function.Injective (e k))
    (X : ∀ k, Matrix (Fin (m k) → Fin d) (Fin (m k) → Fin d) ℂ) :
    ∀ (s : Finset ι) (_ : (s : Set ι).PairwiseDisjoint fun k => Set.range (e k))
      (hcomm : (s : Set ι).Pairwise (Function.onFun Commute fun k => embedOp (e k) (X k)))
      (x y : Fin n → Fin d),
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
    set z₀ : Fin n → Fin d := Function.extend (e a) (y ∘ e a) x with hz₀
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

/-! ### Configurations placed on windows -/

section Place

variable [NeZero d] {ι : Type*}

/-- The configuration carrying `c p` on the window `W p` and `0` at the other sites. -/
noncomputable def placeCfg (W : ι → Fin m → Fin n) (c : ι → Fin m → Fin d) : Fin n → Fin d :=
  Function.extend (fun pt : ι × Fin m => W pt.1 pt.2) (fun pt => c pt.1 pt.2) fun _ => 0

variable {W : ι → Fin m → Fin n} (hW : Function.Injective fun pt : ι × Fin m => W pt.1 pt.2)
include hW

theorem placeCfg_apply (c : ι → Fin m → Fin d) (p : ι) (t : Fin m) : placeCfg W c (W p t) = c p t :=
  hW.extend_apply _ _ (p, t)

theorem placeCfg_comp (c : ι → Fin m → Fin d) (p : ι) : placeCfg W c ∘ W p = c p :=
  funext (placeCfg_apply hW c p)

omit hW in
theorem placeCfg_apply_of_notMem (c : ι → Fin m → Fin d) {y : Fin n} (hy : ∀ p t, W p t ≠ y) :
    placeCfg W c y = 0 :=
  Function.extend_apply' _ _ _ fun ⟨pt, h⟩ => hy pt.1 pt.2 h

/-- A configuration with `0` off the windows is the placed configuration of its contents. -/
theorem eq_placeCfg {z : Fin n → Fin d} (hz : ∀ y, (∀ p t, W p t ≠ y) → z y = 0) :
    z = placeCfg W fun p => z ∘ W p := by
  funext y
  by_cases hy : ∃ p t, W p t = y
  · obtain ⟨p, t, rfl⟩ := hy
    rw [placeCfg_apply hW]; rfl
  · simp only [not_exists] at hy
    rw [placeCfg_apply_of_notMem _ hy, hz y hy]

theorem placeCfg_injective : Function.Injective (placeCfg (d := d) W) := by
  intro c c' h
  funext p
  rw [← placeCfg_comp hW c p, ← placeCfg_comp hW c' p, h]

theorem injective_window (p : ι) : Function.Injective (W p) := fun t t' h =>
  (Prod.ext_iff.mp (hW (a₁ := (p, t)) (a₂ := (p, t')) h)).2

theorem disjoint_range_window {p p' : ι} (hpp : p ≠ p') :
    Disjoint (Set.range (W p)) (Set.range (W p')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, rfl⟩ ⟨t', ht⟩
  exact hpp (Prod.ext_iff.mp (hW (a₁ := (p', t')) (a₂ := (p, t)) ht)).1.symm

end Place

/-! ### A layer of placed matrices -/

/-- **A layer of placed matrices on placed inputs.** Let `Y p` be matrices on the pairwise
disjoint windows `W p` acting on the inputs `ι' p c` as the matrices `V p` with injective outputs
`o p b`: `Y p (z, ι' p c) = V p (b, c)` if `z = o p b` and `0` otherwise. Then the product of
the placed `Y p` applied to the configuration carrying `ι' p (c p)` on the windows and `0`
elsewhere has the amplitude `∏_p V p (e p) (c p)` at the configuration carrying `o p (e p)` on
the windows and `0` elsewhere, and `0` at every other configuration. -/
theorem list_prod_embedOp_placeCfg {d m n P : ℕ} [NeZero d] {W : Fin P → Fin m → Fin n}
    (hW : Function.Injective fun pt : Fin P × Fin m => W pt.1 pt.2)
    (Y : Fin P → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) {α β : Type*}
    (ι' : Fin P → α → Fin m → Fin d) (o : Fin P → β → Fin m → Fin d)
    (ho : ∀ p, Function.Injective (o p))
    (V : Fin P → β → α → ℂ)
    (hY : ∀ p c z, Y p z (ι' p c) = Function.extend (o p) (fun b => V p b c) 0 z)
    (c : Fin P → α) (y : Fin n → Fin d) :
    ((List.finRange P).map fun p => embedOp (W p) (Y p)).prod y
        (placeCfg W fun p => ι' p (c p)) =
      Function.extend (fun e : Fin P → β => placeCfg W fun p => o p (e p))
        (fun e => ∏ p, V p (e p) (c p)) 0 y := by
  classical
  have hWp := injective_window hW
  have hcomm : ((List.finRange P).toFinset : Set (Fin P)).Pairwise
      (Function.onFun Commute fun p => embedOp (W p) (Y p)) := fun p _ p' _ h =>
    commute_embedOp_of_disjoint (hWp p) (hWp p') (disjoint_range_window hW h) _ _
  rw [← Finset.noncommProd_toFinset (List.finRange P) _ hcomm (List.nodup_finRange P),
    noncommProd_embedOp_apply W hWp Y _ (fun p _ p' _ h => disjoint_range_window hW h)]
  simp only [List.toFinset_finRange, Finset.mem_univ, true_implies, placeCfg_comp hW, hY]
  have hinj : Function.Injective fun e : Fin P → β => placeCfg (d := d) W fun p => o p (e p) :=
    fun e e' h => funext fun p => ho p (congrFun (placeCfg_injective hW h) p)
  by_cases hy : ∃ e : Fin P → β, (placeCfg W fun p => o p (e p)) = y
  · obtain ⟨e, rfl⟩ := hy
    have hag : ∀ i, (∀ p j, W p j ≠ i) →
        (placeCfg W fun p => o p (e p)) i = (placeCfg W fun p => ι' p (c p)) i := fun i hi => by
      rw [placeCfg_apply_of_notMem _ hi, placeCfg_apply_of_notMem _ hi]
    rw [hinj.extend_apply, ite_eq_left hag]
    exact Finset.prod_congr rfl fun p _ => by
      rw [placeCfg_comp hW, (ho p).extend_apply]
  · rw [Function.extend_apply' _ _ _ hy, Pi.zero_apply]
    split_ifs with hag
    · by_contra hne
      apply hy
      have hall : ∀ p, ∃ b, o p b = y ∘ W p := by
        intro p
        by_contra hp
        simp only [not_exists] at hp
        exact hne (Finset.prod_eq_zero (Finset.mem_univ p) (by
          rw [Function.extend_apply' _ _ _ fun ⟨b, hb⟩ => hp b hb, Pi.zero_apply]))
      choose e he using hall
      refine ⟨e, ?_⟩
      rw [eq_placeCfg hW (z := y) fun i hi => by
        rw [hag i hi, placeCfg_apply_of_notMem _ hi]]
      simp only [he]
    · rfl


/-- **Columns along a product.** If the column of `M` at `x₀` is `f` placed by an injective `R`,
and `G` maps every `R a` to the column `g a` placed by an injective `R'`, then the column of
`G M` at `x₀` is `b ↦ ∑_a g a b f a` placed by `R'`. -/
theorem _root_.Matrix.mul_apply_extend {H α β : Type*} [Fintype H] [Fintype α]
    (G M : Matrix H H ℂ) (x₀ : H) {R : α → H} (hR : Function.Injective R) (f : α → ℂ)
    (hM : ∀ y, M y x₀ = Function.extend R f 0 y) {R' : β → H} (hR' : Function.Injective R')
    (g : α → β → ℂ) (hG : ∀ a y, G y (R a) = Function.extend R' (g a) 0 y) (y : H) :
    (G * M) y x₀ = Function.extend R' (fun b => ∑ a, g a b * f a) 0 y := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [hM]
  rw [sum_extend_zero hR f (fun z v => G y z * v) fun _ => mul_zero _]
  simp_rw [hG]
  by_cases hy : ∃ b, R' b = y
  · obtain ⟨b, rfl⟩ := hy
    simp only [hR'.extend_apply]
  · simp only [Function.extend_apply' _ _ _ hy, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

end QuantumCircuit
