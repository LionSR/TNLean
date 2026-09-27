/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import TNLean.MPS.Preparation.ControlledGates

/-!
# Controlled two-level rotations as products of two-site gates

On a chain of `n ≥ 2` sites, a single-site two-level rotation or phase at a site `t`,
controlled by the configuration of a set `S` of other sites, is a product of a number of
two-site gates on neighbouring sites that depends only on `|S|` and `n`. The proof removes one
control site at a time: every two-level rotation `rotTwo z` and every phase `diagTwo ν` is a
group commutator `g₁ g₂ g₁† g₂†` with `g₁` of the same kind, and a controlled commutator is a
product of two controlled operations with one control site fewer and two operations acting on
two sites (`MPSPreparation.ctrlOp_insert_commutator`).

This is the step "can be further expressed with a low-depth circuit of local gates" of
arXiv:2307.01696 (caption of Fig. 1), applied to the operations with constant support
of the paragraph "The sequential-RG circuit".

## Main results

* `MPSPreparation.isPairProduct_of_mem_supportedOperators_card_le_two` — a unitary acting on
  at most two sites is a product of at most `2n` gates on neighbouring sites.
* `MPSPreparation.exists_isPairProduct_ctrlOp` — controlled two-level rotations and phases
  with at most `k` control sites are products of at most `K` gates on neighbouring sites.
* `MPSPreparation.twoLevel_update_eq_ctrlOp` — the two-level operator between configurations
  differing at one site is such a controlled operation with all other sites as controls.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexConjugate

namespace MPSPreparation

variable {d n : ℕ}

/-! ### Operators on at most two sites -/

theorem exists_ne_of_two_le (hn : 2 ≤ n) (a : Fin n) : ∃ b : Fin n, b ≠ a := by
  by_cases h : a.val = 0
  · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
  · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩

theorem exists_pair_superset (hn : 2 ≤ n) {T : Finset (Fin n)} (hT : T.card ≤ 2) :
    ∃ s t : Fin n, s ≠ t ∧ (T : Set (Fin n)) ⊆ {s, t} := by
  rcases Nat.lt_or_ge T.card 2 with h | h
  · rcases Nat.lt_or_ge T.card 1 with h' | h'
    · rw [Nat.lt_one_iff, Finset.card_eq_zero] at h'
      subst h'
      exact ⟨(⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n), by simp [Fin.ext_iff], by simp⟩
    · obtain ⟨a, rfl⟩ := (Finset.card_eq_one (s := T)).mp (by omega)
      obtain ⟨b, hb⟩ := exists_ne_of_two_le hn a
      exact ⟨a, b, Ne.symm hb, by simp⟩
  · obtain ⟨a, b, hab, rfl⟩ := (Finset.card_eq_two (s := T)).mp (by omega)
    exact ⟨a, b, hab, by simp⟩

/-- A unitary acting on at most two sites is a product of at most `2n` gates on neighbouring
sites. -/
theorem isPairProduct_of_mem_supportedOperators_card_le_two (hd : 0 < d) (hn : 2 ≤ n)
    {T : Finset (Fin n)} (hT : T.card ≤ 2) {Z : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hZu : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZ : Z ∈ supportedOperators d (T : Set (Fin n))) : IsPairProduct d n (2 * n) Z := by
  obtain ⟨s, t, hst, hsub⟩ := exists_pair_superset hn hT
  exact isPairProduct_of_mem_supportedOperators_pair hd hst hZu (supportedOperators_mono hsub hZ)

/-! ### The two-level targets -/

/-- The `2 × 2` targets of the controlled operations: real rotations and diagonal phases. -/
def IsSpecialTwo (g : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∃ z : ℂ, ‖z‖ = 1 ∧ g = rotTwo z) ∨ ∃ ν : ℂ, ‖ν‖ = 1 ∧ g = diagTwo ν

theorem IsSpecialTwo.mem_unitary {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    g ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases hg with ⟨z, hz, rfl⟩ | ⟨ν, hν, rfl⟩
  · exact rotTwo_mem_unitary hz
  · exact diagTwo_mem_unitary hν

theorem diagTwo_conjTranspose (ν : ℂ) : (diagTwo ν)ᴴ = diagTwo (star ν) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo, conjTranspose_apply]

theorem IsSpecialTwo.conjTranspose {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    IsSpecialTwo gᴴ := by
  rcases hg with ⟨z, hz, rfl⟩ | ⟨ν, hν, rfl⟩
  · exact Or.inl ⟨conj z, by simpa using hz, rotTwo_conjTranspose z⟩
  · exact Or.inr ⟨star ν, by simpa using hν, diagTwo_conjTranspose ν⟩

theorem exists_sq_eq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ∃ w : ℂ, ‖w‖ = 1 ∧ w * w = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z two_pos
  refine ⟨w, ?_, by rw [← hw]; ring⟩
  have h : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw, hz]
  nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - 1)]

/-- Every target is a group commutator `g₁ g₂ g₁† g₂†` with `g₁` a target and `g₂` unitary. -/
theorem IsSpecialTwo.exists_commutator {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    ∃ g₁ g₂ : Matrix (Fin 2) (Fin 2) ℂ, IsSpecialTwo g₁ ∧
      g₂ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ g = g₁ * g₂ * star g₁ * star g₂ := by
  rcases hg with ⟨z, hz, rfl⟩ | ⟨ν, hν, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := exists_sq_eq_of_norm_eq_one hz
    refine ⟨rotTwo w, phaseTwo, Or.inl ⟨w, hw, rfl⟩, phaseTwo_mem_unitary, ?_⟩
    rw [rotTwo_sq_eq_commutator, star_eq_conjTranspose, rotTwo_conjTranspose]; rfl
  · obtain ⟨w, hw, rfl⟩ := exists_sq_eq_of_norm_eq_one hν
    refine ⟨diagTwo w, quarterTwo, Or.inr ⟨w, hw, rfl⟩, quarterTwo_mem_unitary, ?_⟩
    rw [diagTwo_sq_eq_commutator, star_eq_conjTranspose, diagTwo_conjTranspose]; rfl

/-! ### Removing the controls one by one -/

/-- **Controlled two-level operations are products of two-site gates.** For every number `k`
of control sites there is `K` such that every single-site two-level rotation or phase at a
site `t`, controlled by the configuration of at most `k` other sites, is a product of at most
`K` gates on neighbouring sites of the chain of `n ≥ 2` sites. -/
theorem exists_isPairProduct_ctrlOp (hd : 0 < d) (hn : 2 ≤ n) (k : ℕ) :
    ∃ K, ∀ S : Finset (Fin n), S.card ≤ k → ∀ t, t ∉ S → ∀ (c : Cfg d n) (α β : Fin d),
      α ≠ β → ∀ g, IsSpecialTwo g → IsPairProduct d n K (ctrlOp S c t (twoLevel α β g)) := by
  induction k with
  | zero =>
    refine ⟨2 * n, fun S hS t _ c α β hαβ g hg => ?_⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hS
    subst hS
    rw [ctrlOp_empty]
    exact isPairProduct_of_mem_supportedOperators_card_le_two hd hn
      (T := {t}) (by simp) (siteOp_mem_unitary t (twoLevel_mem_unitary hαβ hg.mem_unitary))
      (by simpa using siteOp_mem_supportedOperators t _)
  | succ k ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨2 * K + 2 * (2 * n), fun S hS t ht c α β hαβ g hg => ?_⟩
    rcases Nat.lt_or_ge k S.card with hk | hk
    swap
    · exact (hK S hk t ht c α β hαβ g hg).mono (by omega)
    obtain ⟨s, hs⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    set S' := S.erase s
    have hS' : S'.card ≤ k := by rw [Finset.card_erase_of_mem hs]; omega
    have hsS' : s ∉ S' := Finset.notMem_erase s S
    have htS' : t ∉ S' := fun h => ht (Finset.mem_of_mem_erase h)
    have hst : s ≠ t := fun h => ht (h ▸ hs)
    obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := hg.exists_commutator
    have hV := twoLevel_mem_unitary hαβ hg₁.mem_unitary
    have hW := twoLevel_mem_unitary (ι := Fin d) hαβ hg₂
    have heq : twoLevel α β (g₁ * g₂ * star g₁ * star g₂) =
        twoLevel α β g₁ * twoLevel α β g₂ * star (twoLevel α β g₁) *
          star (twoLevel α β g₂) := by
      rw [star_eq_conjTranspose (twoLevel α β g₁), star_eq_conjTranspose (twoLevel α β g₂),
        twoLevel_conjTranspose, twoLevel_conjTranspose, twoLevel_mul hαβ, twoLevel_mul hαβ,
        twoLevel_mul hαβ]; rfl
    rw [heq, ← Finset.insert_erase hs, ctrlOp_insert_commutator htS' hst c hV hW]
    have hsingle : ∀ u : Matrix (Fin d) (Fin d) ℂ, u ∈ unitary (Matrix (Fin d) (Fin d) ℂ) →
        IsPairProduct d n (2 * n) (ctrlOp {s} c t u) := fun u hu =>
      isPairProduct_of_mem_supportedOperators_card_le_two hd hn (T := {t, s})
        (Finset.card_le_two) (ctrlOp_mem_unitary (by simpa using Ne.symm hst) c hu)
        (by simpa using ctrlOp_mem_supportedOperators {s} c t u)
    have h1 := hK S' hS' t htS' c α β hαβ g₁ hg₁
    have h2 : IsPairProduct d n K (ctrlOp S' c t (star (twoLevel α β g₁))) := by
      rw [star_eq_conjTranspose, twoLevel_conjTranspose]
      exact hK S' hS' t htS' c α β hαβ _ hg₁.conjTranspose
    have := ((h1.mul (hsingle _ hW)).mul h2).mul (hsingle _ (Unitary.star_mem hW))
    exact this.mono (by omega)

/-! ### Two-level operators between neighbouring configurations -/

/-- The two-level operator between the configurations `a` and `a` with the site `t` changed to
`β` acts as the two-level operator between the levels `a t` and `β` at the site `t`,
controlled by all other sites being in the configuration `a`. -/
theorem twoLevel_update_eq_ctrlOp (a : Cfg d n) (t : Fin n) {β : Fin d} (hβ : β ≠ a t)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel a (Function.update a t β) g =
      ctrlOp (Finset.univ.erase t) a t (twoLevel (a t) β g) := by
  set a' := Function.update a t β
  have ha' : ∀ i, i ≠ t → a' i = a i := fun i hi => Function.update_of_ne hi _ _
  have hat : a' t = β := Function.update_self _ _ _
  have hag : ∀ z w : Cfg d n, AgreeOff ![t] z w ↔ ∀ i, i ≠ t → z i = w i := fun z w => by
    constructor
    · intro h i hi; exact h i fun j hj => hi (by rw [← hj]; fin_cases j; rfl)
    · intro h i hi; exact h i fun hit => hi 0 (by rw [hit]; rfl)
  have hmem : ∀ z : Cfg d n, (z = a ∨ z = a') ↔ ((∀ i, i ≠ t → z i = a i) ∧
      (z t = a t ∨ z t = β)) := fun z => by
    constructor
    · rintro (rfl | rfl)
      · exact ⟨fun _ _ => rfl, Or.inl rfl⟩
      · exact ⟨ha', Or.inr hat⟩
    · rintro ⟨hz, hzt | hzt⟩
      · left; funext i; by_cases hi : i = t
        · subst hi; exact hzt
        · exact hz i hi
      · right; funext i; by_cases hi : i = t
        · subst hi; rw [hat]; exact hzt
        · rw [ha' i hi]; exact hz i hi
  have hidx : ∀ z : Cfg d n, (∀ i, i ≠ t → z i = a i) →
      twoLevelIdx a z = twoLevelIdx (a t) (z t) := fun z hz => by
    unfold twoLevelIdx
    by_cases hzt : z t = a t
    · rw [ite_eq_left hzt, ite_eq_left]; funext i; by_cases hi : i = t
      · subst hi; exact hzt
      · exact hz i hi
    · rw [ite_eq_right hzt, ite_eq_right]; rintro rfl; exact hzt rfl
  have hsite : ∀ x y : Cfg d n, siteOp t (twoLevel (a t) β g) x y =
      if AgreeOff ![t] x y then twoLevel (a t) β g (x t) (y t) else 0 := fun x y => rfl
  ext x y
  rw [ctrlOp, ctrlElem, Matrix.add_apply, Matrix.sub_apply, ctrlProj, diagonal_mul, hsite,
    one_apply, diagonal_apply]
  by_cases hx : ∀ i, i ∈ Finset.univ.erase t → x i = a i
  · have hx' : ∀ i, i ≠ t → x i = a i := fun i hi => hx i (by simp [hi])
    rw [ite_eq_left hx, one_mul]
    have hcancel : ((if x = y then (1 : ℂ) else 0) - if x = y then 1 else 0) = 0 := sub_self _
    simp only [hcancel, add_zero]
    by_cases hy : ∀ i, i ≠ t → y i = a i
    · have hxy : AgreeOff ![t] x y := (hag x y).2 fun i hi => (hx' i hi).trans (hy i hi).symm
      rw [ite_eq_left hxy]
      have e1 : (x = a ∨ x = a') ↔ (x t = a t ∨ x t = β) := by
        rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hx', h⟩⟩
      have e2 : (y = a ∨ y = a') ↔ (y t = a t ∨ y t = β) := by
        rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
      have e3 : x = y ↔ x t = y t := ⟨fun h => h ▸ rfl, fun h => funext fun i => by
        by_cases hi : i = t
        · subst hi; exact h
        · rw [hx' i hi, hy i hi]⟩
      simp only [twoLevel, of_apply, e1, e2, e3, hidx x hx', hidx y hy]
    · have hxy : ¬AgreeOff ![t] x y := fun h =>
        hy fun i hi => ((hag x y).1 h i hi).symm.trans (hx' i hi)
      rw [ite_eq_right hxy]
      rw [twoLevel_apply_of_not_mem_right g x (fun h => hy ((hmem y).1 h).1)]
      rw [ite_eq_right]; rintro rfl; exact hy hx'
  · have hx' : ¬∀ i, i ≠ t → x i = a i := fun h => hx fun i hi => h i (Finset.ne_of_mem_erase hi)
    rw [ite_eq_right hx, zero_mul, zero_add]
    rw [twoLevel_apply_of_not_mem_left g (fun h => hx' ((hmem x).1 h).1)]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]

end MPSPreparation
