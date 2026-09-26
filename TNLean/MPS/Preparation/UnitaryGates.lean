/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.GivensDecomposition

/-!
# Unitaries on a constant number of sites as products of two-site gates

Every unitary on an open chain of `n ≥ 2` sites of local dimension `d ≥ 1` is a product of
at most `K` unitary gates, each acting on two neighbouring sites, where `K` depends only on
`d` and `n` (`MPSPreparation.exists_isPairProduct`).

The proof combines three steps:

* a two-level rotation between configurations differing at one site is a controlled
  single-site operation (`MPSPreparation.twoLevel_update_eq_ctrlOp`), hence a product of
  two-site gates (`MPSPreparation.exists_isPairProduct_ctrlOp`);
* a two-level rotation between configurations `a`, `b` differing at more sites is conjugated
  to one between `a` and a configuration `c` closer to `a` by a two-level quarter turn on
  the pair `{c, b}` (`MPSPreparation.twoLevel_conj_quarterTwo`);
* the Givens decomposition writes a special unitary as a product of two-level rotations
  (`MPSPreparation.isTwoLevelWord_of_det_eq_one`), and a global phase is a single-site gate.

This is the step "can be further expressed with a low-depth circuit of local gates" of
arXiv:2307.01696 (caption of Fig. 1), for the unitaries with constant support of the
paragraph "The sequential-RG circuit".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexConjugate

namespace MPSPreparation

/-! ### Moving a two-level rotation by a quarter turn -/

section Conj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quarterTwo_isSpecialTwo : IsSpecialTwo quarterTwo :=
  Or.inl ⟨-Complex.I, by simp, quarterTwo_eq_rotTwo⟩

/-- The quarter turn `T` on the pair `{c, b}` sends `|b⟩ ↦ |c⟩` and `|c⟩ ↦ -|b⟩`, so it
conjugates the two-level operator on `{a, b}` to the one on `{a, c}`:
`T (twoLevel a b g) = (twoLevel a c g) T`. -/
theorem twoLevel_quarterTwo_mul {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel c b quarterTwo * twoLevel a b g = twoLevel a c g * twoLevel c b quarterTwo := by
  ext x y
  rw [twoLevel_mul_apply (Ne.symm hbc), twoLevel_mul_apply hac]
  simp only [twoLevel, of_apply, twoLevelIdx, quarterTwo, cons_val', cons_val_zero,
    cons_val_one, head_cons, empty_val', cons_val_fin_one, head_fin_const]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;> by_cases hyc : y = c <;>
    simp_all [eq_comm]

/-- `twoLevel a b g = T† (twoLevel a c g) T` for the quarter turn `T` on `{c, b}`. -/
theorem twoLevel_conj_quarterTwo {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel a b g =
      star (twoLevel c b quarterTwo) * twoLevel a c g * twoLevel c b quarterTwo := by
  have hT := twoLevel_mem_unitary (ι := ι) (Ne.symm hbc) quarterTwo_mem_unitary
  rw [Matrix.mul_assoc, ← twoLevel_quarterTwo_mul hab hac hbc, ← Matrix.mul_assoc,
    Unitary.star_mul_self_of_mem hT, Matrix.one_mul]

end Conj

/-! ### Two-level rotations between configurations of the chain -/

variable {d n : ℕ}

/-- The number of sites at which two configurations differ. -/
def hammingDist' (a b : Cfg d n) : ℕ := (Finset.univ.filter fun i => a i ≠ b i).card

theorem hammingDist'_le (a b : Cfg d n) : hammingDist' a b ≤ n := by
  unfold hammingDist'
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem hammingDist'_pos {a b : Cfg d n} (hab : a ≠ b) : 0 < hammingDist' a b := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

/-- **Two-level rotations are products of two-site gates.** For `d ≥ 1` and `n ≥ 2` there is
`K` such that every two-level rotation or phase between two distinct configurations of the
chain of `n` sites is a product of at most `K` gates on neighbouring sites. -/
theorem exists_isPairProduct_twoLevel (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ K, ∀ a b : Cfg d n, a ≠ b → ∀ g, IsSpecialTwo g →
      IsPairProduct d n K (twoLevel a b g) := by
  obtain ⟨K₁, hK₁⟩ := exists_isPairProduct_ctrlOp hd hn n
  -- configurations differing at exactly one site
  have hone : ∀ (a : Cfg d n) (t : Fin n) (β : Fin d), β ≠ a t → ∀ g, IsSpecialTwo g →
      IsPairProduct d n K₁ (twoLevel a (Function.update a t β) g) := by
    intro a t β hβ g hg
    rw [twoLevel_update_eq_ctrlOp a t hβ g]
    exact hK₁ _ ((Finset.card_le_univ _).trans (by simp)) t (by simp) a (a t) β
      (Ne.symm hβ) g hg
  have key : ∀ h : ℕ, ∀ a b : Cfg d n, hammingDist' a b = h + 1 → ∀ g, IsSpecialTwo g →
      IsPairProduct d n ((2 * h + 1) * K₁) (twoLevel a b g) := by
    intro h
    induction h with
    | zero =>
      intro a b hab g hg
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hab
      have hb : b = Function.update a t (b t) := by
        funext i
        by_cases hi : i = t
        · subst hi; simp
        · rw [Function.update_of_ne hi]
          by_contra h'
          have : i ∈ Finset.univ.filter fun i => a i ≠ b i := by simp [Ne.symm h']
          rw [ht] at this
          exact hi (Finset.mem_singleton.mp this)
      have hbt : b t ≠ a t := by
        have : t ∈ Finset.univ.filter fun i => a i ≠ b i := by rw [ht]; simp
        simpa [eq_comm] using this
      rw [hb]
      simpa using hone a t (b t) hbt g hg
    | succ h ih =>
      intro a b hab g hg
      obtain ⟨t, ht⟩ : (Finset.univ.filter fun i => a i ≠ b i).Nonempty :=
        Finset.card_pos.mp (by unfold hammingDist' at hab; omega)
      have hat : a t ≠ b t := (Finset.mem_filter.mp ht).2
      set c := Function.update b t (a t) with hc
      have hfilter : (Finset.univ.filter fun i => a i ≠ c i) =
          (Finset.univ.filter fun i => a i ≠ b i).erase t := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hc]
        by_cases hi : i = t
        · subst hi; simp
        · simp [Function.update_of_ne hi, hi]
      have hac' : hammingDist' a c = h + 1 := by
        unfold hammingDist'
        rw [hfilter, Finset.card_erase_of_mem ht]
        unfold hammingDist' at hab
        omega
      have hac : a ≠ c := fun h' => by
        have := hammingDist'_pos (a := a) (b := c)
        rw [hac'] at this
        rw [← h'] at hac'
        simp [hammingDist'] at hac'
      have hbc : b ≠ c := fun h' => by
        have := congrFun h' t
        rw [hc, Function.update_self] at this
        exact hat this.symm
      have hab' : a ≠ b := fun h' => by rw [h'] at hat; exact hat rfl
      have hcb : b = Function.update c t (b t) := by
        rw [hc, Function.update_idem, Function.update_eq_self]
      have hT : IsPairProduct d n K₁ (twoLevel c b quarterTwo) := by
        have hbt : b t ≠ c t := by rw [hc, Function.update_self]; exact Ne.symm hat
        rw [hcb]
        simpa using hone c t (b t) hbt _ quarterTwo_isSpecialTwo
      rw [twoLevel_conj_quarterTwo hab' hac hbc g]
      have := (hT.star.mul (ih a c hac' g hg)).mul hT
      refine this.mono (le_of_eq ?_)
      ring
  refine ⟨(2 * n + 1) * K₁, fun a b hab g hg => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h, hammingDist' a b = h + 1 :=
    ⟨hammingDist' a b - 1, by have := hammingDist'_pos hab; omega⟩
  refine (key h a b hh g hg).mono (Nat.mul_le_mul_right _ ?_)
  have := hammingDist'_le a b
  omega

/-- A global phase `μ • 1` with `|μ| = 1` is a product of at most `2n` gates on neighbouring
sites. -/
theorem isPairProduct_smul_one (hd : 0 < d) (hn : 2 ≤ n) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    IsPairProduct d n (2 * n) (μ • (1 : Matrix (Cfg d n) (Cfg d n) ℂ)) := by
  have hu : μ • (1 : Matrix (Cfg d n) (Cfg d n) ℂ) ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
    rw [Unitary.mem_iff, star_smul, star_one, smul_mul_smul_comm, smul_mul_smul_comm,
      Matrix.one_mul, Complex.star_def, Complex.conj_mul', Complex.mul_conj', hμ]
    simp
  refine isPairProduct_of_mem_supportedOperators_card_le_two hd hn (T := ∅) (by simp) hu ?_
  exact Submodule.smul_mem _ _ (one_mem_supportedOperators _)

/-- **Unitaries on a constant number of sites.** For `d ≥ 1` and `n ≥ 2` there is `K`
such that every unitary on the open chain of `n` sites is a product of at most `K` unitary
gates, each acting on two neighbouring sites.

arXiv:2307.01696, caption of Fig. 1: the unitaries with constant support "can be further
expressed with a low-depth circuit of local gates". -/
theorem exists_isPairProduct (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ K, ∀ X : Matrix (Cfg d n) (Cfg d n) ℂ, X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) →
      IsPairProduct d n K X := by
  obtain ⟨K₂, hK₂⟩ := exists_isPairProduct_twoLevel hd hn
  set m := Fintype.card (Cfg d n)
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hd⟩⟩
  refine ⟨2 * n + 3 * m * m * K₂, fun X hX => ?_⟩
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq X.det hm
  have hdetn : ‖X.det‖ = 1 := by
    have h := congrArg det (Unitary.star_mul_self_of_mem hX)
    rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose, Complex.star_def,
      Complex.conj_mul'] at h
    exact_mod_cast (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (by exact_mod_cast h)
  have hμn : ‖μ‖ = 1 := by
    have h : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hμ, hdetn]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hμ0 : μ ≠ 0 := fun h => by simp [h] at hμn
  set X' := μ⁻¹ • X with hX'
  have hX'u : X' ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
    have hu := isPairProduct_smul_one (d := d) hd hn (μ := μ⁻¹) (by simp [hμn])
    have : X' = (μ⁻¹ • (1 : Matrix (Cfg d n) (Cfg d n) ℂ)) * X := by
      rw [hX', smul_mul_assoc, Matrix.one_mul]
    rw [this]
    exact Submonoid.mul_mem _ hu.mem_unitary hX
  have hX'det : X'.det = 1 := by
    rw [hX', det_smul, inv_pow, hμ, inv_mul_cancel₀]
    intro h; rw [h] at hdetn; simp at hdetn
  obtain ⟨l, hl, hlg, hlX⟩ := isTwoLevelWord_of_det_eq_one hX'u hX'det
  have hprod : IsPairProduct d n (l.length * K₂)
      (l.map fun p => twoLevel p.1 p.2.1 p.2.2).prod := by
    have := IsPairProduct.list_prod (K := K₂) (l.map fun p => twoLevel p.1 p.2.1 p.2.2)
      (fun Y hY => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hY
        exact hK₂ _ _ (hlg p hp).1 _ (hlg p hp).2)
    simpa using this
  have hXeq : X = (μ • (1 : Matrix (Cfg d n) (Cfg d n) ℂ)) * X' := by
    rw [hX', smul_mul_assoc, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  rw [hXeq, hlX]
  refine ((isPairProduct_smul_one hd hn hμn).mul hprod).mono ?_
  have : l.length * K₂ ≤ 3 * m * m * K₂ := Nat.mul_le_mul_right _ hl
  omega

end MPSPreparation
