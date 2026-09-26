/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PairProduct
import TNLean.MPS.Preparation.TwoLevel

/-!
# Controlled single-site operations

On a chain of `n` sites, the operation "apply `u` at the site `t` when the sites of `S` are in
the configuration `c`" is `C(p, U) = p U + (1 - p)`, where `p` is the projection onto the
configurations agreeing with `c` on `S` and `U = u` at `t`. This file develops the algebra of
these operations used to write a unitary on a constant number of sites as a product of
two-site gates:

* in any ring, for commuting idempotents `p₁`, `p₂` and invertible `v`, `w` commuting with
  them, `C(p₁ p₂, v w v⁻¹ w⁻¹) = C(p₁, v) C(p₂, w) C(p₁, v⁻¹) C(p₂, w⁻¹)`
  (`MPSPreparation.ctrlElem_commutator`), which lowers the number of control sites by one;
* the projections, single-site operators, and controlled operators on the chain, with their
  supports and unitarity.

The decomposition of gates acting on a constant number of sites into two-site gates is the
step "can be further expressed with a low-depth circuit of local gates" of arXiv:2307.01696
(caption of Fig. 1 and paragraph "The sequential-RG circuit").
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

/-! ### Controlled elements of a ring -/

section Ring

variable {R : Type*} [Ring R]

/-- The controlled element `C(p, x) = p x + (1 - p)`. -/
def ctrlElem (p x : R) : R := p * x + (1 - p)

theorem ctrlElem_one (p : R) : ctrlElem p 1 = 1 := by
  simp [ctrlElem]

theorem ctrlElem_ctrlElem (p₁ p₂ w : R) :
    ctrlElem p₁ (ctrlElem p₂ w) = ctrlElem (p₁ * p₂) w := by
  simp only [ctrlElem]; noncomm_ring

theorem one_sub_mul_self_of_isIdempotentElem {p : R} (hp : IsIdempotentElem p) :
    (1 - p) * p = 0 := by
  rw [sub_mul, one_mul, hp.eq, sub_self]

theorem mul_one_sub_self_of_isIdempotentElem {p : R} (hp : IsIdempotentElem p) :
    p * (1 - p) = 0 := by
  rw [mul_sub, mul_one, hp.eq, sub_self]

/-- For `p` idempotent and commuting with `x`, `C(p, x) C(p, y) = C(p, x y)`. -/
theorem ctrlElem_mul {p x y : R} (hp : IsIdempotentElem p) (hx : Commute p x) :
    ctrlElem p x * ctrlElem p y = ctrlElem p (x * y) := by
  have h1 : p * x * (p * y) = p * (x * y) := by
    rw [mul_assoc, ← mul_assoc x p y, ← hx.eq, mul_assoc, ← mul_assoc p p, hp.eq]
  have h2 : p * x * (1 - p) = 0 := by
    rw [mul_assoc, mul_sub, mul_one, ← hx.eq, mul_sub, ← mul_assoc p p x, hp.eq, sub_self]
  have h3 : (1 - p) * (p * y) = 0 := by
    rw [← mul_assoc, one_sub_mul_self_of_isIdempotentElem hp, zero_mul]
  have h4 : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, one_mul, mul_one_sub_self_of_isIdempotentElem hp, sub_zero]
  calc ctrlElem p x * ctrlElem p y
      = p * x * (p * y) + p * x * (1 - p) + (1 - p) * (p * y) + (1 - p) * (1 - p) := by
        simp only [ctrlElem]; noncomm_ring
    _ = ctrlElem p (x * y) := by rw [h1, h2, h3, h4, ctrlElem]; abel

/-- Conjugating a controlled element by an invertible element commuting with the control. -/
theorem conj_ctrlElem {p v v' : R} (w : R) (hv : Commute p v) (hvv : v * v' = 1) :
    v * ctrlElem p w * v' = ctrlElem p (v * w * v') := by
  have h : p * v * v' = p := by rw [mul_assoc, hvv, mul_one]
  calc v * ctrlElem p w * v' = v * p * w * v' + v * v' - v * p * v' := by
        simp only [ctrlElem]; noncomm_ring
    _ = ctrlElem p (v * w * v') := by
        rw [← hv.eq, h, hvv, ctrlElem]; noncomm_ring

theorem commute_ctrlElem {p q x : R} (hpq : Commute p q) (hpx : Commute p x) :
    Commute p (ctrlElem q x) :=
  (hpq.mul_right hpx).add_right ((Commute.one_right p).sub_right hpq)

/-- **Controlled commutators.** For commuting idempotents `p₁`, `p₂` and elements `v`, `w`
with right inverses `v'`, `w'`, where `p₁` commutes with `v`, `w` and `p₂` with `v`, `v'`, `w`,
`C(p₁ p₂, v w v' w') = C(p₁, v) C(p₂, w) C(p₁, v') C(p₂, w')`. -/
theorem ctrlElem_commutator {p₁ p₂ v v' w w' : R} (hp₁ : IsIdempotentElem p₁)
    (hp₂ : IsIdempotentElem p₂) (h12 : Commute p₁ p₂) (h1v : Commute p₁ v)
    (h1w : Commute p₁ w) (h2v : Commute p₂ v) (h2v' : Commute p₂ v')
    (h2w : Commute p₂ w) (hvv : v * v' = 1) (hww : w * w' = 1) :
    ctrlElem p₁ v * ctrlElem p₂ w * ctrlElem p₁ v' * ctrlElem p₂ w' =
      ctrlElem (p₁ * p₂) (v * w * v' * w') := by
  set A := ctrlElem p₁ v
  set A' := ctrlElem p₁ v'
  have hAA : A * A' = 1 := by rw [ctrlElem_mul hp₁ h1v, hvv, ctrlElem_one]
  have h2A : Commute p₂ A := commute_ctrlElem h12.symm h2v
  have h2A' : Commute p₂ A' := commute_ctrlElem h12.symm h2v'
  -- `A w A' = p₁ (v w v') + (1 - p₁) w`.
  have hAw : A * w * A' = p₁ * (v * w * v') + (1 - p₁) * w := by
    have e1 : p₁ * v * w * (p₁ * v') = p₁ * (v * w * v') := by
      rw [mul_assoc (p₁ * v) w, ← mul_assoc w p₁, ← h1w.eq, mul_assoc p₁ w v', ← mul_assoc,
        mul_assoc p₁ v p₁, ← h1v.eq, ← mul_assoc p₁ p₁, hp₁.eq]
      simp only [mul_assoc]
    have e2 : p₁ * v * w * (1 - p₁) = 0 := by
      rw [mul_sub, mul_one, mul_assoc (p₁ * v) w p₁, ← h1w.eq, ← mul_assoc, mul_assoc p₁ v p₁,
        ← h1v.eq, ← mul_assoc p₁ p₁, hp₁.eq, sub_self]
    have e3 : (1 - p₁) * w * (p₁ * v') = 0 := by
      rw [mul_assoc (1 - p₁) w, ← mul_assoc w p₁, ← h1w.eq, mul_assoc, ← mul_assoc (1 - p₁),
        one_sub_mul_self_of_isIdempotentElem hp₁, zero_mul]
    have e4 : (1 - p₁) * w * (1 - p₁) = (1 - p₁) * w := by
      rw [mul_assoc, mul_sub, mul_one, ← h1w.eq, mul_sub, ← mul_assoc (1 - p₁) p₁ w,
        one_sub_mul_self_of_isIdempotentElem hp₁, zero_mul, sub_zero]
    calc A * w * A' = p₁ * v * w * (p₁ * v') + p₁ * v * w * (1 - p₁) +
          (1 - p₁) * w * (p₁ * v') + (1 - p₁) * w * (1 - p₁) := by
          simp only [A, A', ctrlElem]; noncomm_ring
      _ = p₁ * (v * w * v') + (1 - p₁) * w := by rw [e1, e2, e3, e4]; abel
  have hAwA : A * w * A' * w' = ctrlElem p₁ (v * w * v' * w') := by
    rw [hAw, add_mul, mul_assoc (1 - p₁), hww, mul_one, mul_assoc p₁, ctrlElem]
  have h2u : Commute p₂ (A * w * A') := (h2A.mul_right h2w).mul_right h2A'
  calc A * ctrlElem p₂ w * A' * ctrlElem p₂ w'
      = ctrlElem p₂ (A * w * A') * ctrlElem p₂ w' := by rw [conj_ctrlElem w h2A hAA]
    _ = ctrlElem p₂ (ctrlElem p₁ (v * w * v' * w')) := by
        rw [ctrlElem_mul hp₂ h2u, hAwA]
    _ = ctrlElem (p₁ * p₂) (v * w * v' * w') := by rw [ctrlElem_ctrlElem, h12.eq]

end Ring

/-! ### Projections, single-site operators, and controlled operators on a chain -/

variable {d n : ℕ}

/-- The projection onto the configurations `x` with `x i = c i` for every `i ∈ S`.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
decomposed into local gates). -/
def ctrlProj (S : Finset (Fin n)) (c : Cfg d n) : Matrix (Cfg d n) (Cfg d n) ℂ :=
  diagonal fun x => if ∀ i ∈ S, x i = c i then 1 else 0

theorem isIdempotentElem_ctrlProj (S : Finset (Fin n)) (c : Cfg d n) :
    IsIdempotentElem (ctrlProj S c) := by
  unfold IsIdempotentElem ctrlProj
  rw [diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

theorem commute_ctrlProj (S S' : Finset (Fin n)) (c c' : Cfg d n) :
    Commute (ctrlProj S c) (ctrlProj S' c') := by
  unfold Commute SemiconjBy ctrlProj
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext x; ring

theorem ctrlProj_insert {s : Fin n} (S : Finset (Fin n)) (c : Cfg d n) :
    ctrlProj (insert s S) c = ctrlProj S c * ctrlProj {s} c := by
  unfold ctrlProj
  rw [diagonal_mul_diagonal]
  congr 1; funext x
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  by_cases h1 : x s = c s <;> by_cases h2 : ∀ i ∈ S, x i = c i <;> simp [h1, h2]

@[simp] theorem ctrlProj_empty (c : Cfg d n) : ctrlProj ∅ c = 1 := by
  simp [ctrlProj]

theorem ctrlProj_conjTranspose (S : Finset (Fin n)) (c : Cfg d n) :
    (ctrlProj S c)ᴴ = ctrlProj S c := by
  unfold ctrlProj
  rw [diagonal_conjTranspose]
  congr 1; funext x; simp only [Pi.star_apply]; split_ifs <;> simp

theorem ctrlProj_mem_supportedOperators (S : Finset (Fin n)) (c : Cfg d n) :
    ctrlProj S c ∈ supportedOperators d (S : Set (Fin n)) := by
  classical
  have : ctrlProj S c = finKronecker fun i =>
      if i ∈ S then diagonal (fun a : Fin d => if a = c i then (1 : ℂ) else 0) else 1 := by
    ext x y
    simp only [ctrlProj, finKronecker_apply, diagonal_apply]
    have hfac : ∀ i, (if i ∈ S then diagonal (fun a : Fin d => if a = c i then (1 : ℂ) else 0)
        else 1) (x i) (y i) = (if x i = y i then 1 else 0) *
          (if i ∈ S then (if x i = c i then 1 else 0) else 1) := fun i => by
      split_ifs <;> simp_all [diagonal_apply, one_apply]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_boole,
      Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_boole]
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp only [hxy, ite_false]
      simp only [Finset.mem_univ, forall_const]
      have : ¬∀ i, x i = y i := fun h => hxy (funext h)
      simp [this]
  rw [this]
  exact finKronecker_mem_supportedOperators fun i hi => by
    rw [ite_eq_right (by simpa using hi)]

/-- The operator `u` at the site `t`.

Source: arXiv:2307.01696, main text before Theorem 1 (local gates). -/
noncomputable def siteOp (t : Fin n) (u : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Cfg d n) (Cfg d n) ℂ :=
  embedOp ![t] (u.submatrix (Equiv.funUnique (Fin 1) (Fin d)) (Equiv.funUnique (Fin 1) (Fin d)))

theorem siteSites_injective (t : Fin n) : Function.Injective ![t] := by
  intro a b _; exact Subsingleton.elim a b

theorem siteOp_mul (t : Fin n) (u v : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t u * siteOp t v = siteOp t (u * v) := by
  rw [siteOp, siteOp, embedOp_mul (siteSites_injective t), submatrix_mul_equiv, siteOp]

@[simp] theorem siteOp_one (t : Fin n) : siteOp (d := d) t 1 = 1 := by
  rw [siteOp, submatrix_one_equiv, embedOp_one]

theorem siteOp_conjTranspose (t : Fin n) (u : Matrix (Fin d) (Fin d) ℂ) :
    (siteOp t u)ᴴ = siteOp t uᴴ := by
  rw [siteOp, embedOp_conjTranspose, conjTranspose_submatrix, siteOp]

theorem siteOp_star (t : Fin n) (u : Matrix (Fin d) (Fin d) ℂ) :
    star (siteOp t u) = siteOp t (star u) :=
  siteOp_conjTranspose t u

theorem siteOp_mem_unitary (t : Fin n) {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : u ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    siteOp t u ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
  rw [Unitary.mem_iff] at hu ⊢
  rw [siteOp_star, siteOp_mul, siteOp_mul, hu.1, hu.2, siteOp_one]
  exact ⟨rfl, rfl⟩

theorem siteOp_mem_supportedOperators (t : Fin n) (u : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t u ∈ supportedOperators d {t} := by
  have := embedOp_mem_supportedOperators (siteSites_injective t)
    (u.submatrix (Equiv.funUnique (Fin 1) (Fin d)) (Equiv.funUnique (Fin 1) (Fin d)))
  rwa [Matrix.range_cons, Matrix.range_empty, Set.union_empty] at this

theorem siteOp_diagonal (t : Fin n) (f : Fin d → ℂ) :
    siteOp t (diagonal f) = diagonal fun x : Cfg d n => f (x t) := by
  ext x y
  simp only [siteOp, embedOp_apply, submatrix_apply, Function.comp_apply,
    Equiv.funUnique_apply]
  have hiff : (AgreeOff ![t] x y ∧ x t = y t) ↔ x = y := by
    constructor
    · rintro ⟨h, ht⟩
      funext i
      by_cases hi : i = t
      · subst hi; exact ht
      · exact h i fun j hj => hi (by rw [← hj]; fin_cases j; rfl)
    · rintro rfl; exact ⟨agreeOff_refl _ _, rfl⟩
  simp only [Fin.default_eq_zero, Matrix.cons_val_zero, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp [agreeOff_refl]
  · rw [ite_eq_right hxy]
    by_cases h1 : AgreeOff ![t] x y
    · rw [ite_eq_left h1]
      have h2 : x t ≠ y t := fun h2 => hxy (hiff.1 ⟨h1, h2⟩)
      simp [h2]
    · rw [ite_eq_right h1]

/-- The controlled operator: `u` at the site `t` when the sites of `S` are in the configuration
`c`, the identity otherwise.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
decomposed into local gates). -/
noncomputable def ctrlOp (S : Finset (Fin n)) (c : Cfg d n) (t : Fin n)
    (u : Matrix (Fin d) (Fin d) ℂ) : Matrix (Cfg d n) (Cfg d n) ℂ :=
  ctrlElem (ctrlProj S c) (siteOp t u)

theorem commute_ctrlProj_siteOp {S : Finset (Fin n)} {t : Fin n} (ht : t ∉ S) (c : Cfg d n)
    (u : Matrix (Fin d) (Fin d) ℂ) : Commute (ctrlProj S c) (siteOp t u) :=
  commute_of_mem_supportedOperators (Set.disjoint_singleton_right.mpr (by simpa using ht))
    (ctrlProj_mem_supportedOperators S c) (siteOp_mem_supportedOperators t u)

@[simp] theorem ctrlOp_empty (c : Cfg d n) (t : Fin n) (u : Matrix (Fin d) (Fin d) ℂ) :
    ctrlOp ∅ c t u = siteOp t u := by
  simp [ctrlOp, ctrlElem]

theorem ctrlOp_mul {S : Finset (Fin n)} {t : Fin n} (ht : t ∉ S) (c : Cfg d n)
    (u v : Matrix (Fin d) (Fin d) ℂ) : ctrlOp S c t u * ctrlOp S c t v = ctrlOp S c t (u * v) := by
  rw [ctrlOp, ctrlOp, ctrlElem_mul (isIdempotentElem_ctrlProj S c)
    (commute_ctrlProj_siteOp ht c u), siteOp_mul, ctrlOp]

theorem ctrlOp_one (S : Finset (Fin n)) (c : Cfg d n) (t : Fin n) : ctrlOp S c t 1 = 1 := by
  rw [ctrlOp, siteOp_one, ctrlElem_one]

theorem ctrlOp_star {S : Finset (Fin n)} {t : Fin n} (ht : t ∉ S) (c : Cfg d n)
    (u : Matrix (Fin d) (Fin d) ℂ) : star (ctrlOp S c t u) = ctrlOp S c t (star u) := by
  have hc := commute_ctrlProj_siteOp ht c u
  have hp : star (ctrlProj S c) = ctrlProj S c := ctrlProj_conjTranspose S c
  rw [ctrlOp, ctrlOp, ctrlElem, ctrlElem, star_add, star_mul, star_sub, star_one, hp,
    siteOp_star, (commute_ctrlProj_siteOp ht c (star u)).eq]

theorem ctrlOp_mem_unitary {S : Finset (Fin n)} {t : Fin n} (ht : t ∉ S) (c : Cfg d n)
    {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ctrlOp S c t u ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
  rw [Unitary.mem_iff] at hu ⊢
  rw [ctrlOp_star ht, ctrlOp_mul ht, ctrlOp_mul ht, hu.1, hu.2, ctrlOp_one]
  exact ⟨rfl, rfl⟩

theorem ctrlOp_mem_supportedOperators (S : Finset (Fin n)) (c : Cfg d n) (t : Fin n)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    ctrlOp S c t u ∈ supportedOperators d (insert t (S : Set (Fin n))) := by
  have hp := supportedOperators_mono (Set.subset_insert t (S : Set (Fin n)))
    (ctrlProj_mem_supportedOperators (d := d) S c)
  have hs := supportedOperators_mono (Set.singleton_subset_iff.mpr
    (Set.mem_insert t (S : Set (Fin n))))
    (siteOp_mem_supportedOperators (d := d) t u)
  exact Submodule.add_mem _ (mul_mem_supportedOperators hp hs)
    (Submodule.sub_mem _ (one_mem_supportedOperators _) hp)

/-- **Controlled commutator on the chain.** Removing one control site `s` from the controls of
a commutator `v w v† w†` at the site `t`. -/
theorem ctrlOp_insert_commutator {S : Finset (Fin n)} {s t : Fin n} (ht : t ∉ S)
    (hst : s ≠ t) (c : Cfg d n) {v w : Matrix (Fin d) (Fin d) ℂ}
    (hv : v ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hw : w ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ctrlOp (insert s S) c t (v * w * star v * star w) =
      ctrlOp S c t v * ctrlOp {s} c t w * ctrlOp S c t (star v) * ctrlOp {s} c t (star w) := by
  have hts : t ∉ ({s} : Finset (Fin n)) := by simpa using Ne.symm hst
  rw [ctrlOp, ctrlProj_insert, ← siteOp_mul, ← siteOp_mul, ← siteOp_mul, ctrlOp, ctrlOp, ctrlOp,
    ctrlOp]
  refine (ctrlElem_commutator (isIdempotentElem_ctrlProj S c) (isIdempotentElem_ctrlProj {s} c)
    (commute_ctrlProj S {s} c c) (commute_ctrlProj_siteOp ht c v)
    (commute_ctrlProj_siteOp ht c w)
    (commute_ctrlProj_siteOp hts c v) (commute_ctrlProj_siteOp hts c _)
    (commute_ctrlProj_siteOp hts c w) ?_ ?_).symm
  · rw [siteOp_mul, Unitary.mul_star_self_of_mem hv, siteOp_one]
  · rw [siteOp_mul, Unitary.mul_star_self_of_mem hw, siteOp_one]

/-- A controlled diagonal operator is diagonal. -/
theorem ctrlOp_diagonal (S : Finset (Fin n)) (c : Cfg d n) (t : Fin n) (f : Fin d → ℂ) :
    ctrlOp S c t (diagonal f) =
      diagonal fun x : Cfg d n => if ∀ i ∈ S, x i = c i then f (x t) else 1 := by
  rw [ctrlOp, ctrlElem, siteOp_diagonal, ctrlProj, diagonal_mul_diagonal, ← diagonal_one,
    diagonal_sub, diagonal_add]
  congr 1; funext x; split_ifs <;> simp

end MPSPreparation
