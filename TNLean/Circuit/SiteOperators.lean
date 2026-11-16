/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding

/-!
# Single-site operators and projections onto configurations

Two families of operators on a finite set of sites `ι` with local dimension `d`:

* `QuantumCircuit.ctrlProj S c`, the projection onto the configurations that agree with `c` on
  the finite set `S`; it acts on `S`;
* `QuantumCircuit.siteOp t u`, the operator `u` at the site `t`; it acts on `{t}`.

Projections of the first kind commute with one another, and with a single-site operator at a
site outside `S`. The controlled operators built from the two are in
`TNLean.Circuit.Gates.Controlled`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), main text before Theorem 1 and paragraph
  "The sequential-RG circuit".
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Projections onto configurations -/

/-- The projection onto the configurations `x` with `x i = c i` for every `i ∈ S`.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
decomposed into local gates). -/
def ctrlProj (S : Finset ι) (c : ι → Fin d) : Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  diagonal fun x => if ∀ i ∈ S, x i = c i then 1 else 0

theorem isIdempotentElem_ctrlProj (S : Finset ι) (c : ι → Fin d) :
    IsIdempotentElem (ctrlProj S c) := by
  unfold IsIdempotentElem ctrlProj
  rw [diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

theorem commute_ctrlProj (S S' : Finset ι) (c c' : ι → Fin d) :
    Commute (ctrlProj S c) (ctrlProj S' c') := by
  unfold Commute SemiconjBy ctrlProj
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext x; ring

theorem ctrlProj_insert {s : ι} (S : Finset ι) (c : ι → Fin d) :
    ctrlProj (insert s S) c = ctrlProj S c * ctrlProj {s} c := by
  unfold ctrlProj
  rw [diagonal_mul_diagonal]
  congr 1; funext x
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  by_cases h1 : x s = c s <;> by_cases h2 : ∀ i ∈ S, x i = c i <;> simp [h1, h2]

@[simp] theorem ctrlProj_empty (c : ι → Fin d) : ctrlProj ∅ c = 1 := by
  simp [ctrlProj]

theorem ctrlProj_conjTranspose (S : Finset ι) (c : ι → Fin d) :
    (ctrlProj S c)ᴴ = ctrlProj S c := by
  unfold ctrlProj
  rw [diagonal_conjTranspose]
  congr 1; funext x; simp only [Pi.star_apply]; split_ifs <;> simp

theorem ctrlProj_mem_supportedOperators (S : Finset ι) (c : ι → Fin d) :
    ctrlProj S c ∈ supportedOperators d (S : Set ι) := by
  classical
  have : ctrlProj S c = rectKronecker fun i =>
      if i ∈ S then diagonal (fun a : Fin d => if a = c i then (1 : ℂ) else 0) else 1 := by
    ext x y
    simp only [ctrlProj, rectKronecker_apply, diagonal_apply]
    have hfac : ∀ i, (if i ∈ S then diagonal (fun a : Fin d => if a = c i then (1 : ℂ) else 0)
        else 1) (x i) (y i) = (if x i = y i then 1 else 0) *
          (if i ∈ S then (if x i = c i then 1 else 0) else 1) := fun i => by
      split_ifs <;> simp_all [one_apply]
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
  exact rectKronecker_mem_supportedOperators fun i hi => by
    rw [ite_eq_right (by simpa using hi)]

/-! ### Single-site operators -/

/-- The operator `u` at the site `t`.

Source: arXiv:2307.01696, main text before Theorem 1 (local gates). -/
noncomputable def siteOp (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  embedOp ![t] (u.submatrix (Equiv.funUnique (Fin 1) (Fin d)) (Equiv.funUnique (Fin 1) (Fin d)))

omit [Fintype ι] [DecidableEq ι] in
theorem siteSites_injective (t : ι) : Function.Injective ![t] := by
  intro a b _; exact Subsingleton.elim a b

theorem siteOp_mul (t : ι) (u v : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t u * siteOp t v = siteOp t (u * v) := by
  rw [siteOp, siteOp, embedOp_mul (siteSites_injective t), submatrix_mul_equiv, siteOp]

@[simp] theorem siteOp_one (t : ι) : siteOp (d := d) t 1 = 1 := by
  rw [siteOp, submatrix_one_equiv, embedOp_one]

theorem siteOp_conjTranspose (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) :
    (siteOp t u)ᴴ = siteOp t uᴴ := by
  rw [siteOp, embedOp_conjTranspose, conjTranspose_submatrix, siteOp]

theorem siteOp_star (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) :
    star (siteOp t u) = siteOp t (star u) :=
  siteOp_conjTranspose t u

theorem siteOp_mem_unitary (t : ι) {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : u ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    siteOp t u ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ) := by
  rw [Unitary.mem_iff] at hu ⊢
  rw [siteOp_star, siteOp_mul, siteOp_mul, hu.1, hu.2, siteOp_one]
  exact ⟨rfl, rfl⟩

theorem siteOp_mem_supportedOperators (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t u ∈ supportedOperators d {t} := by
  have := embedOp_mem_supportedOperators (siteSites_injective t)
    (u.submatrix (Equiv.funUnique (Fin 1) (Fin d)) (Equiv.funUnique (Fin 1) (Fin d)))
  rwa [Matrix.range_cons, Matrix.range_empty, Set.union_empty] at this

theorem siteOp_diagonal (t : ι) (f : Fin d → ℂ) :
    siteOp t (diagonal f) = diagonal fun x : (ι → Fin d) => f (x t) := by
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

/-- Entrywise, `u` at the site `t` has the entry `u (x t) (y t)` between configurations that
agree off `t`, and `0` between the others. -/
theorem siteOp_apply (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) (x y : ι → Fin d) :
    siteOp t u x y = if ∀ i, i ≠ t → x i = y i then u (x t) (y t) else 0 := by
  have hag : AgreeOff ![t] x y ↔ ∀ i, i ≠ t → x i = y i :=
    forall_congr' fun i => by simp [eq_comm]
  simp only [siteOp, embedOp_apply, submatrix_apply, Function.comp_apply,
    Equiv.funUnique_apply, Fin.default_eq_zero, Matrix.cons_val_zero, hag]

theorem siteOp_add (t : ι) (u v : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t (u + v) = siteOp t u + siteOp t v := by
  ext x y
  simp only [siteOp_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem siteOp_neg (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t (-u) = -siteOp t u := by
  ext x y
  simp only [siteOp_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem siteOp_sub (t : ι) (u v : Matrix (Fin d) (Fin d) ℂ) :
    siteOp t (u - v) = siteOp t u - siteOp t v := by
  rw [sub_eq_add_neg, siteOp_add, siteOp_neg, ← sub_eq_add_neg]

theorem commute_ctrlProj_siteOp {S : Finset ι} {t : ι} (ht : t ∉ S) (c : ι → Fin d)
    (u : Matrix (Fin d) (Fin d) ℂ) : Commute (ctrlProj S c) (siteOp t u) :=
  commute_of_mem_supportedOperators (Set.disjoint_singleton_right.mpr (by simpa using ht))
    (ctrlProj_mem_supportedOperators S c) (siteOp_mem_supportedOperators t u)

end QuantumCircuit
