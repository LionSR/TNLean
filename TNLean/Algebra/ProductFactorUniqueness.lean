/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.Ring

/-!
# Uniqueness of factors in finite product functions

Equal nonzero product functions have proportional factors, with proportionality
constants whose product is one. For invertible matrix factors the required
nonzero entries are chosen internally. Translation invariance then makes the
matrix factors proportional within each direction.

These calculations are used in the injective PEPS translation-invariance
corollary of arXiv:1804.04964, Applications, lines 1891–1894.
-/

noncomputable section

open scoped BigOperators Matrix

private theorem prod_dependent_update
    {I K : Type*} [Fintype I] [DecidableEq I] [CommMonoid K] {X : I → Type*}
    (f : (i : I) → X i → K) (a₀ : (i : I) → X i) (i : I) (x : X i) :
    (∏ j, f j (Function.update a₀ i x j)) =
      f i x * ∏ j ∈ Finset.univ.erase i, f j (a₀ j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Equality of finite product functions and one nonzero reference product
force nonzero proportionality constants with product one. Supporting algebra
for arXiv:1804.04964, Applications, lines 1801 and 1891–1894. -/
theorem Fintype.exists_scalars_of_prod_eq
    {I K : Type*} [Fintype I] [Field K] {X : I → Type*}
    (f g : (i : I) → X i → K)
    (a₀ : (i : I) → X i)
    (hf₀ : (∏ i, f i (a₀ i)) ≠ 0)
    (hprod : ∀ a : (i : I) → X i, ∏ i, f i (a i) = ∏ i, g i (a i)) :
    ∃ c : I → K, (∀ i, c i ≠ 0) ∧ (∏ i, c i = 1) ∧
      ∀ (i : I) (x : X i), g i x = c i * f i x := by
  classical
  have hf : ∀ i, f i (a₀ i) ≠ 0 :=
    fun i ↦ (Finset.prod_ne_zero_iff.mp hf₀) i (Finset.mem_univ i)
  have hg₀ : (∏ i, g i (a₀ i)) ≠ 0 := by
    rw [← hprod a₀]
    exact hf₀
  have hg : ∀ i, g i (a₀ i) ≠ 0 :=
    fun i ↦ (Finset.prod_ne_zero_iff.mp hg₀) i (Finset.mem_univ i)
  let c : I → K := fun i ↦ g i (a₀ i) / f i (a₀ i)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i
    exact div_ne_zero (hg i) (hf i)
  · calc
      ∏ i, c i = (∏ i, g i (a₀ i)) / (∏ i, f i (a₀ i)) := by
        simp only [c, Finset.prod_div_distrib]
      _ = 1 := by rw [← hprod a₀, div_self hf₀]
  · intro i x
    let fRest : K := ∏ j ∈ Finset.univ.erase i, f j (a₀ j)
    let gRest : K := ∏ j ∈ Finset.univ.erase i, g j (a₀ j)
    have hgRest : gRest ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hg j)
    have hbase : f i (a₀ i) * fRest = g i (a₀ i) * gRest := by
      calc
        f i (a₀ i) * fRest = ∏ j, f j (a₀ j) := by
          simpa only [fRest] using
            Finset.mul_prod_erase Finset.univ (fun j ↦ f j (a₀ j)) (Finset.mem_univ i)
        _ = ∏ j, g j (a₀ j) := hprod a₀
        _ = g i (a₀ i) * gRest := by
          simpa only [gRest] using
            (Finset.mul_prod_erase Finset.univ (fun j ↦ g j (a₀ j)) (Finset.mem_univ i)).symm
    have hvar : f i x * fRest = g i x * gRest := by
      simpa only [prod_dependent_update, fRest, gRest] using
        hprod (Function.update a₀ i x)
    have hcross : g i x * f i (a₀ i) = g i (a₀ i) * f i x := by
      apply mul_right_cancel₀ hgRest
      calc
        (g i x * f i (a₀ i)) * gRest = f i (a₀ i) * (g i x * gRest) := by ring
        _ = f i (a₀ i) * (f i x * fRest) := by rw [← hvar]
        _ = f i x * (f i (a₀ i) * fRest) := by ring
        _ = f i x * (g i (a₀ i) * gRest) := by rw [hbase]
        _ = (g i (a₀ i) * f i x) * gRest := by ring
    change g i x = (g i (a₀ i) / f i (a₀ i)) * f i x
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff (hf i)).mpr hcross

/-- Equality of products of matrix entries determines each invertible factor
up to a nonzero scalar. The reference entries are derived internally.
Supporting algebra for arXiv:1804.04964, lines 1891–1894. -/
private theorem Matrix.GeneralLinearGroup.exists_scalars_of_prod_entries_eq
    {I : Type*} [Fintype I] {n : I → ℕ} (hn : ∀ i, 0 < n i)
    (F : (i : I) → GL (Fin (n i)) ℂ)
    (G : (i : I) → Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (hprod : ∀ a : (i : I) → Fin (n i) × Fin (n i),
      ∏ i, (F i : Matrix (Fin (n i)) (Fin (n i)) ℂ) (a i).1 (a i).2 =
        ∏ i, G i (a i).1 (a i).2) :
    ∃ c : I → ℂ, (∀ i, c i ≠ 0) ∧ (∏ i, c i = 1) ∧
      ∀ (i : I) (a b : Fin (n i)),
        G i a b = c i * (F i : Matrix (Fin (n i)) (Fin (n i)) ℂ) a b := by
  classical
  have hentry (i : I) : ∃ p : Fin (n i) × Fin (n i),
      (F i : Matrix (Fin (n i)) (Fin (n i)) ℂ) p.1 p.2 ≠ 0 := by
    let : NeZero (n i) := ⟨Nat.ne_of_gt (hn i)⟩
    have hF : (F i : Matrix (Fin (n i)) (Fin (n i)) ℂ) ≠ 0 := Units.ne_zero (F i)
    by_contra h
    apply hF
    ext a b
    by_contra hab
    exact h ⟨(a, b), hab⟩
  choose a ha using hentry
  obtain ⟨c, hc, hcprod, hpoint⟩ := Fintype.exists_scalars_of_prod_eq
    (fun i p => (F i : Matrix (Fin (n i)) (Fin (n i)) ℂ) p.1 p.2)
    (fun i p => G i p.1 p.2) a
    (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)) hprod
  exact ⟨c, hc, hcprod, fun i x y => hpoint i (x, y)⟩

/-- Translation invariance of a full product of invertible matrix factors
makes the factors proportional within each direction. The reference factors
are the actual matrices at position zero, and may have different sizes in
different directions. Supporting algebra for arXiv:1804.04964,
lines 1891–1894. -/
theorem Matrix.GeneralLinearGroup.exists_directional_scalars_of_prod_translate_eq
    {Direction Position : Type*} [Fintype Direction] [Fintype Position]
    [AddMonoid Position] {n : Direction → ℕ} (hn : ∀ r, 0 < n r)
    (E : (r : Direction) → Position → GL (Fin (n r)) ℂ)
    (hprod : ∀ (t : Position)
      (a : (z : Direction × Position) → Fin (n z.1) × Fin (n z.1)),
      ∏ z, (E z.1 z.2 : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ)
          (a z).1 (a z).2 =
        ∏ z, (E z.1 (z.2 + t) : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ)
          (a z).1 (a z).2) :
    ∃ α : Direction → Position → ℂ,
      (∀ r p, α r p ≠ 0) ∧
        ∀ (r : Direction) (p : Position) (a b : Fin (n r)),
          (E r p : Matrix (Fin (n r)) (Fin (n r)) ℂ) a b =
            α r p * (E r 0 : Matrix (Fin (n r)) (Fin (n r)) ℂ) a b := by
  classical
  have hscalars (t : Position) : ∃ c : Direction × Position → ℂ,
      (∀ z, c z ≠ 0) ∧ (∏ z, c z = 1) ∧
        ∀ (z : Direction × Position) (a b : Fin (n z.1)),
          (E z.1 (z.2 + t) : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ) a b =
            c z * (E z.1 z.2 : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ) a b :=
    Matrix.GeneralLinearGroup.exists_scalars_of_prod_entries_eq
      (fun z : Direction × Position => hn z.1)
      (fun z : Direction × Position => E z.1 z.2)
      (fun z : Direction × Position =>
        (E z.1 (z.2 + t) : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ)) (hprod t)
  choose c hc _hcprod heq using hscalars
  refine ⟨fun r p => c p (r, 0), fun r p => hc p (r, 0), ?_⟩
  intro r p a b
  simpa only [zero_add] using heq p (r, 0) a b
