/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Block
import TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRep

/-!
# Duality and direct summands of nonnegative integer representations

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex` lines 564–565. The multiplicities `M_{a,x}^y` of a module
category form a nonnegative integer representation (`MPOTensor.IsNIMRep`) on which the dual
label acts by the transpose, `M_{a*} = M_aᵀ`.

This file states the duality condition and direct summands of a representation, used by the
classifications of the dual representations of `Rep(S₃)` in
`TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRepClassification.RepS3Classification` and of
`su(2)₄` in `TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRepClassification.SU24Classification`.
It also collects the elementary counting facts about sums of squares of natural numbers that
both classifications use.

## Main definitions

* `MPOTensor.IsTransposeDual`: the duality `M_{a*} = M_aᵀ`.
* `MPOTensor.IsNIMRepSummand`: the blocks `f u` carry a direct summand isomorphic to `M'`.

## Main results

* `MPOTensor.IsNIMRepSummand.exists_equiv`: a summand that exhausts the blocks identifies the
  action with the summand.
* `MPOTensor.IsNIMRepSummand.surjective_of_isIndecomposable`: a nonempty summand of an
  indecomposable action exhausts the blocks.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

namespace MPOTensor

variable {ι κ κ' : Type*}

/-! ### Duality and direct summands -/

/-- **Duality of an action on blocks** (arXiv:2203.12563, lines 564–565, for the action of a
module category): the dual label acts by the transpose, `M_{a*} = M_aᵀ`. For a ring whose
labels are all self-dual, `dual = id` and the condition says that every `M_a` is symmetric. -/
def IsTransposeDual (M : ι → κ → κ → ℕ) (dual : ι → ι) : Prop :=
  ∀ a x y, M (dual a) x y = M a y x

/-- **A direct summand of an action on blocks**: the blocks `f u` are distinct, no label sends
one of them to a block outside the family, and on the family the multiplicities are those of
`M'`. For a dual action the transpose condition also rules out the converse transitions, so the
family carries a direct summand isomorphic to `M'`. -/
def IsNIMRepSummand (M : ι → κ → κ → ℕ) (M' : ι → κ' → κ' → ℕ) (f : κ' → κ) : Prop :=
  Function.Injective f ∧ (∀ a u z, z ∉ Set.range f → M a (f u) z = 0) ∧
    ∀ a u v, M a (f u) (f v) = M' a u v

namespace IsNIMRepSummand

variable {M : ι → κ → κ → ℕ} {M' : ι → κ' → κ' → ℕ} {f : κ' → κ}

/-- A block reached from a block of a summand lies in the summand. -/
theorem mem_range (hf : IsNIMRepSummand M M' f) {a : ι} {u : κ'} {z : κ}
    (hz : M a (f u) z ≠ 0) : z ∈ Set.range f := by
  by_contra h
  exact hz (hf.2.1 a u z h)

/-- A summand that exhausts the blocks identifies the action with `M'`. -/
theorem exists_equiv (hf : IsNIMRepSummand M M' f) (hsurj : Function.Surjective f) :
    ∃ e : κ ≃ κ', ∀ a x y, M a x y = M' a (e x) (e y) := by
  let e := Equiv.ofBijective f ⟨hf.1, hsurj⟩
  refine ⟨e.symm, fun a x y => ?_⟩
  have hx : f (e.symm x) = x := e.apply_symm_apply x
  have hy : f (e.symm y) = y := e.apply_symm_apply y
  rw [← hf.2.2 a, hx, hy]

/-- A nonempty summand of an action whose label `a` acts indecomposably exhausts the blocks. -/
theorem surjective_of_isIndecomposable [Finite κ] [Nonempty κ'] (hf : IsNIMRepSummand M M' f)
    {a : ι} (hind : Matrix.IsIndecomposable (M a)) : Function.Surjective f := by
  classical
  obtain ⟨u₀⟩ := ‹Nonempty κ'›
  let b : κ → ℕ := fun z => if z ∈ Set.range f then 1 else 0
  have hb : Matrix.BlockTriangular (M a) b := by
    intro i j hij
    dsimp only [b] at hij
    split_ifs at hij with h1 h2 h2 <;> try omega
    obtain ⟨u, rfl⟩ := h2
    exact hf.2.1 a u j h1
  obtain ⟨c, hc⟩ := (Matrix.isIndecomposable_iff_blockTriangular_const (α := ℕ) (M a)).mp
    hind b hb
  intro z
  have h1 : (if f u₀ ∈ Set.range f then 1 else 0) = c := congrFun hc (f u₀)
  have h2 : (if z ∈ Set.range f then 1 else 0) = c := congrFun hc z
  simp only [Set.mem_range_self, ↓reduceIte] at h1
  by_contra hz
  have hz' : z ∉ Set.range f := hz
  simp only [hz', ↓reduceIte] at h2
  omega

end IsNIMRepSummand

/-! ### Sums of squares of natural numbers -/

section Squares

variable [Fintype κ]

/-- A natural sum over all blocks bounded by its restriction to `S` vanishes outside `S`. -/
private theorem eq_zero_of_sum_le_sum {f : κ → ℕ} {S : Finset κ}
    (h : ∑ z, f z ≤ ∑ z ∈ S, f z) {u : κ} (hu : u ∉ S) : f u = 0 := by
  classical
  have h1 : ∑ z ∈ insert u S, f z ≤ ∑ z, f z :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_insert hu] at h1
  omega

/-- If the squares of a natural family sum to one, the family is a single one. -/
theorem exists_eq_one_of_sum_mul_self_eq_one {f : κ → ℕ}
    (h : ∑ z, f z * f z = 1) : ∃ w, f w = 1 ∧ ∀ u, u ≠ w → f u = 0 := by
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => f z * f z) (by omega)
  have hle := Finset.single_le_sum (fun z _ => Nat.zero_le (f z * f z)) (Finset.mem_univ w)
  have hw0 : f w ≠ 0 := fun h0 => hw (by simp [h0])
  have hw1 : f w = 1 := by
    rw [h] at hle
    rcases Nat.lt_or_ge (f w) 2 with h2 | h2
    · omega
    · nlinarith
  refine ⟨w, hw1, fun u hu => ?_⟩
  have h2 := Finset.add_le_sum (fun z _ => Nat.zero_le (f z * f z)) (Finset.mem_univ w)
    (Finset.mem_univ u) hu.symm
  rw [hw1, h] at h2
  exact mul_self_eq_zero.mp (by omega)

/-- Two distinct summands of a natural sum over all blocks are bounded by the sum. -/
theorem sum_pair_le {f : κ → ℕ} {a b : κ} (hab : a ≠ b) :
    f a + f b ≤ ∑ z, f z :=
  Finset.add_le_sum (fun z _ => Nat.zero_le (f z)) (Finset.mem_univ a) (Finset.mem_univ b) hab

/-- Three distinct summands of a natural sum over all blocks are bounded by the sum. -/
theorem sum_three_le {f : κ → ℕ} {a b c : κ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : f a + f b + f c ≤ ∑ z, f z := by
  classical
  have h := Finset.sum_le_sum_of_subset (f := f) (Finset.subset_univ {a, b, c})
  rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc] at h

/-- A natural sum over all blocks bounded by two of its summands vanishes elsewhere. -/
theorem eq_zero_of_sum_le_pair {f : κ → ℕ} {a b : κ} (hab : a ≠ b)
    (h : ∑ z, f z ≤ f a + f b) {u : κ} (hua : u ≠ a) (hub : u ≠ b) : f u = 0 := by
  classical
  exact eq_zero_of_sum_le_sum (S := {a, b}) (by rwa [Finset.sum_pair hab]) (by simp [hua, hub])

/-- A natural sum over all blocks bounded by three of its summands vanishes elsewhere. -/
theorem eq_zero_of_sum_le_three {f : κ → ℕ} {a b c : κ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h : ∑ z, f z ≤ f a + f b + f c) {u : κ} (hua : u ≠ a) (hub : u ≠ b)
    (huc : u ≠ c) : f u = 0 := by
  classical
  exact eq_zero_of_sum_le_sum (S := {a, b, c})
    (by rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc])
    (by simp [hua, hub, huc])

end Squares

/-- Two distinct blocks form an injective family. -/
theorem injective_vecCons_two {a b : κ} (hab : a ≠ b) : Function.Injective ![a, b] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Four pairwise distinct blocks form an injective family. -/
theorem injective_vecCons_four {a b c d : κ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Five pairwise distinct blocks form an injective family. -/
theorem injective_vecCons_five {a b c d e : κ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : Function.Injective ![a, b, c, d, e] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- A row with entries one on `P` and zero elsewhere. -/
theorem eq_ite_of_forall {g : κ → ℕ} {P : κ → Prop} [DecidablePred P]
    (h1 : ∀ z, P z → g z = 1) (h0 : ∀ z, ¬ P z → g z = 0) (z : κ) :
    g z = if P z then 1 else 0 := by
  by_cases h : P z
  · simp only [h, ↓reduceIte, h1 z h]
  · simp only [h, ↓reduceIte, h0 z h]

/-- A natural number whose square is two or three does not exist. -/
theorem mul_self_ne_two_three {q : ℕ} : q * q ≠ 2 ∧ q * q ≠ 3 := by
  rcases Nat.lt_or_ge q 2 with h | h
  · interval_cases q <;> simp
  · constructor <;> nlinarith

/-- Three pairwise distinct blocks form an injective family. -/
theorem injective_vecCons_three {a b c : κ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end MPOTensor
