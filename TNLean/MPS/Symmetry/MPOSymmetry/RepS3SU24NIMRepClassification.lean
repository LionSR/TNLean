/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Block
import TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRep

/-!
# Classification of the dual nonnegative integer representations of `Rep(S₃)` and `su(2)₄`

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1890–1931 and 1933–1989: "there are only two
different phases" of matrix product states symmetric under the `su(2)₄` matrix product operator
algebra, the regular one with five blocks and `𝓜_TY` with four, and every phase for `Rep(S₃)` is
labelled by a subgroup `ℤ₁`, `ℤ₂`, `ℤ₃` or `S₃`, with the four printed actions on the blocks.

The source takes completeness of these lists from the classification of module categories,
which it cites. The multiplicities `M_{a,x}^y` of a module category form a nonnegative integer
representation (`MPOTensor.IsNIMRep`, lines 564–565) on which the unit acts trivially and the
dual label acts by the transpose, `M_{a*} = M_aᵀ`. Every label of `Rep(S₃)` and of `su(2)₄` is
self-dual, so the duality reads `M_a = M_aᵀ`.

**Formalized here.** The duality condition (`MPOTensor.IsTransposeDual`), direct summands of a
representation (`MPOTensor.IsNIMRepSummand`), and the classification of the dual
representations of `Rep(S₃)` and of `su(2)₄` on any finite set of blocks: every block lies in a
direct summand isomorphic to one of the printed actions, and an indecomposable representation is
one of them. The two-block representation `M_ψ = 1`, `M_π = [[0, 1], [2, 1]]` of `Rep(S₃)`
satisfies the representation identity but not the duality, so the duality hypothesis cannot be
dropped.

The proof is local. Since `M_ψ² = 1` and `M_ψ` is a symmetric natural matrix, it is the
permutation matrix of an involution `σ`. Writing `T = M_π`, the relations `T = M_ψ T` and
`T² = 1 + T + M_ψ` give, on the diagonal, `∑_z T_{xz}² = 1 + T_{xx} + [σx = x]`. A block moved
by `σ` lies in a `ℤ₂` summand (`T_{xx} = 1`) or is a corner of an `S₃` summand
(`T_{xx} = 0`); a block fixed by `σ` lies in a `ℤ₁` summand (`T_{xx} = 2`), is the middle
block of an `S₃` summand, or lies in a `ℤ₃` summand. The integer labels `0, 1, 2` of `su(2)₄`
represent `Rep(S₃)`, and the relations `1/2 × 1/2 = 0 + 1` and `1/2 × 2 = 3/2` then determine
the action of `1/2` around each of these configurations: a `ℤ₁` or `ℤ₃` configuration closes
into `𝓜_TY`, and an `S₃` or `ℤ₂` configuration into the regular phase.

**Scope restriction (printed list):** the input is the nonnegative integer representation of a
module category, not the module category itself; the lists are identified at the level of the
multiplicities. Documented in `docs/paper-gaps/glm23_reps3_su24_module_list.tex`.

## Main definitions

* `MPOTensor.IsTransposeDual`: the duality `M_{a*} = M_aᵀ`.
* `MPOTensor.IsNIMRepSummand`: the blocks `f u` carry a direct summand isomorphic to `M'`.
* `MPOTensor.repS3NonDual`: a two-block representation that is not dual.

## Main results

* `MPOTensor.exists_isNIMRepSummand_repS3`: every block of a dual representation of `Rep(S₃)`
  with trivial unit lies in a summand isomorphic to the `ℤ₁`, `ℤ₂`, `ℤ₃` or `S₃` phase.
* `MPOTensor.exists_equiv_of_isIndecomposable_repS3`: the indecomposable ones are exactly these
  four.
* `MPOTensor.exists_isNIMRepSummand_su24`: every block of a dual representation of `su(2)₄` with
  trivial unit lies in a summand isomorphic to the regular phase or to `𝓜_TY`.
* `MPOTensor.exists_equiv_of_isIndecomposable_su24`: the indecomposable ones are exactly these
  two.
* `MPOTensor.isNIMRep_repS3NonDual`, `MPOTensor.not_isTransposeDual_repS3NonDual`.

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
private theorem exists_eq_one_of_sum_mul_self_eq_one {f : κ → ℕ}
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

private theorem sum_pair_le {f : κ → ℕ} {a b : κ} (hab : a ≠ b) :
    f a + f b ≤ ∑ z, f z :=
  Finset.add_le_sum (fun z _ => Nat.zero_le (f z)) (Finset.mem_univ a) (Finset.mem_univ b) hab

private theorem sum_three_le {f : κ → ℕ} {a b c : κ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : f a + f b + f c ≤ ∑ z, f z := by
  classical
  have h := Finset.sum_le_sum_of_subset (f := f) (Finset.subset_univ {a, b, c})
  rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc] at h

private theorem eq_zero_of_sum_le_pair {f : κ → ℕ} {a b : κ} (hab : a ≠ b)
    (h : ∑ z, f z ≤ f a + f b) {u : κ} (hua : u ≠ a) (hub : u ≠ b) : f u = 0 := by
  classical
  exact eq_zero_of_sum_le_sum (S := {a, b}) (by rwa [Finset.sum_pair hab]) (by simp [hua, hub])

private theorem eq_zero_of_sum_le_three {f : κ → ℕ} {a b c : κ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h : ∑ z, f z ≤ f a + f b + f c) {u : κ} (hua : u ≠ a) (hub : u ≠ b)
    (huc : u ≠ c) : f u = 0 := by
  classical
  exact eq_zero_of_sum_le_sum (S := {a, b, c})
    (by rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc])
    (by simp [hua, hub, huc])

end Squares

private theorem injective_vecCons_two {a b : κ} (hab : a ≠ b) : Function.Injective ![a, b] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem injective_vecCons_four {a b c d : κ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem injective_vecCons_five {a b c d e : κ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : Function.Injective ![a, b, c, d, e] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- A row with entries one on `P` and zero elsewhere. -/
private theorem eq_ite_of_forall {g : κ → ℕ} {P : κ → Prop} [DecidablePred P]
    (h1 : ∀ z, P z → g z = 1) (h0 : ∀ z, ¬ P z → g z = 0) (z : κ) :
    g z = if P z then 1 else 0 := by
  by_cases h : P z
  · simp only [h, ↓reduceIte, h1 z h]
  · simp only [h, ↓reduceIte, h0 z h]

/-- A natural number whose square is two or three does not exist. -/
private theorem mul_self_ne_two_three {q : ℕ} : q * q ≠ 2 ∧ q * q ≠ 3 := by
  rcases Nat.lt_or_ge q 2 with h | h
  · interval_cases q <;> simp
  · constructor <;> nlinarith

private theorem injective_vecCons_three {a b c : κ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-! ### The local structure of a dual representation of `Rep(S₃)` -/

section RepS3Local

variable [Fintype κ] [DecidableEq κ] {T : κ → κ → ℕ} {σ : κ → κ}

/-- **A block moved by `ψ`.** For a symmetric `T` with `T (σ x) = T x` and the diagonal
relation `∑_z T_{xz}² = 1 + T_{xx} + [σx = x]`, a block `x` with `σx ≠ x` either lies with `σx`
in a `ℤ₂` summand, or has a unique neighbour `w`, fixed by `σ`, with `T_{ww} = 1` and no
neighbours besides `x`, `σx`, `w` (the `S₃` summand). -/
private theorem repS3_of_ne
    (hT : ∀ x y, T x y = T y x) (hTσ : ∀ x y, T (σ x) y = T x y)
    (hrow : ∀ x, ∑ z, T x z * T x z = 1 + T x x + if σ x = x then 1 else 0)
    (hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, T x z * T z y = T x y)
    {x : κ} (hx : σ x ≠ x) :
    (T x x = 1 ∧ ∀ z, z ≠ x → z ≠ σ x → T x z = 0) ∨
    (T x x = 0 ∧ ∃ w, w ≠ x ∧ w ≠ σ x ∧ σ w = w ∧ T x w = 1 ∧ T w w = 1 ∧
      (∀ z, z ≠ w → T x z = 0) ∧ ∀ z, z ≠ x → z ≠ σ x → z ≠ w → T w z = 0) := by
  have hxy : x ≠ σ x := fun h => hx h.symm
  have hTxy : T x (σ x) = T x x := by rw [hT, hTσ]
  have hr := hrow x
  simp only [hx, ↓reduceIte, add_zero] at hr
  have h2 := sum_pair_le (f := fun z => T x z * T x z) hxy
  simp only [hTxy, hr] at h2
  have hle : T x x ≤ 1 := by nlinarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · right
    refine ⟨h0, ?_⟩
    rw [h0] at hr
    obtain ⟨w, hw1, hw0⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := T x) (by simpa using hr)
    have hwx : w ≠ x := by
      rintro rfl
      omega
    have hwy : w ≠ σ x := by
      rintro rfl
      omega
    have hTwx : T w x = 1 := by rw [hT]; exact hw1
    have hTwy : T w (σ x) = 1 := by rw [hT, hTσ]; exact hw1
    have hrw := hrow w
    have h3 := sum_three_le (f := fun z => T w z * T w z) hxy (Ne.symm hwx) (Ne.symm hwy)
    simp only [hTwx, hTwy, hrw] at h3
    have hwfix : σ w = w := by
      by_contra hne
      simp only [hne, ↓reduceIte] at h3
      nlinarith
    simp only [hwfix, ↓reduceIte] at hrw h3
    have hww : T w w = 1 := by
      have h := hoff x w (Ne.symm hwx) hwy
      rw [Fintype.sum_eq_single w fun z hz => by rw [hw0 z hz, zero_mul], hw1, one_mul] at h
      exact h
    refine ⟨w, hwx, hwy, hwfix, hw1, hww, hw0, fun z hzx hzy hzw => ?_⟩
    have h := eq_zero_of_sum_le_three (f := fun z => T w z * T w z) hxy (Ne.symm hwx)
      (Ne.symm hwy) (by simp only [hTwx, hTwy, hww, hrw]; omega) hzx hzy hzw
    exact mul_self_eq_zero.mp h
  · left
    refine ⟨h1, fun z hzx hzy => ?_⟩
    have h := eq_zero_of_sum_le_pair (f := fun z => T x z * T x z) hxy
      (by simp only [hTxy, hr, h1]; omega) hzx hzy
    exact mul_self_eq_zero.mp h

/-- **A block fixed by `ψ`.** With the hypotheses of `repS3_of_ne`, a block `x` with `σx = x`
lies in a `ℤ₁` summand (`T_{xx} = 2`), or is a neighbour of a block moved by `σ` with
`T_{xx} = 1` (the middle of an `S₃` summand), or lies with two neighbours `w`, `v`, both fixed by
`σ`, in a `ℤ₃` summand. -/
private theorem repS3_of_eq
    (hT : ∀ x y, T x y = T y x) (hσσ : ∀ x, σ (σ x) = x) (hTσ : ∀ x y, T (σ x) y = T x y)
    (hrow : ∀ x, ∑ z, T x z * T x z = 1 + T x x + if σ x = x then 1 else 0)
    (hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, T x z * T z y = T x y)
    {x : κ} (hx : σ x = x) :
    (T x x = 2 ∧ ∀ z, z ≠ x → T x z = 0) ∨
    (T x x = 1 ∧ ∃ w, σ w ≠ w ∧ T x w ≠ 0) ∨
    (T x x = 0 ∧ ∃ w v, w ≠ x ∧ v ≠ x ∧ w ≠ v ∧ σ w = w ∧ σ v = v ∧ T x w = 1 ∧ T x v = 1 ∧
      T w v = 1 ∧ T w w = 0 ∧ T v v = 0 ∧
      ∀ z, z ≠ x → z ≠ w → z ≠ v → T x z = 0 ∧ T w z = 0 ∧ T v z = 0) := by
  have hr := hrow x
  simp only [hx, ↓reduceIte] at hr
  have hsq := Finset.single_le_sum (fun z _ => Nat.zero_le (T x z * T x z)) (Finset.mem_univ x)
  rw [hr] at hsq
  have hle : T x x ≤ 2 := by nlinarith
  by_cases h2 : T x x = 2
  · left
    refine ⟨h2, fun z hzx => mul_self_eq_zero.mp ?_⟩
    have h := Finset.add_le_sum (fun z _ => Nat.zero_le (T x z * T x z)) (Finset.mem_univ x)
      (Finset.mem_univ z) (Ne.symm hzx)
    rw [hr, h2] at h
    omega
  have hle1 : T x x ≤ 1 := by omega
  have htt : T x x * T x x = T x x := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h | h <;> rw [h]
  -- a neighbour of `x` other than `x`
  have hex : ∃ w, w ≠ x ∧ T x w ≠ 0 := by
    by_contra hne
    push Not at hne
    have h := Fintype.sum_eq_single (f := fun z => T x z * T x z) x
      fun z hz => by rw [hne z hz, zero_mul]
    rw [hr, htt] at h
    omega
  by_cases hmov : ∃ w, w ≠ x ∧ σ w ≠ w ∧ T x w ≠ 0
  · right; left
    obtain ⟨w, hwx, hw, hxw⟩ := hmov
    refine ⟨?_, w, hw, hxw⟩
    have hwx' : T w x ≠ 0 := by rwa [hT]
    rcases repS3_of_ne hT hTσ hrow hoff hw with ⟨-, h0⟩ | ⟨-, u, hux, -, -, -, huu, hw0, -⟩
    · refine absurd (h0 x (Ne.symm hwx) fun h => hwx ?_) hwx'
      rw [← hσσ w, ← h, hx]
    · have hux' : u = x := by
        by_contra hne
        exact hwx' (hw0 x (Ne.symm hne))
      rw [← hux']
      exact huu
  · right; right
    push Not at hmov
    obtain ⟨w, hwx, hxw⟩ := hex
    have hwfix : σ w = w := by
      by_contra h
      exact hxw (hmov w hwx h)
    have h2' := Finset.add_le_sum (fun z _ => Nat.zero_le (T x z * T x z)) (Finset.mem_univ x)
      (Finset.mem_univ w) (Ne.symm hwx)
    simp only [hr, htt] at h2'
    have hxw1 : T x w = 1 := by
      rcases Nat.lt_or_ge (T x w) 2 with h | h
      · omega
      · nlinarith
    -- a second neighbour
    have hex' : ∃ v, v ≠ x ∧ v ≠ w ∧ T x v ≠ 0 := by
      by_contra hne
      push Not at hne
      have h := Finset.sum_subset (Finset.subset_univ {x, w})
        (f := fun z => T x z * T x z) fun z _ hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
          rw [hne z hz.1 hz.2, zero_mul]
      rw [Finset.sum_pair (Ne.symm hwx), hr, htt, hxw1] at h
      omega
    obtain ⟨v, hvx, hvw, hxv⟩ := hex'
    have hvfix : σ v = v := by
      by_contra h
      exact hxv (hmov v hvx h)
    have h3 := sum_three_le (f := fun z => T x z * T x z) (Ne.symm hwx) (Ne.symm hvx)
      (Ne.symm hvw)
    simp only [hr, htt, hxw1] at h3
    have hxv1 : T x v = 1 := by
      rcases Nat.lt_or_ge (T x v) 2 with h | h
      · omega
      · nlinarith
    have hx0 : ∀ z, z ≠ x → z ≠ w → z ≠ v → T x z = 0 := fun z hzx hzw hzv =>
      mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => T x z * T x z)
        (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hvw)
        (by simp only [hr, htt, hxw1, hxv1]; omega) hzx hzw hzv)
    -- the off-diagonal relations at `(x, w)` and `(w, v)`
    have hxw' := hoff x w (Ne.symm hwx) (by rw [hx]; exact hwx)
    rw [← Finset.sum_subset (Finset.subset_univ {x, w, v}) fun z _ hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        rw [hx0 z hz.1 hz.2.1 hz.2.2, zero_mul],
      Finset.sum_insert (by simp [Ne.symm hwx, Ne.symm hvx]), Finset.sum_pair (Ne.symm hvw),
      hxw1, hxv1] at hxw'
    have hwv' := hoff w v (Ne.symm hvw) (by rw [hwfix]; exact hvw)
    have hwv3 := sum_three_le (f := fun z => T w z * T z v) (Ne.symm hwx) (Ne.symm hvx)
      (Ne.symm hvw)
    rw [hwv'] at hwv3
    have hTwx : T w x = 1 := by rw [hT]; exact hxw1
    have hTvw : T v w = T w v := hT v w
    simp only [hTwx, hxv1] at hwv3
    have hwv1 : 1 ≤ T w v := by omega
    have hdiag : T w w + T v v = 0 := by nlinarith
    have hww : T w w = 0 := by omega
    have hvv : T v v = 0 := by omega
    rw [hww, hTvw] at hxw'
    have hxx : T x x = 0 := by omega
    have hwv : T w v = 1 := by omega
    refine ⟨hxx, w, v, hwx, hvx, hvw.symm, hwfix, hvfix, hxw1, hxv1, hwv, hww, hvv,
      fun z hzx hzw hzv => ⟨hx0 z hzx hzw hzv, ?_, ?_⟩⟩
    · have hrw := hrow w
      simp only [hwfix, hww, ↓reduceIte] at hrw
      exact mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => T w z * T w z)
        (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hvw)
        (by simp only [hrw, hTwx, hww, hwv]; omega) hzx hzw hzv)
    · have hrv := hrow v
      simp only [hvfix, hvv, ↓reduceIte] at hrv
      have hTvx : T v x = 1 := by rw [hT]; exact hxv1
      exact mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => T v z * T v z)
        (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hvw)
        (by simp only [hrv, hTvx, hTvw, hwv, hvv]; omega) hzx hzw hzv)

end RepS3Local

/-! ### `Rep(S₃)` -/

section RepS3

variable [Fintype κ] [DecidableEq κ] {M : Fin 3 → κ → κ → ℕ}

/-- The relations `ψ × ψ = 1`, `π × ψ = π` and `π × π = 1 + π + ψ` on the blocks
(arXiv:2203.12563, line 1934, through the relation of lines 564–565). -/
private theorem repS3_relations (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (x y : κ) :
    (∑ z, M 2 x z * M 2 z y = if x = y then 1 else 0) ∧
    (∑ z, M 2 x z * M 1 z y = M 1 x y) ∧
    (∑ z, M 1 x z * M 1 z y = (if x = y then 1 else 0) + M 1 x y + M 2 x y) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := hM 2 2 x y
    simp only [repS3Fusion, Fin.sum_univ_three, hunit] at h
    simpa using h.symm
  · have h := hM 1 2 x y
    simp only [repS3Fusion, Fin.sum_univ_three] at h
    simpa using h.symm
  · have h := hM 1 1 x y
    simp only [repS3Fusion, Fin.sum_univ_three, hunit] at h
    simpa [add_assoc] using h.symm

/-- **`ψ` acts by an involution of the blocks.** For a dual representation of `Rep(S₃)` with
trivial unit, `M_ψ` is the permutation matrix of an involution `σ` with `M_π (σx) = M_π x`. -/
private theorem repS3_exists_involution (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) :
    ∃ σ : κ → κ, (∀ x y, M 2 x y = if y = σ x then 1 else 0) ∧ (∀ x, σ (σ x) = x) ∧
      ∀ x y, M 1 (σ x) y = M 1 x y := by
  have hrow : ∀ x, ∃ w, M 2 x w = 1 ∧ ∀ u, u ≠ w → M 2 x u = 0 := fun x => by
    refine exists_eq_one_of_sum_mul_self_eq_one ?_
    have h := (repS3_relations hM hunit x x).1
    simp only [↓reduceIte] at h
    rw [← h]
    exact Finset.sum_congr rfl fun z _ => by rw [← hdual 2 z x]; rfl
  choose σ hσ1 hσ0 using hrow
  have hσ : ∀ x y, M 2 x y = if y = σ x then 1 else 0 := fun x y => by
    by_cases h : y = σ x
    · simp only [h, ↓reduceIte, hσ1]
    · simp only [h, ↓reduceIte, hσ0 x y h]
  refine ⟨σ, hσ, fun x => ?_, fun x y => ?_⟩
  · have h : M 2 (σ x) x = 1 := by rw [← hdual 2 x (σ x)]; exact hσ1 x
    rw [hσ] at h
    by_contra hne
    simp [Ne.symm hne] at h
  · have h := (repS3_relations hM hunit x y).2.1
    rw [Fintype.sum_eq_single (σ x) fun z hz => by rw [hσ0 x z hz, zero_mul], hσ1, one_mul] at h
    exact h

omit [Fintype κ] in
/-- Assembling a summand of a representation of `Rep(S₃)` from the action of `π` on a family
of blocks closed under `π` and under the involution `σ` of `ψ`. -/
private theorem isNIMRepSummand_repS3_of {k : ℕ} {M' : Fin 3 → Matrix (Fin k) (Fin k) ℕ}
    (hM'0 : M' 0 = 1) {π : Fin k → Fin k} (hM'2 : ∀ i j, M' 2 i j = if j = π i then 1 else 0)
    {σ : κ → κ} (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0)
    (hσ : ∀ x y, M 2 x y = if y = σ x then 1 else 0) {f : Fin k → κ}
    (hf : Function.Injective f) (hfσ : ∀ i, σ (f i) = f (π i))
    (hclosed : ∀ i z, z ∉ Set.range f → M 1 (f i) z = 0)
    (hentries : ∀ i j, M 1 (f i) (f j) = M' 1 i j) : IsNIMRepSummand M M' f := by
  have ha : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  refine ⟨hf, fun a i z hz => ?_, fun a i j => ?_⟩
  · have hne : ∀ l, f l ≠ z := fun l h => hz ⟨l, h⟩
    rcases ha a with rfl | rfl | rfl
    · simp [hunit, hne i]
    · exact hclosed i z hz
    · simp [hσ, hfσ, Ne.symm (hne (π i))]
  · rcases ha a with rfl | rfl | rfl
    · rw [hunit, hM'0]
      by_cases h : i = j
      · subst h
        simp
      · simp only [hf.ne h, ↓reduceIte, Matrix.one_apply_ne h]
    · exact hentries i j
    · simp [hσ, hfσ, hM'2, hf.eq_iff]

/-- The local facts behind the classification: the involution `σ` of `ψ`, symmetry of `T = M_π`,
`T (σx) = T x`, the diagonal relation `∑_z T_{xz}² = 1 + T_{xx} + [σx = x]`, and the off-diagonal
relation `∑_z T_{xz} T_{zy} = T_{xy}` away from `y = x` and `y = σx`. -/
private theorem repS3_exists_local (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) :
    ∃ σ : κ → κ, (∀ x y, M 2 x y = if y = σ x then 1 else 0) ∧ (∀ x, σ (σ x) = x) ∧
      (∀ x y, M 1 (σ x) y = M 1 x y) ∧ (∀ x y, M 1 x y = M 1 y x) ∧
      (∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 1 x x + if σ x = x then 1 else 0) ∧
      ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 1 x z * M 1 z y = M 1 x y := by
  obtain ⟨σ, hσ, hσσ, hTσ⟩ := repS3_exists_involution hM hunit hdual
  have hT : ∀ x y, M 1 x y = M 1 y x := fun x y => (hdual 1 y x).symm
  have hrow : ∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 1 x x + if σ x = x then 1 else 0 :=
    fun x => by
      have h := (repS3_relations hM hunit x x).2.2
      have e : (if x = σ x then 1 else 0) = (if σ x = x then 1 else 0) := by simp only [eq_comm]
      rw [hσ, e] at h
      simp only [↓reduceIte] at h
      rw [← h]
      exact Finset.sum_congr rfl fun z _ => by rw [hT z x]
  have hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 1 x z * M 1 z y = M 1 x y :=
    fun x y hxy hyσ => by
      have h := (repS3_relations hM hunit x y).2.2
      rw [hσ] at h
      simpa [hxy, hyσ] using h
  exact ⟨σ, hσ, hσσ, hTσ, hT, hrow, hoff⟩

omit [Fintype κ] [DecidableEq κ] in
private theorem ne_of_notMem_range {k : ℕ} {f : Fin k → κ} {z : κ} (hz : z ∉ Set.range f)
    (i : Fin k) : z ≠ f i := fun h => hz ⟨i, h.symm⟩

/-- The summand of a block moved by the involution of `ψ`: the `ℤ₂` or the `S₃` phase. -/
private theorem repS3_summand_of_ne {σ : κ → κ}
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0)
    (hσ : ∀ x y, M 2 x y = if y = σ x then 1 else 0) (hσσ : ∀ x, σ (σ x) = x)
    (hT : ∀ x y, M 1 x y = M 1 y x) (hTσ : ∀ x y, M 1 (σ x) y = M 1 x y)
    (hrow : ∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 1 x x + if σ x = x then 1 else 0)
    (hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 1 x z * M 1 z y = M 1 x y)
    {x : κ} (hx : σ x ≠ x) :
    (∃ f : Fin 2 → κ, IsNIMRepSummand M repS3Z2 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 3 → κ, IsNIMRepSummand M repS3Fusion f ∧ x ∈ Set.range f) := by
  have hxy : x ≠ σ x := fun h => hx h.symm
  have hTxy : M 1 x (σ x) = M 1 x x := by rw [hT, hTσ]
  have hTyx : M 1 (σ x) x = M 1 x x := hTσ x x
  have hTyy : M 1 (σ x) (σ x) = M 1 x x := by rw [hTσ, hTxy]
  rcases repS3_of_ne hT hTσ hrow hoff hx with
    ⟨h1, h0⟩ | ⟨h0, w, hwx, hwy, hwfix, hxw, hww, hx0, hw0⟩
  · left
    refine ⟨![x, σ x], isNIMRepSummand_repS3_of (π := ![1, 0]) rfl
      (fun i j => by fin_cases i <;> fin_cases j <;> rfl) hunit hσ
      (injective_vecCons_two hxy) (fun i => ?_) (fun i z hz => ?_) (fun i j => ?_), 0, rfl⟩
    · fin_cases i <;> simp [hσσ]
    · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
      have hz1 : z ≠ σ x := by simpa using ne_of_notMem_range hz 1
      fin_cases i
      · simpa using h0 z hz0 hz1
      · simpa [hTσ] using h0 z hz0 hz1
    · fin_cases i <;> fin_cases j <;> simp [repS3Z2, h1, hTxy, hTyx, hTyy]
  · right
    have hTwx : M 1 w x = 1 := by rw [hT]; exact hxw
    have hTwy : M 1 w (σ x) = 1 := by rw [hT, hTσ]; exact hxw
    have hTyw : M 1 (σ x) w = 1 := by rw [hTσ]; exact hxw
    refine ⟨![x, w, σ x], isNIMRepSummand_repS3_of (π := ![2, 1, 0]) rfl
      (fun i j => by fin_cases i <;> fin_cases j <;> rfl) hunit hσ
      (injective_vecCons_three (Ne.symm hwx) hxy hwy) (fun i => ?_) (fun i z hz => ?_)
      (fun i j => ?_), 0, rfl⟩
    · fin_cases i <;> simp [hσσ, hwfix]
    · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
      have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
      have hz2 : z ≠ σ x := by simpa using ne_of_notMem_range hz 2
      fin_cases i
      · simpa using hx0 z hz1
      · simpa using hw0 z hz0 hz2 hz1
      · simpa [hTσ] using hx0 z hz1
    · fin_cases i <;> fin_cases j <;>
        simp [repS3Fusion, h0, hxw, hww, hTxy, hTyx, hTyy, hTwx, hTwy, hTyw]

/-- **Classification of the dual representations of `Rep(S₃)`** (arXiv:2203.12563,
lines 1933–1989). In a nonnegative integer representation of `Rep(S₃)` on any finite set of
blocks, with the unit acting trivially and every label acting by a symmetric matrix (the
duality of a module category, all labels being self-dual), every block lies in a direct summand
isomorphic to one of the four printed phases: `ℤ₁` (one block), `ℤ₂` (two blocks), `ℤ₃` (three
blocks, with the `ψ` row corrected as in `MPOTensor.repS3Z3`) or `S₃` (the regular
representation). -/
theorem exists_isNIMRepSummand_repS3 (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) (x : κ) :
    (∃ f : Fin 1 → κ, IsNIMRepSummand M repS3Z1 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 2 → κ, IsNIMRepSummand M repS3Z2 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 3 → κ, IsNIMRepSummand M repS3Z3 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 3 → κ, IsNIMRepSummand M repS3Fusion f ∧ x ∈ Set.range f) := by
  obtain ⟨σ, hσ, hσσ, hTσ, hT, hrow, hoff⟩ := repS3_exists_local hM hunit hdual
  by_cases hx : σ x = x
  swap
  · rcases repS3_summand_of_ne hunit hσ hσσ hT hTσ hrow hoff hx with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  rcases repS3_of_eq hT hσσ hTσ hrow hoff hx with ⟨h2, h0⟩ | ⟨-, w, hw, hxw⟩ |
      ⟨h0, w, v, hwx, hvx, hwv, hwfix, hvfix, hxw, hxv, hTwv, hww, hvv, hzero⟩
  · left
    refine ⟨![x], isNIMRepSummand_repS3_of (π := ![0]) rfl
      (fun i j => by fin_cases i; fin_cases j; rfl) hunit hσ
      (fun i j _ => Subsingleton.elim i j) (fun i => ?_) (fun i z hz => ?_) (fun i j => ?_),
      0, rfl⟩
    · fin_cases i
      simpa using hx
    · fin_cases i
      simpa using h0 z (by simpa using ne_of_notMem_range hz 0)
    · fin_cases i
      fin_cases j
      simpa [repS3Z1] using h2
  · -- `x` is the middle block of the `S₃` summand of `w`
    have hwx : M 1 w x ≠ 0 := by rwa [hT]
    right; right; right
    rcases repS3_summand_of_ne hunit hσ hσσ hT hTσ hrow hoff hw with
      ⟨f, hf, i, rfl⟩ | ⟨f, hf, i, rfl⟩
    · obtain ⟨j, hj⟩ := hf.mem_range hwx
      have h1 := hf.2.2 2 j j
      rw [hj, hσ, hx] at h1
      fin_cases j <;> simp [repS3Z2] at h1
    · exact ⟨f, hf, hf.mem_range hwx⟩
  · right; right; left
    have hTwx : M 1 w x = 1 := by rw [hT]; exact hxw
    have hTvx : M 1 v x = 1 := by rw [hT]; exact hxv
    have hTvw : M 1 v w = 1 := by rw [hT]; exact hTwv
    refine ⟨![x, w, v], isNIMRepSummand_repS3_of (π := ![0, 1, 2]) rfl
      (fun i j => by fin_cases i <;> fin_cases j <;> rfl) hunit hσ
      (injective_vecCons_three (Ne.symm hwx) (Ne.symm hvx) hwv) (fun i => ?_)
      (fun i z hz => ?_) (fun i j => ?_), 0, rfl⟩
    · fin_cases i <;> simp [hx, hwfix, hvfix]
    · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
      have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
      have hz2 : z ≠ v := by simpa using ne_of_notMem_range hz 2
      have h := hzero z hz0 hz1 hz2
      fin_cases i
      · simpa using h.1
      · simpa using h.2.1
      · simpa using h.2.2
    · fin_cases i <;> fin_cases j <;>
        simp [repS3Z3, h0, hxw, hxv, hTwv, hww, hvv, hTwx, hTvx, hTvw]

/-- **The indecomposable dual representations of `Rep(S₃)` are the four printed phases**
(arXiv:2203.12563, lines 1933–1989: the phases are labelled by the subgroups `ℤ₁`, `ℤ₂`, `ℤ₃`,
`S₃`). A nonempty dual representation with trivial unit on which `π` acts indecomposably is, up to
relabelling the blocks, the `ℤ₁`, `ℤ₂`, `ℤ₃` or `S₃` phase. -/
theorem exists_equiv_of_isIndecomposable_repS3 [Nonempty κ] (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id)
    (hind : Matrix.IsIndecomposable (M 1)) :
    (∃ e : κ ≃ Fin 1, ∀ a x y, M a x y = repS3Z1 a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 2, ∀ a x y, M a x y = repS3Z2 a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 3, ∀ a x y, M a x y = repS3Z3 a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 3, ∀ a x y, M a x y = repS3Fusion a (e x) (e y)) := by
  obtain ⟨x⟩ := ‹Nonempty κ›
  rcases exists_isNIMRepSummand_repS3 hM hunit hdual x with
    ⟨f, hf, -⟩ | ⟨f, hf, -⟩ | ⟨f, hf, -⟩ | ⟨f, hf, -⟩
  · exact Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))
  · exact Or.inr (Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind)))
  · exact Or.inr (Or.inr (Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))))
  · exact Or.inr (Or.inr (Or.inr (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))))

end RepS3

/-! ### `su(2)₄` -/

section SU24

variable [Fintype κ] [DecidableEq κ] {M : Fin 5 → κ → κ → ℕ}

omit [DecidableEq κ] in
/-- The integer labels of a representation of `su(2)₄` represent `Rep(S₃)` (arXiv:2203.12563,
line 1934). -/
private theorem isNIMRep_repS3_comp (hM : IsNIMRep su24Fusion M) :
    IsNIMRep repS3Fusion fun a => M (repS3ToSU24 a) := by
  intro a b x y
  change ∑ c, repS3Fusion a b c * M (repS3ToSU24 c) x y =
    ∑ z, M (repS3ToSU24 b) x z * M (repS3ToSU24 a) z y
  rw [← hM (repS3ToSU24 a) (repS3ToSU24 b) x y]
  have ha : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases ha a with rfl | rfl | rfl <;> rcases ha b with rfl | rfl | rfl <;>
    simp [Fin.sum_univ_five, Fin.sum_univ_three, su24Fusion, repS3Fusion, repS3ToSU24,
      Matrix.one_apply]

/-- The local facts behind the classification for `su(2)₄`, with `Q = M_{1/2}` and
`T = M_1`: the `Rep(S₃)` facts of the integer labels, and the relations
`1/2 × 1/2 = 0 + 1` and `1/2 × 2 = 2 × 1/2 = 3/2` (arXiv:2203.12563, lines 1891–1904). -/
private structure SU24Local (M : Fin 5 → κ → κ → ℕ) (σ : κ → κ) : Prop where
  unit : ∀ x y, M 0 x y = if x = y then 1 else 0
  perm : ∀ x y, M 4 x y = if y = σ x then 1 else 0
  invol : ∀ x, σ (σ x) = x
  T_σ : ∀ x y, M 2 (σ x) y = M 2 x y
  T_symm : ∀ x y, M 2 x y = M 2 y x
  T_row : ∀ x, ∑ z, M 2 x z * M 2 x z = 1 + M 2 x x + if σ x = x then 1 else 0
  T_off : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 2 x z * M 2 z y = M 2 x y
  Q_symm : ∀ x y, M 1 x y = M 1 y x
  Q_row : ∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 2 x x
  Q_off : ∀ x y, x ≠ y → ∑ z, M 1 x z * M 1 z y = M 2 x y
  three : ∀ x y, M 3 x y = M 1 x (σ y)
  Q_σ : ∀ x y, M 1 (σ x) y = M 1 x (σ y)

private theorem su24_exists_local (hM : IsNIMRep su24Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) :
    ∃ σ, SU24Local M σ := by
  obtain ⟨σ, hσ, hσσ, hTσ, hT, hrow, hoff⟩ := repS3_exists_local (isNIMRep_repS3_comp hM)
    (fun x y => hunit x y) (fun a x y => hdual (repS3ToSU24 a) x y)
  have hQ : ∀ x y, M 1 x y = M 1 y x := fun x y => (hdual 1 y x).symm
  have h11 : ∀ x y, ∑ z, M 1 x z * M 1 z y = (if x = y then 1 else 0) + M 2 x y := fun x y => by
    have h := hM 1 1 x y
    simp only [su24Fusion, Fin.sum_univ_five, hunit] at h
    simpa using h.symm
  have h3a : ∀ x y, M 3 x y = ∑ z, M 4 x z * M 1 z y := fun x y => by
    have h := hM 1 4 x y
    simp only [su24Fusion, Fin.sum_univ_five] at h
    simpa using h
  have h3b : ∀ x y, M 3 x y = ∑ z, M 1 x z * M 4 z y := fun x y => by
    have h := hM 4 1 x y
    simp only [su24Fusion, Fin.sum_univ_five] at h
    simpa using h
  have hσ' : ∀ x y, M 4 x y = if y = σ x then 1 else 0 := hσ
  have hthree : ∀ x y, M 3 x y = M 1 x (σ y) := fun x y => by
    rw [h3b, Fintype.sum_eq_single (σ y) fun z hz => by
      have : ¬ y = σ z := fun h => hz (by rw [h, hσσ])
      simp [hσ', this], hσ', hσσ]
    simp
  refine ⟨σ, hunit, hσ', hσσ, hTσ, hT, hrow, hoff, hQ, fun x => ?_, fun x y hxy => ?_, hthree,
    fun x y => ?_⟩
  · have h := h11 x x
    simp only [↓reduceIte] at h
    rw [← h]
    exact Finset.sum_congr rfl fun z _ => by rw [hQ z x]
  · simpa [hxy] using h11 x y
  · rw [← hthree, h3a, Fintype.sum_eq_single (σ x) fun z hz => by
      simp [hσ', hz], hσ']
    simp

/-- The label `2` of `su(2)₄` acts on the labels by the reflection `j ↦ 4 - j`. -/
private def su24Reflect : Fin 5 → Fin 5 := ![4, 3, 2, 1, 0]

private theorem su24Fusion_four_apply (i j : Fin 5) :
    su24Fusion 4 i j = if j = su24Reflect i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem su24Fusion_three_apply (i j : Fin 5) :
    su24Fusion 3 i j = su24Fusion 1 i (su24Reflect j) := by
  fin_cases i <;> fin_cases j <;> simp [su24Fusion, su24Reflect]

namespace SU24Local

variable {σ : κ → κ} (L : SU24Local M σ)
include L

theorem of_ne {x : κ} (hx : σ x ≠ x) :
    (M 2 x x = 1 ∧ ∀ z, z ≠ x → z ≠ σ x → M 2 x z = 0) ∨
    (M 2 x x = 0 ∧ ∃ w, w ≠ x ∧ w ≠ σ x ∧ σ w = w ∧ M 2 x w = 1 ∧ M 2 w w = 1 ∧
      (∀ z, z ≠ w → M 2 x z = 0) ∧ ∀ z, z ≠ x → z ≠ σ x → z ≠ w → M 2 w z = 0) :=
  repS3_of_ne L.T_symm L.T_σ L.T_row L.T_off hx

theorem of_eq {x : κ} (hx : σ x = x) :
    (M 2 x x = 2 ∧ ∀ z, z ≠ x → M 2 x z = 0) ∨
    (M 2 x x = 1 ∧ ∃ w, σ w ≠ w ∧ M 2 x w ≠ 0) ∨
    (M 2 x x = 0 ∧ ∃ w v, w ≠ x ∧ v ≠ x ∧ w ≠ v ∧ σ w = w ∧ σ v = v ∧ M 2 x w = 1 ∧
      M 2 x v = 1 ∧ M 2 w v = 1 ∧ M 2 w w = 0 ∧ M 2 v v = 0 ∧
      ∀ z, z ≠ x → z ≠ w → z ≠ v → M 2 x z = 0 ∧ M 2 w z = 0 ∧ M 2 v z = 0) :=
  repS3_of_eq L.T_symm L.invol L.T_σ L.T_row L.T_off hx

theorem T_le_two (x : κ) : M 2 x x ≤ 2 := by
  by_cases hx : σ x = x
  · rcases L.of_eq hx with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · rcases L.of_ne hx with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem T_σσ (x : κ) : M 2 (σ x) (σ x) = M 2 x x := by
  rw [L.T_σ, L.T_symm, L.T_σ]

/-- Assembling a summand of a representation of `su(2)₄` from the actions of `1/2` and `1` on a
family of blocks closed under them and under the involution `σ` of `2`. -/
theorem isNIMRepSummand {k : ℕ} {M' : Fin 5 → Matrix (Fin k) (Fin k) ℕ} (hM'0 : M' 0 = 1)
    {π : Fin k → Fin k} (hM'4 : ∀ i j, M' 4 i j = if j = π i then 1 else 0)
    (hM'3 : ∀ i j, M' 3 i j = M' 1 i (π j)) {f : Fin k → κ} (hf : Function.Injective f)
    (hfσ : ∀ i, σ (f i) = f (π i))
    (hc1 : ∀ i z, z ∉ Set.range f → M 1 (f i) z = 0)
    (hc2 : ∀ i z, z ∉ Set.range f → M 2 (f i) z = 0)
    (he1 : ∀ i j, M 1 (f i) (f j) = M' 1 i j) (he2 : ∀ i j, M 2 (f i) (f j) = M' 2 i j) :
    IsNIMRepSummand M M' f := by
  have ha : ∀ a : Fin 5, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by decide
  refine ⟨hf, fun a i z hz => ?_, fun a i j => ?_⟩
  · have hne : ∀ l, f l ≠ z := fun l h => hz ⟨l, h⟩
    rcases ha a with rfl | rfl | rfl | rfl | rfl
    · simp [L.unit, hne i]
    · exact hc1 i z hz
    · exact hc2 i z hz
    · rw [L.three]
      refine hc1 i _ fun ⟨j, hj⟩ => hz ⟨π j, ?_⟩
      rw [← hfσ, hj, L.invol]
    · simp [L.perm, hfσ, Ne.symm (hne (π i))]
  · rcases ha a with rfl | rfl | rfl | rfl | rfl
    · rw [L.unit, hM'0]
      by_cases h : i = j
      · subst h
        simp
      · simp only [hf.ne h, ↓reduceIte, Matrix.one_apply_ne h]
    · exact he1 i j
    · exact he2 i j
    · rw [L.three, hfσ, he1, hM'3]
    · simp [L.perm, hfσ, hM'4, hf.eq_iff]

/-- **The module `𝓜_TY` around a `ℤ₃` block** (arXiv:2203.12563, lines 1911–1927): a block fixed
by `2` with `M_1` vanishing on its diagonal lies in a summand isomorphic to `𝓜_TY`. -/
theorem summand_of_fixed_zero {x : κ} (hx : σ x = x) (h0 : M 2 x x = 0) :
    ∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f := by
  rcases L.of_eq hx with ⟨h2, -⟩ | ⟨h1, -⟩ |
      ⟨-, w, v, hwx, hvx, hwv, hwfix, hvfix, hxw, hxv, hTwv, hww, hvv, hzero⟩
  · omega
  · omega
  obtain ⟨s, hxs, hx0⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := M 1 x)
    (by rw [L.Q_row, h0])
  have hQ1 : ∀ y, y ≠ x → M 1 s y = M 2 x y := fun y hy => by
    have h := L.Q_off x y (Ne.symm hy)
    rwa [Fintype.sum_eq_single s fun z hz => by rw [hx0 z hz, zero_mul], hxs, one_mul] at h
  have hsx : M 1 s x = 1 := by rw [L.Q_symm]; exact hxs
  have hsw : M 1 s w = 1 := (hQ1 w hwx).trans hxw
  have hsv : M 1 s v = 1 := (hQ1 v hvx).trans hxv
  have h3 := sum_three_le (f := fun z => M 1 s z * M 1 s z) (Ne.symm hwx) (Ne.symm hvx) hwv
  simp only [hsx, hsw, hsv, L.Q_row] at h3
  have hss : M 2 s s = 2 := by have := L.T_le_two s; omega
  have hsfix : σ s = s := by
    by_contra h
    rcases L.of_ne h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hs0 : ∀ z, z ≠ s → M 2 s z = 0 := by
    rcases L.of_eq hsfix with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h
    · omega
    · omega
  have hsQ0 : ∀ z, z ≠ x → z ≠ w → z ≠ v → M 1 s z = 0 := fun z h1 h2 h3' =>
    mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => M 1 s z * M 1 s z)
      (Ne.symm hwx) (Ne.symm hvx) hwv (by simp only [hsx, hsw, hsv, L.Q_row, hss]; omega)
      h1 h2 h3')
  have hsx' : s ≠ x := fun h => by rw [h] at hss; omega
  have hsw' : s ≠ w := fun h => by rw [h] at hss; omega
  have hsv' : s ≠ v := fun h => by rw [h] at hss; omega
  have hrowQ : ∀ y, σ y = y → M 2 y y = 0 → M 1 y s = 1 → ∀ z, z ≠ s → M 1 y z = 0 :=
    fun y _ hyy hys => by
      obtain ⟨t, hyt, hy0⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := M 1 y)
        (by rw [L.Q_row, hyy])
      have hts : t = s := by
        by_contra h
        rw [hy0 s (Ne.symm h)] at hys
        exact zero_ne_one hys
      rw [← hts]
      exact hy0
  have hw0 := hrowQ w hwfix hww (by rw [L.Q_symm]; exact hsw)
  have hv0 := hrowQ v hvfix hvv (by rw [L.Q_symm]; exact hsv)
  have hQx := eq_ite_of_forall (g := M 1 x) (P := fun z => z = s)
    (fun z hz => hz ▸ hxs) hx0
  have hQw := eq_ite_of_forall (g := M 1 w) (P := fun z => z = s)
    (fun z hz => hz ▸ (by rw [L.Q_symm]; exact hsw)) hw0
  have hQv := eq_ite_of_forall (g := M 1 v) (P := fun z => z = s)
    (fun z hz => hz ▸ (by rw [L.Q_symm]; exact hsv)) hv0
  have hQs := eq_ite_of_forall (g := M 1 s) (P := fun z => z = x ∨ z = w ∨ z = v)
    (fun z hz => by rcases hz with rfl | rfl | rfl <;> assumption)
    (fun z hz => by push Not at hz; exact hsQ0 z hz.1 hz.2.1 hz.2.2)
  have hTwx : M 2 w x = 1 := by rw [L.T_symm]; exact hxw
  have hTvx : M 2 v x = 1 := by rw [L.T_symm]; exact hxv
  have hTvw : M 2 v w = 1 := by rw [L.T_symm]; exact hTwv
  have hTx := eq_ite_of_forall (g := M 2 x) (P := fun z => z = w ∨ z = v)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by
      push Not at hz
      by_cases hzx : z = x
      · rw [hzx]; exact h0
      · exact (hzero z hzx hz.1 hz.2).1)
  have hTw := eq_ite_of_forall (g := M 2 w) (P := fun z => z = x ∨ z = v)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by
      push Not at hz
      by_cases hzw : z = w
      · rw [hzw]; exact hww
      · exact (hzero z hz.1 hzw hz.2).2.1)
  have hTv := eq_ite_of_forall (g := M 2 v) (P := fun z => z = x ∨ z = w)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by
      push Not at hz
      by_cases hzv : z = v
      · rw [hzv]; exact hvv
      · exact (hzero z hz.1 hz.2 hzv).2.2)
  refine ⟨![x, w, v, s], L.isNIMRepSummand (π := id) rfl
    (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (injective_vecCons_four (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hsx') hwv (Ne.symm hsw')
      (Ne.symm hsv'))
    (fun i => by fin_cases i <;> simp [hx, hwfix, hvfix, hsfix]) (fun i z hz => ?_)
    (fun i z hz => ?_) (fun i j => ?_) (fun i j => ?_), 0, rfl⟩
  · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ v := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ s := by simpa using ne_of_notMem_range hz 3
    fin_cases i <;> simp [hQx, hQw, hQv, hQs, hz0, hz1, hz2, hz3]
  · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ v := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ s := by simpa using ne_of_notMem_range hz 3
    fin_cases i <;> simp [hTx, hTw, hTv, hs0 z hz3, hz0, hz1, hz2]
  · fin_cases i <;> fin_cases j <;>
      simp [su24TY, hQx, hQw, hQv, hQs, hwx, hvx, hwv, hsx', hsw', hsv', Ne.symm hwx,
        Ne.symm hvx, Ne.symm hwv, Ne.symm hsx', Ne.symm hsw', Ne.symm hsv']
  · fin_cases i <;> fin_cases j <;>
      simp [su24TY, hTx, hTw, hTv, hss, hs0, hwx, hvx, hwv, hsx', hsw', hsv', Ne.symm hwx,
        Ne.symm hvx, Ne.symm hwv, Ne.symm hsx', Ne.symm hsw', Ne.symm hsv']

/-- **The module `𝓜_TY` around a `ℤ₁` block** (arXiv:2203.12563, lines 1911–1927): a block with
`M_1` equal to `2` on its diagonal lies in a summand isomorphic to `𝓜_TY`. Each neighbour `u` of
the block `s` under `1/2` has `s` as its only neighbour, so `u` is fixed by `2` with `M_1`
vanishing on its diagonal. -/
theorem summand_of_two {s : κ} (h2 : M 2 s s = 2) :
    ∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ s ∈ Set.range f := by
  have hsfix : σ s = s := by
    by_contra h
    rcases L.of_ne h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hs0 : ∀ z, z ≠ s → M 2 s z = 0 := by
    rcases L.of_eq hsfix with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h
    · omega
    · omega
  have hrow := L.Q_row s
  rw [h2] at hrow
  -- every neighbour of `s` has `s` as its only neighbour
  have hnb : ∀ u, M 1 s u ≠ 0 → ∀ v, v ≠ s → M 1 u v = 0 := fun u hu v hv => by
    have h := L.Q_off s v (Ne.symm hv)
    rw [hs0 v hv] at h
    have hle := Finset.single_le_sum (fun z _ => Nat.zero_le (M 1 s z * M 1 z v))
      (Finset.mem_univ u)
    rw [h] at hle
    exact (mul_eq_zero.mp (by omega)).resolve_left hu
  -- a neighbour with a single neighbour has `M_1` vanishing on its diagonal
  have hlone : ∀ u, M 1 s u ≠ 0 → u ≠ s ∧ M 2 u u = 0 := fun u hu => by
    have hrowu := L.Q_row u
    rw [Fintype.sum_eq_single s fun z hz => by rw [hnb u hu z hz, zero_mul]] at hrowu
    have hle := L.T_le_two u
    have hus : M 1 u s ≠ 0 := by rwa [L.Q_symm]
    refine ⟨fun h => ?_, ?_⟩
    · rw [h] at hu
      have h' := hrow
      rw [Fintype.sum_eq_single s fun z hz => by rw [hnb s hu z hz, zero_mul]] at h'
      exact mul_self_ne_two_three.2 (by omega)
    · rcases Nat.lt_or_ge (M 1 u s) 2 with h' | h'
      · interval_cases (M 1 u s) <;> omega
      · nlinarith
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => M 1 s z * M 1 s z) (by omega)
  have hsu : M 1 s u ≠ 0 := fun h => hu (by simp [h])
  obtain ⟨hus, huu⟩ := hlone u hsu
  have hufix : σ u = u := by
    by_contra hne
    rcases L.of_ne hne with ⟨h1, -⟩ | ⟨-, w, hwu, -, -, huw, hww, -, -⟩
    · omega
    have h := L.Q_off u w (Ne.symm hwu)
    rw [Fintype.sum_eq_single s fun z hz => by rw [hnb u hsu z hz, zero_mul], huw] at h
    have hsw : M 1 s w ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
    have := (hlone w hsw).2
    omega
  obtain ⟨f, hf, i, hi⟩ := L.summand_of_fixed_zero hufix huu
  exact ⟨f, hf, hf.mem_range (a := 1) (u := i) (by rw [hi, L.Q_symm]; exact hsu)⟩

/-- **The regular `su(2)₄` phase around a corner of an `S₃` block** (arXiv:2203.12563,
line 1909): a block moved by `2` with `M_1` vanishing on its diagonal lies in a summand
isomorphic to the regular representation. With `a ↦ 0`, the neighbour `p` of `a` under `1/2`
is `1/2`, the middle block `w` of the `S₃` summand is `1`, `σ p` is `3/2` and `σ a` is `2`. -/
theorem summand_of_corner {a : κ} (ha : σ a ≠ a) (h0 : M 2 a a = 0) :
    ∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ a ∈ Set.range f := by
  rcases L.of_ne ha with ⟨h1, -⟩ | ⟨-, w, hwa, hwb, hwfix, haw, hww, ha0, hw0⟩
  · omega
  have hab : a ≠ σ a := fun h => ha h.symm
  obtain ⟨p, hap, ha0Q⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := M 1 a)
    (by rw [L.Q_row, h0])
  have hpv : ∀ v, v ≠ a → M 1 p v = M 2 a v := fun v hv => by
    have h := L.Q_off a v (Ne.symm hv)
    rwa [Fintype.sum_eq_single p fun z hz => by rw [ha0Q z hz, zero_mul], hap, one_mul] at h
  have hpw : M 1 p w = 1 := (hpv w hwa).trans haw
  have hpa : M 1 p a = 1 := by rw [L.Q_symm]; exact hap
  have hp0 : ∀ v, v ≠ a → v ≠ w → M 1 p v = 0 := fun v hva hvw =>
    (hpv v hva).trans (ha0 v hvw)
  have hpfix : σ p ≠ p := fun h => by
    have h' := L.Q_σ p a
    rw [h, hpa] at h'
    rw [hp0 (σ a) (Ne.symm hab) (Ne.symm hwb)] at h'
    exact zero_ne_one h'.symm
  have hpa' : p ≠ a := fun h => by
    rw [h] at hpw
    rw [ha0Q w (fun h' => hwa (h'.trans h))] at hpw
    exact zero_ne_one hpw
  have hpw' : p ≠ w := fun h => hpfix (by rw [h, hwfix])
  have hpp : M 2 p p = 1 := by
    have h := L.Q_row p
    rw [← Finset.sum_subset (Finset.subset_univ {a, w}) fun z _ hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        rw [hp0 z hz.1 hz.2, zero_mul],
      Finset.sum_pair (Ne.symm hwa), hpa, hpw] at h
    omega
  rcases L.of_ne hpfix with ⟨-, hpT0⟩ | ⟨h0', -⟩
  swap
  · omega
  have hbb : M 2 (σ a) (σ a) = 0 := by rw [L.T_σσ, h0]
  have hp'p' : M 2 (σ p) (σ p) = 1 := by rw [L.T_σσ, hpp]
  have hpb : p ≠ σ a := fun h => by rw [h, hbb] at hpp; exact zero_ne_one hpp
  have hp'a : σ p ≠ a := fun h => by rw [h, h0] at hp'p'; exact zero_ne_one hp'p'
  have hp'b : σ p ≠ σ a := fun h => by rw [h, hbb] at hp'p'; exact zero_ne_one hp'p'
  have hwp' : w ≠ σ p := fun h => hpw' (by rw [← L.invol p, ← h, hwfix])
  have hpp' : p ≠ σ p := fun h => hpfix h.symm
  -- the rows of `M_{1/2}`
  have hQa := eq_ite_of_forall (g := M 1 a) (P := fun z => z = p) (fun z hz => hz ▸ hap) ha0Q
  have hQp := eq_ite_of_forall (g := M 1 p) (P := fun z => z = a ∨ z = w)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by push Not at hz; exact hp0 z hz.1 hz.2)
  have hQp' : ∀ z, M 1 (σ p) z = if z = σ a ∨ z = w then 1 else 0 := fun z => by
    rw [L.Q_σ, hQp]
    have e1 : (σ z = a) ↔ (z = σ a) := ⟨fun h => by rw [← h, L.invol], fun h => by
      rw [h, L.invol]⟩
    have e2 : (σ z = w) ↔ (z = w) := ⟨fun h => by rw [← L.invol z, h, hwfix], fun h => by
      rw [h, hwfix]⟩
    simp only [e1, e2]
  have hQb : ∀ z, M 1 (σ a) z = if z = σ p then 1 else 0 := fun z => by
    rw [L.Q_σ, hQa]
    have e : (σ z = p) ↔ (z = σ p) := ⟨fun h => by rw [← h, L.invol], fun h => by
      rw [h, L.invol]⟩
    simp only [e]
  have hQw : ∀ z, M 1 w z = if z = p ∨ z = σ p then 1 else 0 := by
    have hwp : M 1 w p = 1 := by rw [L.Q_symm]; exact hpw
    have hwp2 : M 1 w (σ p) = 1 := by rw [L.Q_symm, hQp']; simp
    refine eq_ite_of_forall (fun z hz => by rcases hz with rfl | rfl <;> assumption)
      fun z hz => ?_
    push Not at hz
    have h := L.Q_row w
    rw [hww] at h
    exact mul_self_eq_zero.mp (eq_zero_of_sum_le_pair (f := fun z => M 1 w z * M 1 w z) hpp'
      (by simp only [hwp, hwp2, h]; omega) hz.1 hz.2)
  -- the rows of `M_1`
  have hTa := eq_ite_of_forall (g := M 2 a) (P := fun z => z = w) (fun z hz => hz ▸ haw) ha0
  have hTb : ∀ z, M 2 (σ a) z = if z = w then 1 else 0 := fun z => by rw [L.T_σ, hTa]
  have hTw : ∀ z, M 2 w z = if z = a ∨ z = w ∨ z = σ a then 1 else 0 :=
    eq_ite_of_forall
      (fun z hz => by
        rcases hz with rfl | rfl | rfl
        · rw [L.T_symm]; exact haw
        · exact hww
        · rw [L.T_symm, hTb]; simp)
      (fun z hz => by push Not at hz; exact hw0 z hz.1 hz.2.2 hz.2.1)
  have hTp : ∀ z, M 2 p z = if z = p ∨ z = σ p then 1 else 0 :=
    eq_ite_of_forall
      (fun z hz => by
        rcases hz with rfl | rfl
        · exact hpp
        · rw [L.T_symm, L.T_σ, hpp])
      (fun z hz => by push Not at hz; exact hpT0 z hz.1 hz.2)
  have hTp' : ∀ z, M 2 (σ p) z = if z = p ∨ z = σ p then 1 else 0 := fun z => by
    rw [L.T_σ, hTp]
  refine ⟨![a, p, w, σ p, σ a], L.isNIMRepSummand (π := su24Reflect) rfl
    su24Fusion_four_apply su24Fusion_three_apply
    (injective_vecCons_five (Ne.symm hpa') (Ne.symm hwa) (Ne.symm hp'a) hab hpw' hpp' hpb hwp'
      hwb hp'b)
    (fun i => by fin_cases i <;> simp [su24Reflect, hwfix, L.invol]) (fun i z hz => ?_)
    (fun i z hz => ?_) (fun i j => ?_) (fun i j => ?_), 0, rfl⟩
  · have hz0 : z ≠ a := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ p := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ w := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ σ p := by simpa using ne_of_notMem_range hz 3
    have hz4 : z ≠ σ a := by simpa using ne_of_notMem_range hz 4
    fin_cases i <;> simp [hQa, hQp, hQw, hQp', hQb, hz0, hz1, hz2, hz3, hz4]
  · have hz0 : z ≠ a := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ p := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ w := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ σ p := by simpa using ne_of_notMem_range hz 3
    have hz4 : z ≠ σ a := by simpa using ne_of_notMem_range hz 4
    fin_cases i <;> simp [hTa, hTp, hTw, hTp', hTb, hz0, hz1, hz2, hz3, hz4]
  · fin_cases i <;> fin_cases j <;>
      simp [su24Fusion, hQa, hQp, hQw, hQp', hQb, hpa', hwa, hp'a, hab, hpw', hpp', hpb, hwp',
        hwb, hp'b, Ne.symm hpa', Ne.symm hwa, Ne.symm hp'a, Ne.symm hab, Ne.symm hpw',
        Ne.symm hpp', Ne.symm hpb, Ne.symm hwp', Ne.symm hwb, Ne.symm hp'b]
  · fin_cases i <;> fin_cases j <;>
      simp [su24Fusion, hTa, hTp, hTw, hTp', hTb, hpa', hwa, hp'a, hab, hpw', hpp', hpb, hwp',
        hwb, hp'b, Ne.symm hpa', Ne.symm hwa, Ne.symm hp'a, Ne.symm hab, Ne.symm hpw',
        Ne.symm hpp', Ne.symm hpb, Ne.symm hwp', Ne.symm hwb, Ne.symm hp'b]

/-- A block fixed by the involution `σ` of `2` lies in a summand isomorphic to the regular
representation or to `𝓜_TY`. If `M_1` is `1` on its diagonal, the block is the middle block `1`
of a regular summand built around a corner. -/
theorem summand_of_fixed {x : κ} (hx : σ x = x) :
    (∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f) := by
  rcases L.of_eq hx with ⟨h2, -⟩ | ⟨-, w, hw, hxw⟩ | ⟨h0, -⟩
  · exact Or.inr (L.summand_of_two h2)
  · have hwx : M 2 w x ≠ 0 := by rwa [L.T_symm]
    rcases L.of_ne hw with ⟨-, hw0⟩ | ⟨h0, -⟩
    · have hxw' : x ≠ w := fun h => hw (by rw [← h]; exact hx)
      have hxσ : x ≠ σ w := fun h => by
        rw [h, L.invol] at hx
        exact hw hx.symm
      exact absurd (hw0 x hxw' hxσ) hwx
    · obtain ⟨f, hf, i, rfl⟩ := L.summand_of_corner hw h0
      exact Or.inl ⟨f, hf, hf.mem_range hwx⟩
  · exact Or.inr (L.summand_of_fixed_zero hx h0)

/-- Every block lies in a summand isomorphic to the regular representation or to `𝓜_TY`. A block
`x` moved by `σ` with `M_1` equal to `1` on its diagonal (the block `1/2` or `3/2` of a regular
summand) has a neighbour under `1/2` fixed by `σ`: by `1/2 × 1/2 = 0 + 1`,
`∑_z (M_{1/2})_{xz} (M_{1/2})_{x,σz} = (M_1)_{x,σx} = 1`, and a neighbour `z ≠ σz` would
contribute the two terms at `z` and `σz`. -/
theorem summand (x : κ) :
    (∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f) := by
  by_cases hx : σ x = x
  · exact L.summand_of_fixed hx
  rcases L.of_ne hx with ⟨h1, -⟩ | ⟨h0, -⟩
  swap
  · exact Or.inl (L.summand_of_corner hx h0)
  have hsum : ∑ z, M 1 x z * M 1 x (σ z) = 1 := by
    have h := L.Q_off x (σ x) fun h => hx h.symm
    rw [L.T_symm, L.T_σ, h1] at h
    rw [← h]
    exact Finset.sum_congr rfl fun z _ =>
      congrArg (M 1 x z * ·) ((L.Q_symm x (σ z)).trans (L.Q_σ z x))
  obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => M 1 x z * M 1 x (σ z)) (by omega)
  have hzx : M 1 z x ≠ 0 := by
    rw [L.Q_symm]
    exact fun h => hz (by simp [h])
  by_cases hzf : σ z = z
  · rcases L.summand_of_fixed hzf with ⟨f, hf, i, rfl⟩ | ⟨f, hf, i, rfl⟩
    · exact Or.inl ⟨f, hf, hf.mem_range hzx⟩
    · exact Or.inr ⟨f, hf, hf.mem_range hzx⟩
  · have h := sum_pair_le (f := fun z => M 1 x z * M 1 x (σ z)) (Ne.symm hzf)
    simp only [L.invol, hsum] at h
    have hz' : M 1 x z * M 1 x (σ z) ≠ 0 := hz
    rw [mul_comm (M 1 x (σ z))] at h
    omega

end SU24Local

/-- **Classification of the dual representations of `su(2)₄`** (arXiv:2203.12563,
lines 1906–1925: "there are only two different phases associated to this MPO algebra"). In a
nonnegative integer representation of `su(2)₄` on any finite set of blocks, with the unit acting
trivially and every label acting by a symmetric matrix (the duality of a module category, all
labels being self-dual), every block lies in a direct summand isomorphic to the regular phase
(five blocks) or to the phase `𝓜_TY` (four blocks). -/
theorem exists_isNIMRepSummand_su24 (hM : IsNIMRep su24Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) (x : κ) :
    (∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f) := by
  obtain ⟨σ, L⟩ := su24_exists_local hM hunit hdual
  exact L.summand x

/-- **The indecomposable dual representations of `su(2)₄` are the two printed phases**
(arXiv:2203.12563, lines 1906–1925). A nonempty dual representation with trivial unit on which
`1/2` acts indecomposably is, up to relabelling the blocks, the regular phase or `𝓜_TY`. -/
theorem exists_equiv_of_isIndecomposable_su24 [Nonempty κ] (hM : IsNIMRep su24Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id)
    (hind : Matrix.IsIndecomposable (M 1)) :
    (∃ e : κ ≃ Fin 5, ∀ a x y, M a x y = su24Fusion a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 4, ∀ a x y, M a x y = su24TY a (e x) (e y)) := by
  obtain ⟨x⟩ := ‹Nonempty κ›
  rcases exists_isNIMRepSummand_su24 hM hunit hdual x with ⟨f, hf, -⟩ | ⟨f, hf, -⟩
  · exact Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))
  · exact Or.inr (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))

end SU24

/-! ### A representation that is not dual -/

/-- **A two-block representation of `Rep(S₃)` that is not dual**: `ψ` fixes both blocks and
`π · x₀ = x₁`, `π · x₁ = 2 x₀ + x₁`. It is recorded in
`docs/paper-gaps/glm23_reps3_su24_module_list.tex` as the reason the duality hypothesis of the
classification cannot be dropped. -/
def repS3NonDual : Fin 3 → Matrix (Fin 2) (Fin 2) ℕ
  | 0 => 1
  | 1 => !![0, 1; 2, 1]
  | 2 => 1

/-- The representation `MPOTensor.repS3NonDual` satisfies the relation of arXiv:2203.12563,
lines 564–565. -/
theorem isNIMRep_repS3NonDual : IsNIMRep repS3Fusion repS3NonDual := by
  unfold IsNIMRep; decide +kernel

/-- The representation `MPOTensor.repS3NonDual` is not dual: `M_π` is not symmetric although `π`
is self-dual. So it is neither the `ℤ₂` phase nor a sum of two `ℤ₁` phases. -/
theorem not_isTransposeDual_repS3NonDual : ¬ IsTransposeDual repS3NonDual id := by
  intro h
  have := h 1 0 1
  simp [repS3NonDual] at this

end MPOTensor
