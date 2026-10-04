/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Card

/-!
# Cut rows with coefficients in a finite alphabet

A rank-`r` matrix whose entries lie in a finite set `S` of scalars has at most
`S.card ^ r` distinct rows. Choose `r` columns spanning its column space;
restriction to these columns distinguishes its rows.

For a permutation MPU, every coefficient is zero or one. Factoring a cut
matrix through a bond of dimension `D` therefore bounds the number of
residual coefficient functions by `2 ^ D`, independently of the smallest
Schmidt coefficient. This is the finite-state description used in
`docs/audits/2026-10-02_mpu_finite_alphabet_circuits.tex` to construct
circuits for permutation and finite-phase monomial MPUs.

This module proves the row-count estimates. The finite-state transitions,
output recovery, and reversible quantum circuits are not formalized here.
Source context: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
the general circuit question at lines 684--690 and the nonuniform
conditioning theorem at lines 1373--1402. The finite-alphabet argument is
an additional construction, rather than a formalization of that theorem.
-/

open Function Module Submodule

namespace Matrix

variable {K m n : Type*} [Field K]

/-- A basis of the column space selects exactly `rank` columns distinguishing all rows. -/
theorem exists_row_separating_columns [Fintype n] (M : Matrix m n K) :
    ∃ s : Finset n, s.card = M.rank ∧
      ∀ i i', (∀ j ∈ s, M i j = M i' j) → M i = M i' := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K M.col
  have : Finite κ := Finite.of_injective a ha
  let := Fintype.ofFinite κ
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ,
      rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  · intro i i' hij
    ext j
    have hmem : M.col j ∈ span K (Set.range (M.col ∘ a)) :=
      hspan.symm ▸ subset_span ⟨j, rfl⟩
    refine span_induction (p := fun x _ => x i = x i') ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨k, rfl⟩
      exact hij (a k) (Finset.mem_image_of_mem a (Finset.mem_univ k))
    · rfl
    · exact fun x y _ _ hx hy => congrArg₂ (· + ·) hx hy
    · exact fun c x _ hx => congrArg (c * ·) hx

/-- If every entry of `M` lies in the finite set `S`, then `M` has finitely many distinct rows,
and at most `S.card ^ M.rank` of them. -/
theorem card_range_le_pow_rank [Fintype n] (M : Matrix m n K) (S : Finset K)
    (hM : ∀ i j, M i j ∈ S) : (Set.range M).Finite ∧ Nat.card (Set.range M) ≤ S.card ^ M.rank := by
  classical
  obtain ⟨s, hs, hsep⟩ := M.exists_row_separating_columns
  have hvalues : ∀ v ∈ Set.range M, ∀ j, v j ∈ S :=
    Set.forall_mem_range.mpr hM
  let f : Set.range M → (s → S) :=
    fun v j => ⟨v.val j.val, hvalues v.val v.property j.val⟩
  have hf : Injective f := by
    rintro ⟨_, i, rfl⟩ ⟨_, i', rfl⟩ h
    apply Subtype.ext
    exact hsep i i' fun j hj => congrArg Subtype.val (congrFun h ⟨j, hj⟩)
  have hcard := Nat.card_le_card_of_injective f hf
  refine ⟨Set.finite_coe_iff.mpr (Finite.of_injective f hf), ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, hs] using hcard

/-- A nonempty alphabet and a rank bound give a bound on the number of distinct rows. -/
theorem card_range_le_pow_of_rank_le [Fintype n] (M : Matrix m n K) (S : Finset K)
    (hS : S.Nonempty) (hM : ∀ i j, M i j ∈ S) (D : ℕ) (hD : M.rank ≤ D) :
    (Set.range M).Finite ∧ Nat.card (Set.range M) ≤ S.card ^ D := by
  exact ⟨(M.card_range_le_pow_rank S hM).1,
    (M.card_range_le_pow_rank S hM).2.trans
      (pow_le_pow_right' (Finset.one_le_card.mpr hS) hD)⟩

/-- A factorization through a finite bond bounds the number of finite-alphabet cut rows. -/
theorem card_range_mul_le_pow [Finite n] (b : Type*) [Fintype b] (A : Matrix m b K)
    (B : Matrix b n K) (S : Finset K) (hS : S.Nonempty)
    (hM : ∀ i j, (A * B) i j ∈ S) :
    (Set.range (A * B)).Finite ∧
      Nat.card (Set.range (A * B)) ≤ S.card ^ Fintype.card b := by
  let := Fintype.ofFinite n
  exact (A * B).card_range_le_pow_of_rank_le S hS hM _
    ((rank_mul_le_left A B).trans A.rank_le_card_width)

/-- Zero-one cut coefficients give at most `2 ^ D` residual rows for a bond of dimension `D`. -/
theorem card_range_mul_le_two_pow [Finite n] (b : Type*) [Fintype b]
    (A : Matrix m b K) (B : Matrix b n K)
    (hM : ∀ i j, (A * B) i j = 0 ∨ (A * B) i j = 1) :
    (Set.range (A * B)).Finite ∧
      Nat.card (Set.range (A * B)) ≤ 2 ^ Fintype.card b := by
  classical
  simpa using card_range_mul_le_pow b A B {0, 1} (by simp) (by simpa using hM)

end Matrix
