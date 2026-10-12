/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointInsertedBoundary
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRestriction

/-!
# Intersection of joint inserted supports

Equality of the two overlapping restrictions is compared by the joint
boundary map. Its injectivity separates all block boundaries simultaneously.
A matrix-valued left inverse for each family of inserted letters then
recovers one tuple of boundaries for the longer chain. No exact physical
orthogonality, inverse of an insertion, or assembled full-algebra injectivity
is required.

Source: arXiv:2203.12563, Section 5, lines 1695–1777, extending the
one-block restriction argument at lines 1690–1692 to the common block labels.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The joint extended coefficient support, with one matrix boundary per block.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def blockInsertedGroundSpace
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  (blockInsertedGroundSpaceMap A W N).range

/-- The two restrictions agree on their common interior in joint boundary coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpaceMap_mul_eq_of_restrict
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    {K : ℕ} (hK : 0 < K) {ψ : NSiteSpace d (K + 2)}
    {Y Z : Fin d → (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ}
    (hY : ∀ i, restrictFirst ψ i = blockInsertedGroundSpaceMap A W (K + 1) (Y i))
    (hZ : ∀ j, restrictLast ψ j = blockInsertedGroundSpaceMap A W (K + 1) (Z j))
    (i j : Fin d) :
    blockInsertedGroundSpaceMap A W K (fun x => W x * A x j * Y i x) =
      blockInsertedGroundSpaceMap A W K (fun x => Z j x * A x i * W x) := by
  rw [← blockInsertedGroundSpaceMap_restrictLast A W (Y i) hK,
    ← hY i, ← blockInsertedGroundSpaceMap_restrictFirst A W (Z j) hK, ← hZ j]
  ext σ
  simp only [restrictLast_apply, restrictFirst_apply, Fin.cons_snoc_eq_snoc_cons]

/-- Compatible joint boundary families recover one tuple of outer boundary matrices.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem mem_blockInsertedGroundSpace_succ_of_intertwine
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    {K : ℕ} (hK : 0 < K) {ψ : NSiteSpace d (K + 1)}
    {Y Z : Fin d → (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ}
    (R : (x : Fin r) → Fin d → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hR : ∀ x, ∑ j, R x j * W x * A x j = 1)
    (hY : ∀ i, restrictFirst ψ i = blockInsertedGroundSpaceMap A W K (Y i))
    (hCompat : ∀ i j x, W x * A x j * Y i x = Z j x * A x i * W x) :
    ψ ∈ blockInsertedGroundSpace A W (K + 1) := by
  let X : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ :=
    fun x => ∑ j, R x j * Z j x
  have hYeq (i : Fin d) : Y i = fun x => X x * A x i * W x := by
    funext x
    calc
      Y i x = (∑ j, R x j * W x * A x j) * Y i x := by
        rw [hR x, Matrix.one_mul]
      _ = ∑ j, R x j * (Z j x * A x i * W x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simpa only [Matrix.mul_assoc] using
          congrArg (fun M => R x j * M) (hCompat i j x)
      _ = X x * A x i * W x := by
        simp only [X, Finset.sum_mul, Matrix.mul_assoc]
  refine ⟨X, ?_⟩
  apply eq_of_forall_restrictFirst_eq
  intro i
  rw [blockInsertedGroundSpaceMap_restrictFirst A W X hK, hY i, hYeq i]

/-- Joint inserted supports have the restriction intersection property.
The overlap comparison uses simultaneous injectivity, not a per-block
comparison of physical spaces. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpace_intersection
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)}
    (hLeft : ∀ j, restrictLast ψ j ∈ blockInsertedGroundSpace A W L)
    (hRight : ∀ i, restrictFirst ψ i ∈ blockInsertedGroundSpace A W L) :
    ψ ∈ blockInsertedGroundSpace A W (L + 1) := by
  classical
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
  have hK : 0 < K := by omega
  choose Y hY using fun i => LinearMap.mem_range.mp (hRight i)
  choose Z hZ using fun j => LinearMap.mem_range.mp (hLeft j)
  choose R hR using fun x =>
    exists_leftInverse_insertedLetters (A x) (hA.isInjective_one x) (W x) (hW x)
  apply mem_blockInsertedGroundSpace_succ_of_intertwine A W (Z := Z)
    (by omega) R hR (fun i => (hY i).symm)
  intro i j x
  have hEq := blockInsertedGroundSpaceMap_injective A hA W hW hK
    (blockInsertedGroundSpaceMap_mul_eq_of_restrict A W hK
      (fun i => (hY i).symm) (fun j => (hZ j).symm) i j)
  exact congrFun hEq x

/-- The joint extended support is exactly the intersection of its two endpoint
restriction spaces. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpace_iff_left_right
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)} :
    ψ ∈ blockInsertedGroundSpace A W (L + 1) ↔
      (∀ j, restrictLast ψ j ∈ blockInsertedGroundSpace A W L) ∧
      (∀ i, restrictFirst ψ i ∈ blockInsertedGroundSpace A W L) := by
  constructor
  · rintro ⟨X, rfl⟩
    constructor
    · intro j
      rw [blockInsertedGroundSpaceMap_restrictLast A W X (by omega)]
      exact ⟨_, rfl⟩
    · intro i
      rw [blockInsertedGroundSpaceMap_restrictFirst A W X (by omega)]
      exact ⟨_, rfl⟩
  · rintro ⟨hLeft, hRight⟩
    exact blockInsertedGroundSpace_intersection A hA W hW hL hLeft hRight

/-- Positive-length contiguous restrictions preserve joint inserted supports.
This inclusion does not require injectivity or nonvanishing insertions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem contiguousRestrictₗ_blockInsertedGroundSpace_mem
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    {N L : ℕ} (hL : 0 < L) (s : ℕ) (hs : s + L ≤ N)
    (τ : Cfg d N) {ψ : NSiteSpace d N} (hψ : ψ ∈ blockInsertedGroundSpace A W N) :
    contiguousRestrictₗ s L hs τ ψ ∈ blockInsertedGroundSpace A W L := by
  apply contiguousRestrictₗ_mem_of_restriction_closed (blockInsertedGroundSpace A W)
    ?_ ?_ hL s hs τ hψ
  · intro M hM φ hφ j
    obtain ⟨X, rfl⟩ := hφ
    rw [blockInsertedGroundSpaceMap_restrictLast A W X hM]
    exact ⟨_, rfl⟩
  · intro M hM φ hφ i
    obtain ⟨X, rfl⟩ := hφ
    rw [blockInsertedGroundSpaceMap_restrictFirst A W X hM]
    exact ⟨_, rfl⟩

end MPSTensor.MPOSymmetry
