/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointExtendedBoundary
import TNLean.MPS.Core.InsertedLeftInverse
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Intersection of the actual extended endpoint supports

The extended supports satisfy the open-chain intersection property even
when the inserted matrix is singular. The overlap equation is
`W Aʲ Yᵢ = Zⱼ Aⁱ W`. A matrix-valued left inverse of the family `W Aʲ`
recovers a single full boundary matrix. Thus the free outer bond indices
survive at both endpoints, in contrast to the canonical padded-endpoint
boundary space.

Source: arXiv:2203.12563, Section 5, lines 1690–1692; the grow-back method
is arXiv:2011.12127, Section IV.C, lines 2013–2078.
-/

open scoped Matrix BigOperators

namespace MPSTensor
namespace MPOSymmetry

variable {d D : ℕ}

/-- The coefficient-space extended support with free left and right
boundary indices. Source: arXiv:2203.12563, Section 5, line 1690. -/
noncomputable def insertedGroundSpace
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  (insertedGroundSpaceMap A W N).range

/-- Fixing the last physical letter retains an extended boundary vector,
with boundary `W Aʲ X`. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem insertedGroundSpaceMap_restrictLast
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {L : ℕ} (hL : 0 < L) (X : Matrix (Fin D) (Fin D) ℂ) (j : Fin d) :
    restrictLast (insertedGroundSpaceMap A W (L + 1) X) j =
      insertedGroundSpaceMap A W L (W * A j * X) := by
  ext σ
  exact insertedGroundSpaceMap_snoc A W hL X σ j

/-- Fixing the first physical letter retains an extended boundary vector,
with boundary `X Aⁱ W`. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem insertedGroundSpaceMap_restrictFirst
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {L : ℕ} (hL : 0 < L) (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    restrictFirst (insertedGroundSpaceMap A W (L + 1) X) i =
      insertedGroundSpaceMap A W L (X * A i * W) := by
  ext σ
  exact insertedGroundSpaceMap_cons A W hL X i σ

/-- Matching the left and right restrictions gives the actual inserted
boundary compatibility equation on their common interior.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem insertedGroundSpaceMap_mul_eq_of_restrict
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {K : ℕ} (hK : 0 < K)
    {ψ : NSiteSpace d (K + 2)} {Y Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hY : ∀ i, restrictFirst ψ i = insertedGroundSpaceMap A W (K + 1) (Y i))
    (hZ : ∀ j, restrictLast ψ j = insertedGroundSpaceMap A W (K + 1) (Z j))
    (i j : Fin d) :
    insertedGroundSpaceMap A W K (W * A j * Y i) =
      insertedGroundSpaceMap A W K (Z j * A i * W) := by
  rw [← insertedGroundSpaceMap_restrictLast A W hK, ← hY i,
    ← insertedGroundSpaceMap_restrictFirst A W hK, ← hZ j]
  ext σ
  simp only [restrictLast_apply, restrictFirst_apply, Fin.cons_snoc_eq_snoc_cons]

/-- A compatible pair of inserted boundary families grows back to one full
boundary matrix. The matrix-valued cancellation uses the letters `W Aʲ`
and does not require `W` to be invertible.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mem_insertedGroundSpace_succ_of_intertwine
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    {K : ℕ} (hK : 0 < K)
    {ψ : NSiteSpace d (K + 1)} {Y Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (R : Fin d → Matrix (Fin D) (Fin D) ℂ) (hR : ∑ j, R j * W * A j = 1)
    (hY : ∀ i, restrictFirst ψ i = insertedGroundSpaceMap A W K (Y i))
    (hCompat : ∀ i j, W * A j * Y i = Z j * A i * W) :
    ψ ∈ insertedGroundSpace A W (K + 1) := by
  let X : Matrix (Fin D) (Fin D) ℂ := ∑ j, R j * Z j
  have hYeq (i : Fin d) : Y i = X * A i * W := by
    calc
      Y i = (∑ j, R j * W * A j) * Y i := by rw [hR, Matrix.one_mul]
      _ = ∑ j, R j * (Z j * A i * W) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simpa only [Matrix.mul_assoc] using
          congrArg (fun M => R j * M) (hCompat i j)
      _ = X * A i * W := by simp only [X, Finset.sum_mul, Matrix.mul_assoc]
  refine ⟨X, ?_⟩
  apply eq_of_forall_restrictFirst_eq
  intro i
  rw [insertedGroundSpaceMap_restrictFirst A W hK, hY i, hYeq i]

/-- Exact intersection of the extended supports at every positive insertion,
including singular endpoint insertions. Only injectivity of the unweighted
tensor and nonvanishing of the insertion are required.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem insertedGroundSpace_intersection
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0)
    {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)}
    (hLeft : ∀ j, restrictLast ψ j ∈ insertedGroundSpace A W L)
    (hRight : ∀ i, restrictFirst ψ i ∈ insertedGroundSpace A W L) :
    ψ ∈ insertedGroundSpace A W (L + 1) := by
  classical
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
  have hK : 0 < K := by omega
  choose Y hY using fun i => LinearMap.mem_range.mp (hRight i)
  choose Z hZ using fun j => LinearMap.mem_range.mp (hLeft j)
  obtain ⟨R, hR⟩ := exists_leftInverse_insertedLetters A hA W hW
  apply mem_insertedGroundSpace_succ_of_intertwine A W (Z := Z) (by omega) R hR
    (fun i => (hY i).symm)
  intro i j
  apply insertedGroundSpaceMap_injective A hA W hW hK
  exact insertedGroundSpaceMap_mul_eq_of_restrict A W hK
    (fun i => (hY i).symm) (fun j => (hZ j).symm) i j

/-- A vector belongs to the longer extended support exactly when its left
and right restrictions belong to the shorter extended supports.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem insertedGroundSpace_iff_left_right
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0)
    {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)} :
    ψ ∈ insertedGroundSpace A W (L + 1) ↔
      (∀ j, restrictLast ψ j ∈ insertedGroundSpace A W L) ∧
      (∀ i, restrictFirst ψ i ∈ insertedGroundSpace A W L) := by
  constructor
  · rintro ⟨X, rfl⟩
    constructor
    · intro j
      rw [insertedGroundSpaceMap_restrictLast A W (by omega)]
      exact ⟨_, rfl⟩
    · intro i
      rw [insertedGroundSpaceMap_restrictFirst A W (by omega)]
      exact ⟨_, rfl⟩
  · rintro ⟨hLeft, hRight⟩
    exact insertedGroundSpace_intersection A hA W hW hL hLeft hRight

end MPOSymmetry
end MPSTensor
