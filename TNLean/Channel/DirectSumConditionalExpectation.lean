/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumKraus
import TNLean.Channel.RightFactorConditionalExpectation

/-!
# Coordinate direct-sum conditional expectation

This file constructs, in the coordinates of the finite-dimensional star-algebra
classification, the trace-preserving conditional expectation onto
\[
  \bigoplus_k \bigl(\mathbf 1_{m_k} \otimes M_{d_k}(\mathbb C)\bigr).
\]
For a matrix `A` on the direct sum, its value is
\[
  \operatorname{blockDiagonal}'\!\left(k \mapsto
    \mathbf 1_{m_k} \otimes
      \bigl(m_k^{-1}\operatorname{tr}_{m_k}(A_{kk})\bigr)\right),
\]
where `Aₖₖ` is the `k`-th diagonal compression. Complete positivity is obtained
by applying the one-block right-factor expectation in every coordinate and then
using the existing direct-sum Kraus extension; no new Kraus family is introduced.

This is the coordinate direct-sum retraction used in Wolf's operator-system
extension argument. Arbitrary unitary change of coordinates and codomain
corestriction are not part of this construction.

## Main definitions

* `Matrix.coordinateRightFactorStarAlgHom`: the coordinate embedding of the
  direct sum of right matrix factors.
* `Matrix.coordinateRightFactorStarSubalgebra`: its range.
* `Matrix.coordinateDirectSumConditionalExpectation`: the normalized
  coordinate direct-sum expectation.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5,
  Equation (1.40), and the operator-system extension theorem; local source
  `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 536--570
  and 616--626.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker BigOperators
open Matrix

noncomputable section

namespace Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m d : κ → ℕ}

/-- The coordinate star-algebra embedding
`(Bₖ)ₖ ↦ blockDiagonal' (k ↦ 1_{mₖ} ⊗ Bₖ)`. -/
noncomputable def coordinateRightFactorStarAlgHom :
    (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) →⋆ₐ[ℂ]
      Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
        ((k : κ) × (Fin (m k) × Fin (d k))) ℂ where
  toFun B := directSumDiagonalEmbedding fun k ↦
    rightKroneckerEmbed (m := Fin (m k)) (B k)
  map_one' := by
    change Matrix.blockDiagonal' _ = 1
    rw [← Matrix.blockDiagonal'_one]
    congr 1
    funext k
    exact map_one (rightKroneckerEmbed (m := Fin (m k)) (n := Fin (d k)))
  map_mul' A B := by
    rw [← directSumDiagonalEmbedding_mul]
    congr 1
    funext k
    exact map_mul (rightKroneckerEmbed (m := Fin (m k)) (n := Fin (d k))) (A k) (B k)
  map_zero' := by
    change Matrix.blockDiagonal' _ = 0
    rw [← Matrix.blockDiagonal'_zero]
    congr 1
    funext k
    exact map_zero (rightKroneckerEmbed (m := Fin (m k)) (n := Fin (d k)))
  map_add' A B := by
    rw [← Matrix.blockDiagonal'_add]
    congr 1
    funext k
    exact map_add (rightKroneckerEmbed (m := Fin (m k)) (n := Fin (d k))) (A k) (B k)
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change directSumDiagonalEmbedding _ = r • (1 : Matrix _ _ ℂ)
    rw [← Matrix.blockDiagonal'_smul, ← Matrix.blockDiagonal'_one]
    congr 1
    funext k
    exact map_smul (rightKroneckerEmbed (m := Fin (m k)) (n := Fin (d k))) r 1
  map_star' A := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose,
      ← directSumDiagonalEmbedding_conjTranspose]
    congr 1
    funext k
    exact map_star (rightKroneckerEmbed (m := Fin (m k)) (n := Fin (d k))) (A k)

@[simp]
theorem coordinateRightFactorStarAlgHom_apply
    (B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    coordinateRightFactorStarAlgHom (m := m) B =
      Matrix.blockDiagonal' fun k ↦
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k :=
  rfl

/-- The coordinate star subalgebra
`⊕ k, (1_{mₖ} ⊗ M_{dₖ}(ℂ))`. -/
def coordinateRightFactorStarSubalgebra :
    StarSubalgebra ℂ
      (Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
        ((k : κ) × (Fin (m k) × Fin (d k))) ℂ) :=
  StarAlgHom.range (coordinateRightFactorStarAlgHom (m := m) (d := d))

/-- Exact membership in the coordinate right-factor star subalgebra. -/
theorem mem_coordinateRightFactorStarSubalgebra
    (A : Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
      ((k : κ) × (Fin (m k) × Fin (d k))) ℂ) :
    A ∈ coordinateRightFactorStarSubalgebra (m := m) (d := d) ↔
      ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        A = Matrix.blockDiagonal' fun k ↦
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, hB.symm⟩
  · rintro ⟨B, rfl⟩
    exact ⟨B, rfl⟩

/-- The coordinate direct-sum conditional expectation obtained by applying the
normalized right-factor expectation separately to every diagonal block. -/
noncomputable def coordinateDirectSumConditionalExpectation :
    Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
        ((k : κ) × (Fin (m k) × Fin (d k))) ℂ →ₗ[ℂ]
      Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
        ((k : κ) × (Fin (m k) × Fin (d k))) ℂ :=
  directSumExtension (LinearMap.piMap fun k ↦
    rightFactorConditionalExpectation (m := m k) (d := d k))

/-- Explicit evaluation formula for the coordinate direct-sum expectation. -/
@[simp]
theorem coordinateDirectSumConditionalExpectation_apply
    (A : Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
      ((k : κ) × (Fin (m k) × Fin (d k))) ℂ) :
    coordinateDirectSumConditionalExpectation (m := m) (d := d) A =
      Matrix.blockDiagonal' fun k ↦
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
          (((m k : ℂ)⁻¹) • partialTraceLeft
            (directSumDiagonalCompression A k)) := by
  rw [coordinateDirectSumConditionalExpectation, directSumExtension_apply]
  congr 1
  funext k
  exact rightFactorConditionalExpectation_apply _

/-- Every off-diagonal block of the coordinate direct-sum expectation vanishes. -/
theorem coordinateDirectSumConditionalExpectation_offDiagonal
    (A : Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
      ((k : κ) × (Fin (m k) × Fin (d k))) ℂ)
    {k l : κ} (hkl : k ≠ l) (i : Fin (m k) × Fin (d k))
    (j : Fin (m l) × Fin (d l)) :
    coordinateDirectSumConditionalExpectation (m := m) (d := d) A ⟨k, i⟩ ⟨l, j⟩ = 0 := by
  rw [coordinateDirectSumConditionalExpectation_apply,
    Matrix.blockDiagonal'_apply_ne _ _ _ hkl]

/-- Positivity and trace preservation of the coordinate direct-sum expectation. -/
theorem coordinateDirectSumConditionalExpectation_isKrausCPTP
    (hm : ∀ k, 0 < m k) :
    IsKrausCPTP (coordinateDirectSumConditionalExpectation (m := m) (d := d)) := by
  letI (k : κ) : NeZero (m k) := ⟨Nat.ne_of_gt (hm k)⟩
  apply isKrausCPTP_of_isKrausCP_trace_preserving
  · change IsKrausCP (directSumExtension (LinearMap.piMap fun k ↦
      rightFactorConditionalExpectation (m := m k) (d := d k)))
    rw [← directSumMapExtension_self]
    exact isKrausDirectSumMap_piMap _ fun k ↦
      rightFactorConditionalExpectation_isKrausCP
  · intro A
    apply (IsTracePreservingDirectSumMap.directSumExtension_isTracePreservingMap
      (T := LinearMap.piMap fun k ↦
        rightFactorConditionalExpectation (m := m k) (d := d k)) ?_) A
    intro B
    apply Finset.sum_congr rfl
    intro k _
    exact rightFactorConditionalExpectation_isKrausCPTP.trace_map (B k)

/-- The coordinate direct-sum expectation takes values in the coordinate
right-factor star subalgebra. -/
theorem coordinateDirectSumConditionalExpectation_range_subset
    (A : Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
      ((k : κ) × (Fin (m k) × Fin (d k))) ℂ) :
    coordinateDirectSumConditionalExpectation (m := m) (d := d) A ∈
      coordinateRightFactorStarSubalgebra (m := m) (d := d) := by
  rw [mem_coordinateRightFactorStarSubalgebra,
    coordinateDirectSumConditionalExpectation_apply]
  exact ⟨fun k ↦ ((m k : ℂ)⁻¹) • partialTraceLeft
    (directSumDiagonalCompression A k), rfl⟩

/-- The coordinate direct-sum expectation fixes its target star subalgebra
pointwise. -/
theorem coordinateDirectSumConditionalExpectation_fixes
    (hm : ∀ k, 0 < m k)
    (B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    coordinateDirectSumConditionalExpectation (m := m) (d := d)
        (coordinateRightFactorStarAlgHom (m := m) B) =
      coordinateRightFactorStarAlgHom (m := m) B := by
  letI (k : κ) : NeZero (m k) := ⟨Nat.ne_of_gt (hm k)⟩
  apply (directSumExtension_embedding_eq_self_iff _ _).2
  funext k
  exact rightFactorConditionalExpectation_fixes (B k)

/-- The coordinate direct-sum expectation is idempotent. -/
theorem coordinateDirectSumConditionalExpectation_idempotent
    (hm : ∀ k, 0 < m k)
    (A : Matrix ((k : κ) × (Fin (m k) × Fin (d k)))
      ((k : κ) × (Fin (m k) × Fin (d k))) ℂ) :
    coordinateDirectSumConditionalExpectation (m := m) (d := d)
        (coordinateDirectSumConditionalExpectation (m := m) (d := d) A) =
      coordinateDirectSumConditionalExpectation (m := m) (d := d) A := by
  rw [coordinateDirectSumConditionalExpectation_apply A]
  exact coordinateDirectSumConditionalExpectation_fixes hm _

/-- The coordinate direct-sum expectation is unital. -/
theorem coordinateDirectSumConditionalExpectation_unital
    (hm : ∀ k, 0 < m k) :
    coordinateDirectSumConditionalExpectation (m := m) (d := d) 1 = 1 := by
  rw [← map_one (coordinateRightFactorStarAlgHom (m := m) (d := d))]
  exact coordinateDirectSumConditionalExpectation_fixes hm 1

/-- The coordinate normalized partial trace is a conditional expectation onto
`⊕ k, (1_{mₖ} ⊗ M_{dₖ}(ℂ))`. -/
theorem coordinateDirectSumConditionalExpectation_isConditionalExpectation
    (hm : ∀ k, 0 < m k) :
    Kraus.IsConditionalExpectation
      (coordinateDirectSumConditionalExpectation (m := m) (d := d))
      (coordinateRightFactorStarSubalgebra (m := m) (d := d)) where
  positive :=
    (isKrausCP_iff_isCPMap.mp
      (coordinateDirectSumConditionalExpectation_isKrausCPTP hm).isKrausCP).isPositiveMap
  idempotent := coordinateDirectSumConditionalExpectation_idempotent hm
  unital := coordinateDirectSumConditionalExpectation_unital hm
  range_subset := coordinateDirectSumConditionalExpectation_range_subset
  fixes A hA := by
    rw [mem_coordinateRightFactorStarSubalgebra] at hA
    obtain ⟨B, rfl⟩ := hA
    exact coordinateDirectSumConditionalExpectation_fixes hm B

/-- The coordinate direct-sum map is simultaneously CPTP and a conditional
expectation onto `⊕ k, (1_{mₖ} ⊗ M_{dₖ}(ℂ))`. -/
theorem coordinateDirectSumConditionalExpectation_isKrausCPTP_and_isConditionalExpectation
    (hm : ∀ k, 0 < m k) :
    IsKrausCPTP (coordinateDirectSumConditionalExpectation (m := m) (d := d)) ∧
      Kraus.IsConditionalExpectation
        (coordinateDirectSumConditionalExpectation (m := m) (d := d))
        (coordinateRightFactorStarSubalgebra (m := m) (d := d)) :=
  ⟨coordinateDirectSumConditionalExpectation_isKrausCPTP hm,
    coordinateDirectSumConditionalExpectation_isConditionalExpectation hm⟩

end Matrix
