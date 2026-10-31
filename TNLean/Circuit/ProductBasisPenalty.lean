/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.Controlled
import TNLean.Circuit.SiteEmbeddingOrder
import TNLean.Circuit.EntropySupport

/-!
# On-site penalties selecting a prescribed product basis vector

The sum of the actual penalties on all sites has the specified product basis
vector at energy zero and projector gap at least one. The construction also
covers the empty site family, where its orthogonal complement is zero.

Source: algebraic product-ancilla padding of the LVV13 successive construction,
arXiv:1307.5143v1, final induction, lines 652--678. The padding is an auxiliary
reduction, rather than an additional hypothesis on the original interaction.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive on-site penalty vanishing precisely at a prescribed basis level. -/
noncomputable def siteBasisPenalty (a : Fin q) : Matrix (Fin q) (Fin q) ℂ :=
  diagonal fun b ↦ if b = a then 0 else 1

/-- The actual sum of placed on-site penalties selecting the basis configuration `b`. -/
noncomputable def productBasisPenalty (b : ι → Fin q) :
    Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  ∑ v, siteOp v (siteBasisPenalty (b v))

/-- Each on-site penalty is positive. -/
theorem siteBasisPenalty_posSemidef (a : Fin q) : (siteBasisPenalty a).PosSemidef := by
  apply PosSemidef.diagonal
  intro b
  change (0 : ℂ) ≤ if b = a then 0 else 1
  split_ifs <;> norm_num

/-- Each on-site penalty has operator upper bound one. -/
theorem siteBasisPenalty_le_one (a : Fin q) : siteBasisPenalty a ≤ 1 := by
  apply Matrix.le_iff.mpr
  have hid : 1 - siteBasisPenalty a = diagonal (fun b ↦ if b = a then (1 : ℂ) else 0) := by
    ext b c
    by_cases hbc : b = c
    · subst c
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, siteBasisPenalty, diagonal_apply_eq]
      split_ifs <;> norm_num
    · simp [Matrix.sub_apply, siteBasisPenalty, hbc]
  rw [hid]
  apply PosSemidef.diagonal
  intro b
  change (0 : ℂ) ≤ if b = a then 1 else 0
  split_ifs <;> norm_num

/-- The product penalty is the diagonal count of sites differing from the target. -/
theorem productBasisPenalty_eq_diagonal (b : ι → Fin q) :
    productBasisPenalty b = diagonal (fun x ↦ ∑ v, if x v = b v then (0 : ℂ) else 1) := by
  classical
  simp only [productBasisPenalty, siteBasisPenalty, siteOp_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.sum_apply, diagonal_apply_eq]
  · simp [Matrix.sum_apply, hxy]

omit [DecidableEq ι] in
private theorem productBasis_outer (b : ι → Fin q) :
    vecMulVec (Pi.single b (1 : ℂ)) (star (Pi.single b (1 : ℂ))) =
      diagonal (fun x ↦ if x = b then (1 : ℂ) else 0) := by
  classical
  ext x y
  by_cases hx : x = b
  · subst x
    by_cases hy : y = b
    · subst y
      simp [vecMulVec_apply]
    · have hby : b ≠ y := Ne.symm hy
      simp [vecMulVec_apply, hy, hby]
  · simp [vecMulVec_apply, hx, Matrix.diagonal_apply]

/-- The sum of the actual on-site penalties has projector gap at least one
above its specified product basis vector, including the empty-site case. -/
theorem productBasisPenalty_gap (b : ι → Fin q) :
    (productBasisPenalty b -
      (1 - vecMulVec (Pi.single b (1 : ℂ)) (star (Pi.single b (1 : ℂ))))).PosSemidef := by
  classical
  rw [productBasisPenalty_eq_diagonal, productBasis_outer,
    ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_sub]
  apply PosSemidef.diagonal
  intro x
  change (0 : ℂ) ≤ (∑ v, if x v = b v then (0 : ℂ) else 1) -
    (1 - if x = b then 1 else 0)
  by_cases hx : x = b
  · subst x
    simp
  · obtain ⟨v, hv⟩ : ∃ v, x v ≠ b v := by
      by_contra h
      push Not at h
      exact hx (funext h)
    have hcount : (1 : ℂ) ≤ ∑ w, if x w = b w then (0 : ℂ) else 1 := by
      have h := Finset.single_le_sum
        (fun w _ ↦ (show (0 : ℂ) ≤ if x w = b w then 0 else 1 by
          split_ifs <;> norm_num)) (Finset.mem_univ v)
      simpa only [hv, ite_false] using h
    simp only [hx, ite_false, sub_zero]
    exact sub_nonneg.mpr hcount

/-- The prescribed product basis vector is an actual zero-energy vector. -/
theorem productBasisPenalty_mulVec (b : ι → Fin q) :
    productBasisPenalty b *ᵥ Pi.single b (1 : ℂ) = 0 := by
  classical
  rw [productBasisPenalty_eq_diagonal]
  ext x
  by_cases hx : x = b <;> simp [Matrix.mulVec_diagonal, hx]

end QuantumCircuit
