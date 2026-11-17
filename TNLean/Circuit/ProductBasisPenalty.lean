/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.Controlled
import TNLean.Circuit.SiteEmbeddingOrder
import TNLean.Circuit.EntropySupport
import QICLean.ManyBody.Hamiltonian.KroneckerSum

/-!
# On-site penalties selecting a prescribed product basis vector

The sum of the actual penalties on all sites is gapped at energy zero with gap one, and its
zero-energy space is the line through the specified product basis vector. The construction also
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

/-- The product penalty as the diagonal matrix of the real count of sites differing from the
target. -/
private theorem productBasisPenalty_eq_diagonal_real (b : ι → Fin q) :
    productBasisPenalty b =
      diagonal fun x ↦ ((∑ v, if x v = b v then (0 : ℝ) else 1 : ℝ) : ℂ) := by
  rw [productBasisPenalty_eq_diagonal]
  congr 1
  funext x
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by split_ifs <;> simp

omit [DecidableEq ι] in
/-- A configuration other than the target differs from it at some site. -/
private theorem one_le_count_of_ne {b x : ι → Fin q} (hx : x ≠ b) :
    1 ≤ ∑ v, if x v = b v then (0 : ℝ) else 1 := by
  obtain ⟨v, hv⟩ : ∃ v, x v ≠ b v := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have h := Finset.single_le_sum
    (fun w _ ↦ (show (0 : ℝ) ≤ if x w = b w then 0 else 1 by split_ifs <;> norm_num))
    (Finset.mem_univ v)
  simpa only [hv, ite_false] using h

/-- The sum of the on-site penalties is Hermitian. -/
theorem isHermitian_productBasisPenalty (b : ι → Fin q) : (productBasisPenalty b).IsHermitian := by
  rw [productBasisPenalty_eq_diagonal_real]
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun x ↦ Complex.conj_ofReal _)

/-- The sum of the on-site penalties is gapped at energy zero with gap one, including the
empty-site case. -/
theorem isGapped_productBasisPenalty (b : ι → Fin q) :
    ManyBody.IsGapped (productBasisPenalty b) 0 1 := by
  rw [productBasisPenalty_eq_diagonal_real, ManyBody.isGapped_diagonal_iff]
  refine ⟨⟨b, by simp⟩, fun x ↦ ?_⟩
  by_cases hx : x = b
  · exact Or.inl (by simp [hx])
  · exact Or.inr (by simpa only [zero_add] using one_le_count_of_ne hx)

/-- The zero-energy space of the sum of the on-site penalties is the line through the
prescribed product basis vector. -/
theorem groundSpace_productBasisPenalty (b : ι → Fin q) :
    ManyBody.groundSpace (productBasisPenalty b) 0 =
      Submodule.span ℂ {WithLp.toLp 2 (Pi.single b (1 : ℂ))} := by
  ext ψ
  rw [productBasisPenalty_eq_diagonal_real, ManyBody.mem_groundSpace_diagonal_iff,
    Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨ψ b, ?_⟩
    ext x
    by_cases hx : x = b
    · subst hx
      simp
    · have hne : ((∑ v, if x v = b v then (0 : ℝ) else 1 : ℝ) : ℂ) ≠ ((0 : ℝ) : ℂ) :=
        Complex.ofReal_injective.ne (one_pos.trans_le (one_le_count_of_ne hx)).ne'
      simp [hx, h x hne]
  · rintro ⟨c, rfl⟩ x hx
    have hxb : x ≠ b := by
      rintro rfl
      exact hx (by simp)
    simp [hxb]

end QuantumCircuit
