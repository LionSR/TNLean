/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardForm
import TNLean.MPS.MPU.StaircaseGates

/-!
# Source cuts of an actual supplied two-site standard form

The two cuts of the supplied tensor itself have explicit factors. Their
intermediate spaces are pairs of the original spin coordinates. Contracting
the right factors gives exactly `v₂₃ (u₁₂ ⊗ u₃₄)`; contracting the left
factors gives exactly `v₂₃`. These act on four original spins. The tensor
has not been blocked again before taking its cuts.

These identities isolate the source-factor construction needed in the
forward local time-reversal argument. They assert actual cut equalities,
not the existence of comparison gauges or a local symmetry certificate.
Normalized source-factor records and their canonical rank identifications
are not asserted here.

Source: arXiv:1703.09188, proof of `PropChiral`, `eq:block-twosites`,
lines 1237–1252; cut conventions are `eq:sf-svd`, lines 479–506.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor.TwoSiteStandardFormData

variable {d D : ℕ} {W : MPOTensor (d * d) D}
  {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}

/-- Left factor of the first cut of the supplied tensor: retain its first
output spin and the original right half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutX₁ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin (d * d) × Fin D) (Fin d × Fin d) ℂ :=
  fun (i, γ) (a, s) ↦
    (1 : Matrix (Fin d) (Fin d) ℂ) (finProdFinEquiv.symm i).1 a *
      S.X₁ ((finProdFinEquiv.symm i).2, γ) s

/-- Right factor of the first cut, obtained by joining the unshifted gate
to the original left half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutY₁ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin d × Fin d) (Fin D × Fin (d * d)) ℂ :=
  fun (a, s) (α, j) ↦ ∑ t : Fin d,
    S.X₂ (α, a) t * u (t, s) (finProdFinEquiv.symm j)

/-- Left factor of the second cut: retain its second output spin and the
original left half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutX₂ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin D × Fin (d * d)) (Fin d × Fin d) ℂ :=
  fun (α, i) (t, b) ↦ S.X₂ (α, (finProdFinEquiv.symm i).1) t *
    (1 : Matrix (Fin d) (Fin d) ℂ) (finProdFinEquiv.symm i).2 b

/-- Right factor of the second cut, joining the unshifted gate to the
original right half factor. Source: arXiv:1703.09188,
`eq:block-twosites`, lines 1237–1244, and `eq:sf-svd`, lines 479–506. -/
noncomputable def cutY₂ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin d × Fin d) (Fin (d * d) × Fin D) ℂ :=
  fun (t, b) (j, γ) ↦ ∑ s : Fin d,
    u (t, s) (finProdFinEquiv.symm j) * S.X₁ (b, γ) s

/-- The first actual cut factors through the displayed pair space. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244. -/
theorem sourceCutM₁_eq_cutX₁_mul_cutY₁ (S : TwoSiteStandardFormData W u v) :
    sourceCutM₁ W = S.cutX₁ * S.cutY₁ := by
  classical
  ext ⟨i, γ⟩ ⟨α, j⟩
  rw [sourceCutM₁_apply, S.W_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, cutX₁, cutY₁,
    Matrix.one_apply, ite_mul, zero_mul, Finset.mul_sum,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ↓reduceIte, one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ s _
  ring

/-- The second actual cut factors through the displayed pair space. Source:
arXiv:1703.09188, `eq:block-twosites`, lines 1237–1244. -/
theorem sourceCutM₂_eq_cutX₂_mul_cutY₂ (S : TwoSiteStandardFormData W u v) :
    sourceCutM₂ W = S.cutX₂ * S.cutY₂ := by
  classical
  ext ⟨α, i⟩ ⟨j, γ⟩
  rw [sourceCutM₂_apply, S.W_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, cutX₂, cutY₂,
    Matrix.one_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ↓reduceIte, mul_one]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Contracting the two right cut factors gives the literal four-spin
three-gate expression, with no additional blocking. Source:
arXiv:1703.09188, `eq:block-twosites` and `UUdaggertrick`, lines 1237–1252. -/
theorem cutY₂_cutY₁_eq_staircaseMiddle_mul_kronecker
    (S : TwoSiteStandardFormData W u v) :
    (fun (l r : (Fin d × Fin d) × (Fin d × Fin d)) ↦
      ∑ β : Fin D, S.cutY₂ l.1 (finProdFinEquiv r.1, β) *
        S.cutY₁ l.2 (β, finProdFinEquiv r.2)) =
      staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) := by
  classical
  ext ⟨⟨a, b⟩, c, e⟩ ⟨i, j⟩
  simp only [cutY₁, cutY₂, Equiv.symm_apply_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_prod_type, staircaseMiddle, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ↓reduceIte, one_mul, mul_one]
  simp_rw [S.v_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ β _
  ring

/-- Contracting the two left cut factors gives the middle gate on four
original spins. Source: arXiv:1703.09188, `eq:block-twosites` and
`UUdaggertrick`, lines 1237–1252. -/
theorem cutX₁_cutX₂_eq_staircaseMiddle
    (S : TwoSiteStandardFormData W u v) :
    (fun (l r : (Fin d × Fin d) × (Fin d × Fin d)) ↦
      ∑ β : Fin D, S.cutX₁ (finProdFinEquiv l.1, β) r.1 *
        S.cutX₂ (β, finProdFinEquiv l.2) r.2) =
      staircaseMiddle (A := Fin d) (E := Fin d) v := by
  classical
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp only [cutX₁, cutX₂, Equiv.symm_apply_apply, staircaseMiddle,
    Matrix.kroneckerMap_apply, S.v_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  ring

end MPOTensor.TwoSiteStandardFormData
