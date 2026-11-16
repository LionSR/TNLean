/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryKronecker
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# The standard form of the doubled block

If a tensor `W` on pairs of sites is in standard form with gates `u, v`, then its
two-site block is in standard form with the gates
`u⁽²⁾ = (1_ℓ ⊗ v ⊗ 1_r)(u ⊗ u)` and `v⁽²⁾ = 1_d ⊗ v ⊗ 1_d`, of left rank `ℓ d`
and right rank `d r`. In the indices of arXiv:1703.09188, lines 1456--1458 and
1556--1558, these are `u⁽²⁾_{11',22'} = v_{1'2} u_{11'} u_{22'}` and
`v⁽²⁾_{11',22'} = v_{1'2}`.

## Main definitions

* `MPOTensor.doubledU`, `MPOTensor.doubledV`: the doubled gates.
* `MPOTensor.TwoSiteStandardFormData.doubled`: the standard form of `blockTwo W`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D ℓ r : ℕ}

/-- The output coordinates `ℓ ⊗ (d ⊗ d) ⊗ r` of the doubled unshifted gate,
grouped as the left rank `ℓ d` and the right rank `d r`. -/
def doubledOutEquiv (ℓ d r : ℕ) :
    Fin ℓ × ((Fin d × Fin d) × Fin r) ≃ Fin (ℓ * d) × Fin (d * r) where
  toFun x := (finProdFinEquiv (x.1, x.2.1.1), finProdFinEquiv (x.2.1.2, x.2.2))
  invFun y := ((finProdFinEquiv.symm y.1).1,
    (((finProdFinEquiv.symm y.1).2, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2))
  left_inv x := by simp
  right_inv y := by simp

/-- The input coordinates of the doubled gates: a pair of pairs of sites. -/
def doubledInEquiv (d : ℕ) :
    (Fin d × Fin d) × (Fin d × Fin d) ≃ Fin (d * d) × Fin (d * d) :=
  Equiv.prodCongr finProdFinEquiv finProdFinEquiv

/-- Regrouping `(ℓ ⊗ r) ⊗ (ℓ ⊗ r)` as `ℓ ⊗ (r ⊗ ℓ) ⊗ r`, the middle factor
being the input of the shifted gate. -/
def doubledMidEquiv (ℓ r : ℕ) :
    (Fin ℓ × Fin r) × (Fin ℓ × Fin r) ≃ Fin ℓ × ((Fin r × Fin ℓ) × Fin r) where
  toFun x := (x.1.1, ((x.1.2, x.2.1), x.2.2))
  invFun y := ((y.1, y.2.1.1), (y.2.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The input coordinates `d ⊗ (r ⊗ ℓ) ⊗ d` of the doubled shifted gate, grouped
as the right rank `d r` and the left rank `ℓ d`. -/
def doubledShiftInEquiv (ℓ d r : ℕ) :
    Fin d × ((Fin r × Fin ℓ) × Fin d) ≃ Fin (d * r) × Fin (ℓ * d) where
  toFun x := (finProdFinEquiv (x.1, x.2.1.1), finProdFinEquiv (x.2.1.2, x.2.2))
  invFun y := ((finProdFinEquiv.symm y.1).1,
    (((finProdFinEquiv.symm y.1).2, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2))
  left_inv x := by simp
  right_inv y := by simp

/-- The output coordinates `d ⊗ (d ⊗ d) ⊗ d` of the doubled shifted gate, a
pair of pairs of sites. -/
def doubledShiftOutEquiv (d : ℕ) :
    Fin d × ((Fin d × Fin d) × Fin d) ≃ Fin (d * d) × Fin (d * d) where
  toFun x := (finProdFinEquiv (x.1, x.2.1.1), finProdFinEquiv (x.2.1.2, x.2.2))
  invFun y := ((finProdFinEquiv.symm y.1).1,
    (((finProdFinEquiv.symm y.1).2, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2))
  left_inv x := by simp
  right_inv y := by simp

/-- The doubled unshifted gate `u⁽²⁾ = (1_ℓ ⊗ v ⊗ 1_r)(u ⊗ u)`.
Source: arXiv:1703.09188, lines 1456--1458 and 1556--1558. -/
noncomputable def doubledU (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin (ℓ * d) × Fin (d * r)) (Fin (d * d) × Fin (d * d)) ℂ :=
  Matrix.reindex (doubledOutEquiv ℓ d r) (doubledInEquiv d)
    (((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) *
      Matrix.reindex (doubledMidEquiv ℓ r) (Equiv.refl _) (u ⊗ₖ u))

/-- The doubled shifted gate `v⁽²⁾ = 1_d ⊗ v ⊗ 1_d`.
Source: arXiv:1703.09188, lines 1456--1458 and 1556--1558. -/
noncomputable def doubledV (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * r) × Fin (ℓ * d)) ℂ :=
  Matrix.reindex (doubledShiftOutEquiv d) (doubledShiftInEquiv ℓ d r)
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)))

theorem doubledU_apply (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (t : Fin ℓ) (a b : Fin d) (s : Fin r)
    (i₁ i₁' i₂ i₂' : Fin d) :
    doubledU u v (finProdFinEquiv (t, a), finProdFinEquiv (b, s))
        (finProdFinEquiv (i₁, i₁'), finProdFinEquiv (i₂, i₂')) =
      ∑ s₁ : Fin r, ∑ t₂ : Fin ℓ, v (a, b) (s₁, t₂) * (u (t, s₁) (i₁, i₁') * u (t₂, s) (i₂, i₂')) := by
  simp only [doubledU, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp [doubledOutEquiv, doubledInEquiv, doubledMidEquiv, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem doubledV_apply (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (j₁ j₁' j₂ j₂' b : Fin d)
    (s : Fin r) (t : Fin ℓ) (a : Fin d) :
    doubledV v (finProdFinEquiv (j₁, j₁'), finProdFinEquiv (j₂, j₂'))
        (finProdFinEquiv (b, s), finProdFinEquiv (t, a)) =
      (if j₁ = b then 1 else 0) * (v (j₁', j₂) (s, t) * (if j₂' = a then 1 else 0)) := by
  simp [doubledV, doubledShiftOutEquiv, doubledShiftInEquiv, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem isUnitaryBetween_doubledU {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hu : u.IsUnitaryBetween)
    (hv : v.IsUnitaryBetween) : (doubledU u v).IsUnitaryBetween := by
  have h1 : ∀ n : ℕ, (1 : Matrix (Fin n) (Fin n) ℂ).IsUnitaryBetween := fun n ↦
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (one_mem _)
  have hmid := Matrix.IsUnitaryBetween.kronecker _ _ (h1 ℓ)
    (Matrix.IsUnitaryBetween.kronecker _ _ hv (h1 r))
  have huu := (Matrix.IsUnitaryBetween.kronecker _ _ hu hu).reindex _ (doubledMidEquiv ℓ r)
    (Equiv.refl _)
  exact (hmid.mul _ _ huu).reindex _ _ _

theorem isUnitaryBetween_doubledV {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hv : v.IsUnitaryBetween) : (doubledV v).IsUnitaryBetween := by
  have h1 : ∀ n : ℕ, (1 : Matrix (Fin n) (Fin n) ℂ).IsUnitaryBetween := fun n ↦
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (one_mem _)
  exact (Matrix.IsUnitaryBetween.kronecker _ _ (h1 d)
    (Matrix.IsUnitaryBetween.kronecker _ _ hv (h1 d))).reindex _ _ _

end MPOTensor
