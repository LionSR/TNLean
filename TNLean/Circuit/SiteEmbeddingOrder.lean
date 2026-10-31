/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.Controlled
import QICLean.Analysis.MatrixSqrt

/-!
# Positivity and order under placement of sites

Placing an operator on an injectively selected family of sites preserves
positivity and operator order. The proof uses the positive square root and
the existing multiplicative, unital and adjoint-preserving placement map.

Source: the tensor-factor placement in arXiv:2307.01696, before Theorem 1;
also used for product-state ancillary extensions of the LVV13 chain.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Placement of operators as a complex-linear map. -/
noncomputable def embedOpLinearMap (e : κ → ι) :
    Matrix (κ → Fin d) (κ → Fin d) ℂ →ₗ[ℂ] Matrix (ι → Fin d) (ι → Fin d) ℂ where
  toFun := embedOp e
  map_add' := embedOp_add e
  map_smul' := embedOp_smul e

/-- Placement respects subtraction of operators on the selected sites. -/
theorem embedOp_sub (e : κ → ι) (X Y : Matrix (κ → Fin d) (κ → Fin d) ℂ) :
    embedOp e (X - Y) = embedOp e X - embedOp e Y :=
  (embedOpLinearMap e).map_sub X Y

/-- Placing a positive operator among additional idle sites preserves positivity. -/
theorem embedOp_posSemidef {e : κ → ι} (he : Function.Injective e)
    {X : Matrix (κ → Fin d) (κ → Fin d) ℂ} (hX : X.PosSemidef) :
    (embedOp e X).PosSemidef := by
  classical
  have h := Matrix.posSemidef_conjTranspose_mul_self (embedOp e (CFC.sqrt X))
  rw [embedOp_conjTranspose, embedOp_mul he, Matrix.conjTranspose_cfc_sqrt,
    CFC.sqrt_mul_sqrt_self X hX.nonneg] at h
  exact h

/-- Placement preserves operator inequalities on the selected sites. -/
theorem embedOp_le {e : κ → ι} (he : Function.Injective e)
    {X Y : Matrix (κ → Fin d) (κ → Fin d) ℂ} (hXY : X ≤ Y) :
    embedOp e X ≤ embedOp e Y := by
  classical
  apply Matrix.le_iff.mpr
  rw [← embedOp_sub]
  exact embedOp_posSemidef he (Matrix.le_iff.mp hXY)

/-- A positive on-site operator remains positive when placed at a physical site. -/
theorem siteOp_posSemidef (t : ι) {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosSemidef) : (siteOp t X).PosSemidef := by
  classical
  exact embedOp_posSemidef (siteSites_injective t)
    (hX.submatrix (Equiv.funUnique (Fin 1) (Fin d)))

/-- Placement at a single site preserves operator inequalities. -/
theorem siteOp_le (t : ι) {X Y : Matrix (Fin d) (Fin d) ℂ} (hXY : X ≤ Y) :
    siteOp t X ≤ siteOp t Y := by
  apply Matrix.le_iff.mpr
  rw [← siteOp_sub]
  exact siteOp_posSemidef t (Matrix.le_iff.mp hXY)

end QuantumCircuit
