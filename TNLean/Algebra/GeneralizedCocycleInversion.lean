/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GeneralizedCocycle

/-!
# Inversion of block-dependent generalized cocycles

This file formalizes the hat operation from arXiv:2502.20257, line 5912, for
block-dependent scalar one- and two-cochains. For a group `G` acting on block
labels `X`, the operations are

`(hat χ)ˣ_g = χ^{g • x}_{g⁻¹}`

and

`(hat Ω)ˣ_{g,h} = Ω^{gh • x}_{h⁻¹,g⁻¹}`.

Both operations are involutions, preserve pointwise multiplication, and
commute with the generalized coboundary.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

namespace ActionTensorGauge

/-- The block-dependent hat operation on scalar one-cochains:
`(hat χ)ˣ_g = χ^{g • x}_{g⁻¹}`.

This is arXiv:2502.20257, line 5912, specialized to one group index. -/
def hat (χ : ActionTensorGauge G X) : ActionTensorGauge G X :=
  fun g x => χ g⁻¹ (g • x)

/-- The hat operation on block-dependent scalar one-cochains is an involution. -/
@[simp]
theorem hat_hat (χ : ActionTensorGauge G X) : hat (hat χ) = χ := by
  funext g x
  simp [hat]

/-- The hat operation preserves the constant one cochain. -/
@[simp]
theorem hat_one : hat (1 : ActionTensorGauge G X) = 1 := by
  rfl

/-- The hat operation preserves pointwise multiplication. -/
@[simp]
theorem hat_mul (χ ψ : ActionTensorGauge G X) : hat (χ * ψ) = hat χ * hat ψ := by
  rfl

/-- The hat operation preserves pointwise inversion. -/
@[simp]
theorem hat_inv (χ : ActionTensorGauge G X) : hat χ⁻¹ = (hat χ)⁻¹ := by
  rfl

/-- The hat operation preserves pointwise division. -/
@[simp]
theorem hat_div (χ ψ : ActionTensorGauge G X) : hat (χ / ψ) = hat χ / hat ψ := by
  rfl

end ActionTensorGauge

namespace LSymbol

/-- The block-dependent hat operation on scalar two-cochains:
`(hat Ω)ˣ_{g,h} = Ω^{gh • x}_{h⁻¹,g⁻¹}`.

This is arXiv:2502.20257, line 5912, specialized to two group indices. -/
def hat (Ω : LSymbol G X) : LSymbol G X :=
  fun x g h => Ω ((g * h) • x) h⁻¹ g⁻¹

/-- The hat operation on block-dependent scalar two-cochains is an involution. -/
@[simp]
theorem hat_hat (Ω : LSymbol G X) : hat (hat Ω) = Ω := by
  funext x g h
  simp [hat, mul_smul]

/-- The hat operation preserves the constant one two-cochain. -/
@[simp]
theorem hat_one : hat (1 : LSymbol G X) = 1 := by
  rfl

/-- The hat operation preserves pointwise multiplication. -/
@[simp]
theorem hat_mul (Ω Λ : LSymbol G X) : hat (Ω * Λ) = hat Ω * hat Λ := by
  rfl

/-- The hat operation preserves pointwise inversion. -/
@[simp]
theorem hat_inv (Ω : LSymbol G X) : hat Ω⁻¹ = (hat Ω)⁻¹ := by
  rfl

/-- The hat operation preserves pointwise division. -/
@[simp]
theorem hat_div (Ω Λ : LSymbol G X) : hat (Ω / Λ) = hat Ω / hat Λ := by
  rfl

/-- The block-dependent hat operation commutes with the generalized
coboundary: `hat (dχ) = d(hat χ)`.

This is the one-to-two-cochain instance of the notation introduced in
arXiv:2502.20257, lines 5910--5922. -/
theorem hat_coboundary (χ : ActionTensorGauge G X) :
    hat (ActionTensorGauge.coboundary χ) =
      ActionTensorGauge.coboundary (ActionTensorGauge.hat χ) := by
  funext x g h
  simp only [hat, ActionTensorGauge.coboundary, ActionTensorGauge.hat]
  simp [mul_smul, mul_comm]

end LSymbol

end TNLean.Algebra
