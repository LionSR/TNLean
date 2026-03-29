/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.VirtualRepresentation
import TNLean.Algebra.CocycleCohomology

/-!
# Gauge independence of the cocycle class for SPT classification

This file proves that the cohomology class `H²(G, U(1))` associated to an
injective symmetric MPS tensor is independent of the gauge choice for the
virtual representation matrices `X(g)`.

## Main results

* `MPSTensor.cohomologousTo_of_isInjective` : different gauge choices for `X(g)` on an
  injective symmetric MPS tensor produce cohomologous cocycles

## References

* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
-/

open scoped Matrix

/-! ### Gauge independence of the cocycle class -/

namespace MPSTensor

open TNLean.Algebra

variable {d D : ℕ} {G : Type*} [Group G]

/-- **Gauge independence of the cocycle class.**

If two projective representations `ρ₁` and `ρ₂` (with cocycles `ω₁` and `ω₂`)
both arise as virtual representations of the same injective MPS tensor `A` under
on-site symmetry `U`, then `ω₁` and `ω₂` are cohomologous.

Concretely, if `X₁(g⁻¹)` and `X₂(g⁻¹)` both intertwine `A` with the `g`-twisted
tensor, then by gauge uniqueness `X₂(g⁻¹) = f(g) · X₁(g⁻¹)` for some scalar
`f(g) ∈ ℂˣ`. Substituting into the projective multiplication law yields
`ω₂(g,h) = f(g) * f(h) * f(g*h)⁻¹ * ω₁(g,h)`. -/
theorem cohomologousTo_of_isInjective
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hD : 0 < D)
    {ω₁ ω₂ : ScalarCocycle G}
    {ρ₁ : ProjectiveRepresentation (D := D) ω₁}
    {ρ₂ : ProjectiveRepresentation (D := D) ω₂}
    (hρ₁ : ∀ g i, twistedTensor A U g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (hρ₂ : ∀ g i, twistedTensor A U g i =
      (ρ₂.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₂.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ScalarCocycle.CohomologousTo ω₂ ω₁ := by
  -- Step 1: For each g, the two gauge matrices differ by a scalar
  have hScalar : ∀ g : G, ∃ u : Units ℂ,
      (ρ₂.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) =
        (u : ℂ) • (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) :=
    fun g => gauge_unique_up_to_scalar hA (hρ₁ g) (hρ₂ g)
  choose f hf using hScalar
  -- Step 2: Reindex so that ρ₂.X(g') = f(g'⁻¹) • ρ₁.X(g') for all g'
  have hρ₂_eq : ∀ g' : G, (ρ₂.X g' : Matrix (Fin D) (Fin D) ℂ) =
      (f (g'⁻¹) : ℂ) • (ρ₁.X g' : Matrix (Fin D) (Fin D) ℂ) := by
    intro g'
    have := hf (g'⁻¹)
    simp only [inv_inv] at this
    exact this
  -- Step 3: The witness is φ(g) = f(g⁻¹)
  refine ⟨fun g => f (g⁻¹), fun g h => ?_⟩
  -- Step 4: Compare multiplication laws to extract scalar equation
  -- From ρ₂.map_mul: ρ₂.X(g) * ρ₂.X(h) = ω₂(g,h) • ρ₂.X(g*h)
  have h_mul₂ := ρ₂.map_mul g h
  -- Substitute ρ₂.X(·) = f(·⁻¹) • ρ₁.X(·)
  rw [hρ₂_eq g, hρ₂_eq h, hρ₂_eq (g * h)] at h_mul₂
  -- LHS: (f(g⁻¹) • ρ₁.X g) * (f(h⁻¹) • ρ₁.X h)
  --     = (f(g⁻¹) * f(h⁻¹)) • (ρ₁.X g * ρ₁.X h)
  --     = (f(g⁻¹) * f(h⁻¹)) • (ω₁(g,h) • ρ₁.X(g*h))
  --     = (f(g⁻¹) * f(h⁻¹) * ω₁(g,h)) • ρ₁.X(g*h)
  -- RHS: ω₂(g,h) • (f((g*h)⁻¹) • ρ₁.X(g*h))
  --     = (ω₂(g,h) * f((g*h)⁻¹)) • ρ₁.X(g*h)
  -- Simplify h_mul₂ to scalar • matrix = scalar • matrix form
  rw [smul_mul_smul_comm, ρ₁.map_mul, smul_smul, smul_smul] at h_mul₂
  -- Step 5: Cancel the invertible matrix
  have h_scalar_eq : (f (g⁻¹) : ℂ) * (f (h⁻¹) : ℂ) * (ω₁ g h : ℂ) =
      (ω₂ g h : ℂ) * (f ((g * h)⁻¹) : ℂ) :=
    ProjectiveRepresentation.smul_eq_smul_cancel hD ⟨ρ₁.X (g * h), rfl⟩ h_mul₂
  -- Step 6: Lift scalar equation from ℂ to Units ℂ
  have hne : (f ((g * h)⁻¹) : ℂ) ≠ 0 := Units.ne_zero _
  apply Units.val_injective
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  -- Goal: ↑(ω₂ g h) = ↑(f g⁻¹) * (↑(f h⁻¹) * (↑(ω₁ g h) * (↑(f (g * h)⁻¹))⁻¹))
  -- From h_scalar_eq: a * b * c = ω₂ * e, so ω₂ = a * b * c * e⁻¹
  rw [eq_comm] at h_scalar_eq
  rw [← mul_inv_cancel_right₀ hne (ω₂ g h : ℂ), h_scalar_eq]
  ring

/-- Backward-compatible alias for `cohomologousTo_of_isInjective`. -/
@[deprecated cohomologousTo_of_isInjective (since := "2026-03-29")]
theorem cocycle_class_gauge_independent
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hD : 0 < D)
    {ω₁ ω₂ : ScalarCocycle G}
    {ρ₁ : ProjectiveRepresentation (D := D) ω₁}
    {ρ₂ : ProjectiveRepresentation (D := D) ω₂}
    (hρ₁ : ∀ g i, twistedTensor A U g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (hρ₂ : ∀ g i, twistedTensor A U g i =
      (ρ₂.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₂.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ScalarCocycle.CohomologousTo ω₂ ω₁ :=
  cohomologousTo_of_isInjective A hA U hD hρ₁ hρ₂

end MPSTensor
