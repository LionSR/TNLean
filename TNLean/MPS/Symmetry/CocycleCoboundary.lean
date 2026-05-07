/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.VirtualRepresentation
import TNLean.Algebra.CocycleCohomology

/-!
# Gauge independence of the cocycle class

If an injective MPS tensor is on-site symmetric under a group representation,
different choices of virtual gauge matrices `X(g)` produce cohomologous cocycles.
This establishes the cohomology class as a well-defined invariant of the
symmetric tensor, independent of the gauge parametrisation.

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

If `X₁(g⁻¹)` and `X₂(g⁻¹)` both intertwine `A` with the `g`-twisted tensor,
gauge uniqueness gives `X₂(g⁻¹) = f(g) · X₁(g⁻¹)` for some scalar
`f(g) ∈ ℂˣ`. Substituting into the projective multiplication law gives
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
  -- For each g, the two gauge matrices differ by a scalar.
  have hScalar : ∀ g : G, ∃ u : Units ℂ,
      (ρ₂.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) =
        (u : ℂ) • (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) :=
    fun g => gauge_unique_up_to_scalar hA (hρ₁ g) (hρ₂ g)
  choose f hf using hScalar
  have hρ₂_eq : ∀ g' : G, (ρ₂.X g' : Matrix (Fin D) (Fin D) ℂ) =
      (f (g'⁻¹) : ℂ) • (ρ₁.X g' : Matrix (Fin D) (Fin D) ℂ) := by
    intro g'
    have := hf (g'⁻¹)
    simp only [inv_inv] at this
    exact this
  refine ⟨fun g => f (g⁻¹), fun g h => ?_⟩
  -- From ρ₂.map_mul and the scalar relation above, extract the cocycle relation.
  have h_mul₂ := ρ₂.map_mul g h
  rw [hρ₂_eq g, hρ₂_eq h, hρ₂_eq (g * h)] at h_mul₂
  rw [smul_mul_smul_comm, ρ₁.map_mul, smul_smul, smul_smul] at h_mul₂
  have h_scalar_eq : (f (g⁻¹) : ℂ) * (f (h⁻¹) : ℂ) * (ω₁ g h : ℂ) =
      (ω₂ g h : ℂ) * (f ((g * h)⁻¹) : ℂ) :=
    ProjectiveRepresentation.smul_eq_smul_cancel hD ⟨ρ₁.X (g * h), rfl⟩ h_mul₂
  have hne : (f ((g * h)⁻¹) : ℂ) ≠ 0 := Units.ne_zero _
  apply Units.val_injective
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [eq_comm] at h_scalar_eq
  rw [← mul_inv_cancel_right₀ hne (ω₂ g h : ℂ), h_scalar_eq]
  ring

end MPSTensor
