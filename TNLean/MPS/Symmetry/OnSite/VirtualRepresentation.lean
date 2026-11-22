/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Gauge.OnSiteSymmetry
import TNLean.MPS.Tensor.Gauge.GaugeUniqueness
import QICLean.Algebra.Cohomology.ProjectiveRepresentation
import QICLean.Algebra.Cohomology.CocycleCohomology

/-!
# Virtual representation theorem for injective MPS

If an injective MPS tensor `A` is on-site symmetric under a group representation `U`,
then the virtual gauge matrices obtained from the single-block Fundamental
Theorem can be reindexed by inversion to produce a projective representation on the
bond space.

The pointwise gauges are supplied by `gaugeEquiv_twistedTensor_of_injective`
(the single-block Fundamental Theorem applied to each twisted tensor).
Gauge uniqueness and the twist composition law then assemble these gauges into the
virtual representation.

## Main results

* `MPSTensor.virtual_rep_of_symmetric_injective`: the virtual gauges
  define a unit-valued scalar cocycle `ω` and a `ProjectiveRepresentation` on the bond
  space.

## Convention

The composition law `twistedTensor_mul` gives
`twist(g*h) = twist_g ∘ twist_h`, which translates to
`X(h) * X(g) = ω(h,g) • X(g * h)` for the chosen gauges.  The theorem
below reindexes by inversion, setting `V(g) = X(g⁻¹)`, to obtain the
standard projective representation law
`V(g) * V(h) = ω(g,h) • V(g*h)`.

## References

* Pérez-García et al., *Matrix Product State Representations*, arXiv:0608197
* Pérez-García et al., *Characterizing symmetries in an MPS*, arXiv:0802.0447 (PRL)
* Cirac et al., *MPS and PEPS*, arXiv:2011.12127, Section III.A
* Molnár, *The frustration-free Hamiltonian…*, arXiv:1804.04964, Section 5

## Gauge independence of the cocycle class

If an injective MPS tensor is on-site symmetric under a group representation,
different choices of virtual gauge matrices `X(g)` produce cohomologous cocycles.
This establishes the cohomology class as a well-defined invariant of the
symmetric tensor, independent of the gauge parametrisation.

### Main results

* `MPSTensor.cohomologousTo_of_isInjective` : different gauge choices for `X(g)` on an
  injective symmetric MPS tensor produce cohomologous cocycles

### References

* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
-/

section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

private abbrev invMat (Y : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

/-! ### Virtual representation theorem -/

section VirtualRep

variable {G : Type} [Group G]

/-- Virtual covariance on an injective tensor determines a projective
representation after inversion of the group index. The chosen virtual
matrices are retained, so unitarity can be preserved. Source:
arXiv:1010.3732, Section II.F.2, projective virtual symmetry. -/
theorem exists_projectiveRepresentation_of_virtual_covariance
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (X : G → GL (Fin D) ℂ)
    (hX : ∀ g i, twistedTensor A U g i =
      (X g : Matrix (Fin D) (Fin D) ℂ) * A i * invMat (X g)) :
    ∃ ω : ScalarCocycle G, ∃ ρ : ProjectiveRepresentation (D := D) ω,
      (∀ g, ρ.X g = X (g⁻¹)) ∧
      ∀ g i, twistedTensor A U g i =
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i * invMat (ρ.X (g⁻¹)) := by
  have hProd : ∀ g h : G, ∀ i : Fin d,
      twistedTensor A U (g * h) i =
        ((X h * X g : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((X h * X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    fun g h => gauge_product_intertwines A U X hX g h
  have hScalar : ∀ g h : G, ∃ u : Units ℂ,
      (X h : Matrix (Fin D) (Fin D) ℂ) * (X g : Matrix (Fin D) (Fin D) ℂ) =
        (u : ℂ) • (X (g * h) : Matrix (Fin D) (Fin D) ℂ) := by
    intro g h
    rcases gauge_unique_up_to_scalar hA (hX (g * h)) (hProd g h) with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simpa [Matrix.GeneralLinearGroup.coe_mul] using hu
  choose ω hω using fun p : G × G => hScalar (p.2⁻¹) (p.1⁻¹)
  let ρ : ProjectiveRepresentation (D := D) ω := {
    X := fun g => X (g⁻¹)
    map_mul' := by
      intro g h
      simpa [mul_inv_rev] using hω (g, h)
  }
  refine ⟨ω, ρ, fun _ => rfl, ?_⟩
  intro g i
  simpa [ρ] using hX g i

/-- **Virtual representation theorem for injective MPS with on-site symmetry.**

If an injective MPS tensor `A` is symmetric under on-site action of a group `G`,
then the single-block Fundamental Theorem supplies gauges for all twists, and
there exist:
- a unit-valued scalar cocycle `ω : ScalarCocycle G`,
- a projective representation `ρ` of `G` on the bond space,

such that:
1. `ρ.X (g⁻¹)` intertwines `A` with the `g`-twisted tensor, and
2. `ρ.map_mul'` is the standard projective multiplication law. -/
theorem virtual_rep_of_symmetric_injective
    (A : MPSTensor d D)
    (hA : Kraus.IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D) ω,
        ∀ g i, twistedTensor A U g i =
          (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
            invMat (ρ.X (g⁻¹)) := by
  have hGauge := gaugeEquiv_twistedTensor_of_injective A hA U hSymm
  choose X hX using hGauge
  obtain ⟨ω, ρ, _, hρ⟩ := exists_projectiveRepresentation_of_virtual_covariance A hA U X hX
  exact ⟨ω, ρ, hρ⟩

/-- For positive bond dimension, the factor system obtained from
`virtual_rep_of_symmetric_injective` satisfies the 2-cocycle identity. -/
theorem virtual_rep_of_symmetric_injective_cocycle
    (A : MPSTensor d D)
    (hA : Kraus.IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U)
    (hD : 0 < D) :
    ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D) ω,
        (∀ g i, twistedTensor A U g i =
          (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i * invMat (ρ.X (g⁻¹))) ∧
        ∀ g h k : G,
          (ω (g, h) : ℂ) * (ω (g * h, k) : ℂ) =
            (ω (g, h * k) : ℂ) * (ω (h, k) : ℂ) := by
  rcases virtual_rep_of_symmetric_injective A hA U hSymm with ⟨ω, ρ, hρ⟩
  refine ⟨ω, ρ, hρ, ?_⟩
  intro g h k
  exact ρ.cocycle_of_assoc (D := D) hD g h k

end VirtualRep

end MPSTensor

end

section

open scoped Matrix ScalarCohomology

/-! ### Gauge independence of the cocycle class -/

namespace MPSTensor

open ScalarCohomology

variable {d D : ℕ} {G : Type} [Group G]

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
    (hA : Kraus.IsInjective A)
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
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₂ hD)) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ hD)) := by
  apply (H2π_eq_iff_isMulCoboundary₂_div _ _).mpr
  apply (isMulCoboundary₂_div_iff _ _).mpr
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
  have h_scalar_eq : (f (g⁻¹) : ℂ) * (f (h⁻¹) : ℂ) * (ω₁ (g, h) : ℂ) =
      (ω₂ (g, h) : ℂ) * (f ((g * h)⁻¹) : ℂ) :=
    ProjectiveRepresentation.smul_eq_smul_cancel hD ⟨ρ₁.X (g * h), rfl⟩ h_mul₂
  have hne : (f ((g * h)⁻¹) : ℂ) ≠ 0 := Units.ne_zero _
  apply Units.val_injective
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [eq_comm] at h_scalar_eq
  rw [← mul_inv_cancel_right₀ hne (ω₂ (g, h) : ℂ), h_scalar_eq]
  ring

end MPSTensor

end
