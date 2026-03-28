/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.GaugeUniqueness
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Virtual representation theorem for injective MPS

If an injective MPS tensor `A` is on-site symmetric under a group representation `U`,
then the virtual gauge matrices extracted from the single-block Fundamental Theorem
can be reindexed by inversion to produce a genuine projective representation on the
bond space.

## Main results

* `MPSTensor.virtual_rep_of_symmetric_injective`: the main theorem — the virtual gauges
  define a unit-valued scalar cocycle `ω` and a `ProjectiveRepresentation` on the bond
  space.

## Convention note

The natural law from `twistedTensor_mul` (which says `twist(g*h) = twist_g ∘ twist_h`)
gives `X(h) * X(g) = ω(h,g) • X(g * h)`. The theorem below packages this into the
standard projective representation law by defining `V(g) = X(g⁻¹)`.

## References

* Pérez-García et al., *Matrix Product State Representations*, arXiv:0608197
* Pérez-García et al., *Characterizing symmetries in an MPS*, arXiv:0802.0447 (PRL)
* Cirac et al., *MPS and PEPS*, arXiv:2011.12127, Section III.A
* Molnár, *The frustration-free Hamiltonian…*, arXiv:1804.04964, Section 5
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

private abbrev invMat (Y : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

/-! ### Virtual representation theorem -/

section VirtualRep

open TNLean.Algebra

variable {G : Type*} [Group G]

/-- Twisting commutes with virtual conjugation. -/
private lemma twistedTensor_gaugeEquiv
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (Y : GL (Fin D) ℂ) (g : G) :
    twistedTensor (fun j =>
      (Y : Matrix (Fin D) (Fin D) ℂ) * A j * invMat Y) U g =
      fun i =>
        (Y : Matrix (Fin D) (Fin D) ℂ) * twistedTensor A U g i * invMat Y := by
  funext i
  simp only [twistedTensor]
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1
  ext j
  simp [Matrix.mul_assoc]

/-- The product `X(h) * X(g)` intertwines `A` with `twist(g * h)`. -/
private lemma gauge_product_intertwines
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (X : G → GL (Fin D) ℂ)
    (hX : ∀ g i, twistedTensor A U g i =
      (X g : Matrix (Fin D) (Fin D) ℂ) * A i * invMat (X g))
    (g h : G) (i : Fin d) :
    twistedTensor A U (g * h) i =
      ((X h * X g : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
        invMat (X h * X g) := by
  rw [twistedTensor_mul]
  conv_lhs =>
    rw [show twistedTensor A U h = fun j =>
      (X h : Matrix (Fin D) (Fin D) ℂ) * A j * invMat (X h) from funext (hX h)]
  rw [twistedTensor_gaugeEquiv A U (X h) g]
  simp only
  rw [hX g i]
  simp only [invMat, Matrix.GeneralLinearGroup.coe_mul, mul_inv_rev, Matrix.mul_assoc]

/-- **Virtual representation theorem for injective MPS with on-site symmetry.**

If an injective MPS tensor `A` is symmetric under on-site action of a group `G`,
then there exist:
- a unit-valued scalar cocycle `ω : ScalarCocycle G`,
- a projective representation `ρ` of `G` on the bond space,

such that:
1. `ρ.X (g⁻¹)` intertwines `A` with the `g`-twisted tensor, and
2. `ρ.map_mul'` is the standard projective multiplication law. -/
theorem virtual_rep_of_symmetric_injective
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D) ω,
        ∀ g i, twistedTensor A U g i =
          (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
            invMat (ρ.X (g⁻¹)) := by
  have hGauge : ∀ g : G, GaugeEquiv A (twistedTensor A U g) :=
    gaugeEquiv_twistedTensor_of_injective A hA U hSymm
  choose X hX using fun g => (hGauge g)
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
  choose ω hω using fun g h => hScalar (h⁻¹) (g⁻¹)
  let ρ : ProjectiveRepresentation (D := D) ω := {
    X := fun g => X (g⁻¹)
    map_mul' := by
      intro g h
      simpa [mul_inv_rev] using hω g h
  }
  refine ⟨ω, ρ, ?_⟩
  intro g i
  simpa [ρ] using hX g i

/-- For positive bond dimension, the factor system obtained from
`virtual_rep_of_symmetric_injective` satisfies the 2-cocycle identity. -/
theorem virtual_rep_of_symmetric_injective_cocycle
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U)
    (hD : 0 < D) :
    ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D) ω,
        (∀ g i, twistedTensor A U g i =
          (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i * invMat (ρ.X (g⁻¹))) ∧
        ∀ g h k : G,
          (ω g h : ℂ) * (ω (g * h) k : ℂ) =
            (ω g (h * k) : ℂ) * (ω h k : ℂ) := by
  rcases virtual_rep_of_symmetric_injective A hA U hSymm with ⟨ω, ρ, hρ⟩
  refine ⟨ω, ρ, hρ, ?_⟩
  intro g h k
  exact ρ.cocycle_of_assoc (D := D) hD g h k

end VirtualRep

end MPSTensor
