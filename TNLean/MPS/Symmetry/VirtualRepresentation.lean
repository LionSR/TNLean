/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.Algebra.ProjectiveRepresentation
import TNLean.Algebra.ScalarCommutant

/-!
# Virtual representation theorem for injective MPS

If an injective MPS tensor `A` is on-site symmetric under a group representation `U`,
then the virtual gauge matrices `X(g)` obtained from the single-block Fundamental Theorem
form a **projective representation** of `G` on the bond space.

## Main results

* `MPSTensor.gaugeEquiv_unique_up_to_scalar`: gauge uniqueness — for injective `A`, any two
  gauge matrices relating the same pair of tensors differ by a scalar factor.
* `MPSTensor.virtual_rep_of_symmetric_injective`: the main theorem — the virtual gauges
  satisfy a projective multiplication law with a scalar 2-cochain `ω`.

## Convention note

The natural law from `twistedTensor_mul` (which says `twist(g*h) = twist_g ∘ twist_h`)
gives `X(h) * X(g) = ω(h,g) • X(g * h)`. To obtain the standard projective
representation law `V(g) * V(h) = ω'(g,h) • V(g * h)`, one defines `V(g) = X(g⁻¹)`.

## References

* Pérez-García et al., *Matrix Product State Representations*, arXiv:0608197
* Pérez-García et al., *Characterizing symmetries in an MPS*, arXiv:0802.0447 (PRL)
* Cirac et al., *MPS and PEPS*, arXiv:2011.12127, Section III.A
* Molnár, *The frustration-free Hamiltonian…*, arXiv:1804.04964, Section 5
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### GL coercion helpers -/

private lemma GL_inv_mul (X : GL (Fin D) ℂ) :
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
      (X : Matrix (Fin D) (Fin D) ℂ) = 1 :=
  show (X⁻¹ * X : GL (Fin D) ℂ).val = 1 by simp

private lemma GL_mul_inv (X : GL (Fin D) ℂ) :
    (X : Matrix (Fin D) (Fin D) ℂ) *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 :=
  show (X * X⁻¹ : GL (Fin D) ℂ).val = 1 by simp

/-! ### Gauge uniqueness for injective tensors -/

/-- If `A` is injective and both `X₁` and `X₂` satisfy the gauge equivalence
`B i = X * A i * X⁻¹`, then `X₁` and `X₂` differ by a scalar factor. -/
theorem gaugeEquiv_unique_up_to_scalar
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {X₁ X₂ : GL (Fin D) ℂ}
    (h₁ : ∀ i : Fin d, B i = X₁ * A i * (X₁⁻¹ : GL (Fin D) ℂ))
    (h₂ : ∀ i : Fin d, B i = X₂ * A i * (X₂⁻¹ : GL (Fin D) ℂ)) :
    ∃ c : ℂ, (X₁ : Matrix (Fin D) (Fin D) ℂ) =
      c • (X₂ : Matrix (Fin D) (Fin D) ℂ) := by
  -- Write x₁, x₂ for the matrix coercions for clarity
  set x₁ : Matrix (Fin D) (Fin D) ℂ := (X₁ : Matrix (Fin D) (Fin D) ℂ)
  set x₂ : Matrix (Fin D) (Fin D) ℂ := (X₂ : Matrix (Fin D) (Fin D) ℂ)
  set x₁' : Matrix (Fin D) (Fin D) ℂ := ((X₁⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set x₂' : Matrix (Fin D) (Fin D) ℂ := ((X₂⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set z : Matrix (Fin D) (Fin D) ℂ := x₂' * x₁
  have hx₁inv : x₁' * x₁ = 1 := GL_inv_mul X₁
  have hx₂inv : x₂' * x₂ = 1 := GL_inv_mul X₂
  have hZcomm : ∀ i : Fin d, z * A i = A i * z := by
    intro i
    have heq : x₁ * A i * x₁' = x₂ * A i * x₂' := by rw [← h₁ i, ← h₂ i]
    have lhs : z * A i = x₂' * (x₁ * A i * x₁') * x₁ := by
      change x₂' * x₁ * A i = x₂' * (x₁ * A i * x₁') * x₁
      simp only [Matrix.mul_assoc]
      conv_rhs => rw [hx₁inv, Matrix.mul_one]
    have rhs : x₂' * (x₂ * A i * x₂') * x₁ = A i * z := by
      change x₂' * (x₂ * A i * x₂') * x₁ = A i * (x₂' * x₁)
      simp only [Matrix.mul_assoc]
      conv_lhs => rw [← Matrix.mul_assoc x₂' x₂, hx₂inv, Matrix.one_mul]
    rw [lhs, heq, rhs]
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top z hA.span_eq_top
    (fun M hM => by obtain ⟨i, rfl⟩ := hM; exact hZcomm i)
  refine ⟨c, ?_⟩
  have hx₁_eq : x₁ = x₂ * z := by
    calc x₁ = 1 * x₁ := by rw [Matrix.one_mul]
      _ = (x₂ * x₂') * x₁ := by
          rw [show x₂ * x₂' = (1 : Matrix (Fin D) (Fin D) ℂ) from by
            calc x₂ * x₂' = x₂ * x₂' := rfl
              _ = 1 := GL_mul_inv X₂]
      _ = x₂ * z := by rw [Matrix.mul_assoc]
  rw [hx₁_eq, hc]
  ext p q
  simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Finset.sum_ite_eq', Finset.mem_univ, mul_comm]

/-! ### Virtual representation theorem -/

section VirtualRep

variable {G : Type*} [Group G]

/-- Twisting commutes with virtual conjugation. -/
private lemma twistedTensor_gaugeEquiv
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (Y : GL (Fin D) ℂ) (g : G) :
    ∀ i : Fin d,
      twistedTensor (fun j =>
        (Y : Matrix (Fin D) (Fin D) ℂ) * A j *
          ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) U g i =
        (Y : Matrix (Fin D) (Fin D) ℂ) * twistedTensor A U g i *
          ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  intro i
  simp only [twistedTensor]
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1; ext j
  simp [Matrix.mul_assoc]

/-- The product `X(h) * X(g)` intertwines `A` with `twist(g * h)`. -/
private lemma gauge_product_intertwines
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (X : G → GL (Fin D) ℂ)
    (hX : ∀ g i, twistedTensor A U g i =
      (X g : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X g)⁻¹ : GL (Fin D) ℂ))
    (g h : G) (i : Fin d) :
    twistedTensor A U (g * h) i =
      ((X h * X g : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((X h * X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  rw [twistedTensor_mul]
  conv_lhs =>
    rw [show twistedTensor A U h = fun j =>
      (X h : Matrix (Fin D) (Fin D) ℂ) * A j *
        ((X h)⁻¹ : GL (Fin D) ℂ) from funext (hX h)]
  rw [twistedTensor_gaugeEquiv A U (X h) g i, hX g i]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
    mul_inv_rev, Matrix.mul_assoc]

/-- **Virtual representation theorem for injective MPS with on-site symmetry.**

If an injective MPS tensor `A` is symmetric under on-site action of a group `G`,
then there exist:
- a family of invertible virtual matrices `X : G → GL(D, ℂ)`,
- a scalar 2-cochain `ω : G → G → ℂ`,

such that:
1. each `X(g)` intertwines `A` with the `g`-twisted tensor, and
2. `X(h) * X(g) = ω(h,g) • X(g * h)` — the projective multiplication law. -/
theorem virtual_rep_of_symmetric_injective
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∃ (X : G → GL (Fin D) ℂ),
      (∀ g i, twistedTensor A U g i =
        (X g : Matrix (Fin D) (Fin D) ℂ) * A i *
          ((X g)⁻¹ : GL (Fin D) ℂ)) ∧
      ∃ (ω : G → G → ℂ),
        ∀ g h : G,
          ((X h : Matrix (Fin D) (Fin D) ℂ) *
            (X g : Matrix (Fin D) (Fin D) ℂ)) =
            ω h g • (X (g * h) : Matrix (Fin D) (Fin D) ℂ) := by
  have hGauge : ∀ g : G, GaugeEquiv A (twistedTensor A U g) :=
    gaugeEquiv_twistedTensor_of_injective A hA U hSymm
  choose X hX using fun g => (hGauge g)
  refine ⟨X, hX, ?_⟩
  have hProd : ∀ g h : G, ∀ i : Fin d,
      twistedTensor A U (g * h) i =
        ((X h * X g : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((X h * X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    fun g h => gauge_product_intertwines A U X hX g h
  have hScalar : ∀ g h : G, ∃ c : ℂ,
      ((X h * X g : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
        c • (X (g * h) : Matrix (Fin D) (Fin D) ℂ) :=
    fun g h => gaugeEquiv_unique_up_to_scalar hA (hProd g h) (hX (g * h))
  choose ω hω using fun h g => hScalar g h
  refine ⟨ω, fun g h => ?_⟩
  rw [show (X h : Matrix (Fin D) (Fin D) ℂ) * (X g : Matrix (Fin D) (Fin D) ℂ) =
    ((X h * X g : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
    from (Matrix.GeneralLinearGroup.coe_mul (X h) (X g)).symm]
  exact hω h g

end VirtualRep

end MPSTensor
