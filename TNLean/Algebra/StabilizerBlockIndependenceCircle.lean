/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CircleCohomology
import TNLean.Algebra.StabilizerBlockIndependence

/-!
# Block independence and extension of the stabilizer class with circle coefficients

arXiv:2502.20257, Proposition `prop:BI_psi` (`Papers/2502.20257/main.tex:7042--7064`), states
the block-independence criterion with coefficients `U(1)`: block independence holds exactly when
the stabilizer class `[ψ] ∈ H²(H, U(1))` extends to `G`. The scalar criterion of
`TNLean.Algebra.StabilizerBlockIndependence` is stated with coefficients `ℂˣ`. This file
transports it to circle coefficients.

Restriction along a group homomorphism commutes with the coefficient inclusion
`U(1) → ℂˣ` on `H²`. Coefficient inclusion is injective for every group and, by the finite-group
comparison of `TNLean.Algebra.CircleCohomology`, surjective for a finite group. Hence, for a
finite ambient group, a circle class lies in the image of restriction exactly when its
complex-unit image does. Applied to the stabilizer cocycle, scalar block independence of the
induced L-symbol is equivalent to the `U(1)` class of the pointwise phase of `ψ` lying in the
image of `H²(G, U(1)) → H²(H, U(1))`. For a unit-modulus representative `ψ` that phase is `ψ`
itself.

The file also records that scalar block independence is invariant under joint scalar gauges,
which lets the criterion be applied to L-symbols in an arbitrary gauge.

**Scope restriction (finite discrete group):** the comparison of coefficients uses algebraic
group cohomology of a finite discrete group, not the sheaf-cohomology comparison invoked at
arXiv:2502.20257, line 1931; see `docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`.

## Main definitions

* `TNLean.Algebra.circleRepresentationRes`: restriction of the trivial circle representation
  along a group homomorphism, the coefficient map of Mathlib's restriction on `H²(-, U(1))`.

## Main results

* `TNLean.Algebra.circleToComplexUnits_map_comp_map_res`: restriction commutes with coefficient
  inclusion.
* `TNLean.Algebra.mem_range_map_circleRepresentationRes_iff`: for a finite ambient group, a
  circle class is a restriction exactly when its complex-unit image is.
* `TNLean.Algebra.LSymbol.isBlockIndependent_gauge_iff`: block independence is gauge invariant.
* `TNLean.Algebra.StabilizerRepresentatives.inducedLSymbol_isBlockIndependent_iff_circle`:
  `prop:BI_psi` with coefficients `U(1)` for the induced L-symbol.
-/

noncomputable section

open CategoryTheory

namespace TNLean.Algebra

open scoped ScalarCohomology

/-! ### Restriction with circle coefficients -/

section Restriction

variable {G S : Type} [Group G] [Group S]

/-- Restriction of the trivial circle representation of `G` along `f : S →* G` to the trivial
circle representation of `S`. This is the identity on `Additive Circle`, and it is the
coefficient map of Mathlib's restriction `groupCohomology.map f` on `H²(-, U(1))`, as
`scalarRepresentationRes` is for `ℂˣ`. -/
def circleRepresentationRes (f : S →* G) :
    Rep.res f (Rep.ofMulDistribMulAction G Circle) ⟶ Rep.ofMulDistribMulAction S Circle := by
  apply Rep.ofHom
  refine ⟨LinearMap.id, ?_⟩
  intro g
  rfl

/-- **Restriction commutes with coefficient inclusion.** Restricting a circle class along `f`
and then including the coefficients into `ℂˣ` is the same as including first and then
restricting. No finiteness is needed. -/
theorem circleToComplexUnits_map_comp_map_res (f : S →* G) :
    groupCohomology.map f (circleRepresentationRes f) 2 ≫
        groupCohomology.map (MonoidHom.id S) (circleToComplexUnitsRepHom S) 2 =
      groupCohomology.map (MonoidHom.id G) (circleToComplexUnitsRepHom G) 2 ≫
        groupCohomology.map f (scalarRepresentationRes f) 2 := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact groupCohomology.map_congr (by ext; rfl) (by ext; rfl) 2

/-- The elementwise form of `circleToComplexUnits_map_comp_map_res`. -/
theorem circleToComplexUnits_map_res_apply (f : S →* G)
    (c : groupCohomology.H2 (Rep.ofMulDistribMulAction G Circle)) :
    groupCohomology.map (MonoidHom.id S) (circleToComplexUnitsRepHom S) 2
        (groupCohomology.map f (circleRepresentationRes f) 2 c) =
      groupCohomology.map f (scalarRepresentationRes f) 2
        (groupCohomology.map (MonoidHom.id G) (circleToComplexUnitsRepHom G) 2 c) :=
  ConcreteCategory.congr_hom (circleToComplexUnits_map_comp_map_res f) c

/-- **Extension of circle classes is detected with complex-unit coefficients.** For a finite
group `G` and any homomorphism `f : S →* G`, a class in `H²(S, U(1))` lies in the image of
restriction from `H²(G, U(1))` exactly when its image in `H²(S, ℂˣ)` lies in the image of
restriction from `H²(G, ℂˣ)`.

Finiteness of `G` gives surjectivity of coefficient inclusion on `G`
(arXiv:2502.20257, line 1931, in the algebraic form of
`docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`); injectivity on `S` holds for
every group. -/
theorem mem_range_map_circleRepresentationRes_iff [Finite G] (f : S →* G)
    (c : groupCohomology.H2 (Rep.ofMulDistribMulAction S Circle)) :
    c ∈ Set.range (groupCohomology.map f (circleRepresentationRes f) 2) ↔
      groupCohomology.map (MonoidHom.id S) (circleToComplexUnitsRepHom S) 2 c ∈
        Set.range (groupCohomology.map f (scalarRepresentationRes f) 2) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (circleToComplexUnits_map_res_apply f a).symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := circleToComplexUnits_map_surjective G b
    refine ⟨a, circleToComplexUnits_map_injective S ?_⟩
    exact (circleToComplexUnits_map_res_apply f a).trans hb

end Restriction

/-! ### Gauge invariance of block independence -/

namespace LSymbol

variable {G : Type} {X : Type*} [Group G] [MulAction G X]

/-- **Scalar block independence is gauge invariant.** A joint scalar gauge of an L-symbol is
block independent after a further gauge exactly when the L-symbol itself is, since joint gauges
compose and invert (arXiv:2502.20257, `eq:Lsymbgauge` and `prop:technical01`). -/
theorem isBlockIndependent_gauge_iff (β : ScalarCocycle G) (γ : ActionTensorGauge G X)
    (L : LSymbol G X) : IsBlockIndependent (gauge β γ L) ↔ IsBlockIndependent L := by
  constructor
  · rintro ⟨β', γ', h⟩
    exact ⟨β * β', γ * γ', by rwa [gauge_comp] at h⟩
  · rintro ⟨β', γ', h⟩
    refine ⟨β⁻¹ * β', γ⁻¹ * γ', ?_⟩
    rwa [gauge_comp, mul_inv_cancel_left, mul_inv_cancel_left]

end LSymbol

/-! ### Block independence with circle coefficients -/

namespace StabilizerRepresentatives

variable {G : Type} {X : Type*} [Group G] [MulAction G X] {x₀ : X}

/-- **Block independence and extension of the stabilizer class, with coefficients `U(1)`.**
For a finite group `G`, scalar block independence of the L-symbol induced by a stabilizer
two-cocycle `ψ` is equivalent to the class in `H²(H, U(1))` of the pointwise phase of `ψ` lying
in the image of the restriction map `H²(G, U(1)) → H²(H, U(1))`, for `H` the stabilizer of the
basepoint. The class is never evaluated as a cochain, and `H` need not be normal.

This is the class form of arXiv:2502.20257, Proposition `prop:BI_psi`
(`main.tex:7042--7064`), with the coefficients of the source. -/
theorem inducedLSymbol_isBlockIndependent_iff_circle [Finite G]
    (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)}
    (hψ : groupCohomology.IsMulCocycle₂ ψ) :
    LSymbol.IsBlockIndependent (K.inducedLSymbol ψ) ↔
      groupCohomology.H2π _
          (ScalarCocycle.circlePhaseMathlibCocycle
            (groupCohomology.cocyclesOfIsMulCocycle₂ hψ)) ∈
        Set.range (groupCohomology.map (MulAction.stabilizer G x₀).subtype
          (circleRepresentationRes (MulAction.stabilizer G x₀).subtype) 2) := by
  rw [mem_range_map_circleRepresentationRes_iff, groupCohomology.H2π_comp_map_apply,
    ScalarCocycle.H2π_map_circlePhaseMathlibCocycle hψ,
    K.inducedLSymbol_isBlockIndependent_iff_H2π_mem_range_map_subtype hψ]

end StabilizerRepresentatives

end TNLean.Algebra
