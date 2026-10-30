/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleRestriction
import TNLean.Algebra.StabilizerCocycleExtension

/-!
# Scalar block independence and extension of the stabilizer class

The converse calculation in arXiv:2502.20257, Proposition `prop:BI_psi`
(`Papers/2502.20257/main.tex:7042–7064`), for the scalar L-symbol induced by
a stabilizer cocycle. A trivializing joint gauge forces its fusion cochain
to be a genuine two-cocycle. Its inverse, multiplied by the coboundary of
the action gauge at the basepoint, extends the stabilizer cocycle exactly.
Together with the forward calculation and Mathlib's restriction map, this
gives the scalar block-independence criterion on actual cohomology classes.

The source uses forward gauges expressing the L-symbol as a gauge of one.
Our witnesses trivialize the L-symbol, so both gauges must be inverted in
the source's extension formula. No normalization of either gauge or cocycle,
and no normality or finiteness of the stabilizer, is assumed.

**Scope restriction (scalar L-symbols):** The coefficients are `ℂˣ`. This
does not identify scalar block independence with the tensor predicate for
an MPS–MPU pair, or assert naturality of a comparison with `U(1)` coefficients.
See `docs/paper-gaps/fbc25_mpu_action_stabilizer_source_audit.tex`.
-/

open scoped TNLean.Algebra.ScalarCohomology

namespace TNLean.Algebra

variable {G : Type} {X : Type*} [Group G] [MulAction G X] {x₀ : X}

namespace LSymbol

/-- A fusion cochain in an actual trivializing gauge of a nonanomalous
compatible L-symbol is a two-cocycle. This derives the assertion at
arXiv:2502.20257, `prop:BI_psi`, line 7060, from compatibility. -/
theorem isMulCocycle₂_of_isTrivial_gauge (x₀ : X)
    {L : LSymbol G X} (hL : IsCompatible L (fun _ _ _ ↦ 1))
    {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    (htriv : IsTrivial (gauge β γ L)) : groupCohomology.IsMulCocycle₂ β := by
  apply (isMulCocycle₂_iff _).mpr
  intro g h k
  change ∀ x g h, gauge β γ L x g h = 1 at htriv
  have hc := (hL.gauge β γ) x₀ g h k
  have hd : β (g, h * k) * β (h, k) / (β (g, h) * β (g * h, k)) = 1 := by
    simpa only [htriv, ScalarThreeCochain.fusionGauge, ScalarThreeCochain.coboundary,
      mul_one, one_mul] using hc.symm
  exact (div_eq_one.mp hd).symm

/-- The exact ambient extension cochain constructed from trivializing gauges,
the reciprocal-gauge version of arXiv:2502.20257, `prop:BI_psi`, line 7062:
`Ψ(g,h) = γ(g,x₀) γ(h,x₀) γ(gh,x₀)⁻¹ β(g,h)⁻¹`. -/
def basepointExtension (x₀ : X) (β : ScalarCocycle G) (γ : ActionTensorGauge G X) :
    ScalarCocycle G :=
  fun p ↦ γ p.1 x₀ * γ p.2 x₀ * (γ (p.1 * p.2) x₀)⁻¹ * (β p)⁻¹

/-- The cochain constructed from actual trivializing gauges is a cocycle,
without any normalization, as in arXiv:2502.20257, `prop:BI_psi`, line 7064. -/
theorem basepointExtension_isMulCocycle₂ (x₀ : X)
    {L : LSymbol G X} (hL : IsCompatible L (fun _ _ _ ↦ 1))
    {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    (htriv : IsTrivial (gauge β γ L)) :
    groupCohomology.IsMulCocycle₂ (basepointExtension x₀ β γ) := by
  have hβ := (isMulCocycle₂_iff _).mp (isMulCocycle₂_of_isTrivial_gauge x₀ hL htriv)
  have hi : groupCohomology.IsMulCocycle₂ β⁻¹ := by
    apply (isMulCocycle₂_iff _).mpr
    intro g h k
    simpa only [Pi.inv_apply, mul_inv] using congrArg Inv.inv (hβ g h k)
  exact ScalarCocycle.isMulCocycle₂_coboundary_mul hi (fun g ↦ γ g x₀)

end LSymbol

namespace StabilizerRepresentatives

/-- The extension extracted from a trivializing gauge restricts literally to
the chosen stabilizer representative. This is the basepoint calculation of
arXiv:2502.20257, `prop:BI_psi`, line 7064, in the trivializing convention. -/
theorem basepointExtension_restrict (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)}
    {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    (htriv : LSymbol.IsTrivial (LSymbol.gauge β γ (K.inducedLSymbol ψ)))
    (a b : MulAction.stabilizer G x₀) :
    LSymbol.basepointExtension x₀ β γ ((a : G), (b : G)) = ψ (a, b) := by
  have hb : (b : G) • x₀ = x₀ := MulAction.mem_stabilizer_iff.mp b.property
  have ht := htriv x₀ (a : G) (b : G)
  rw [LSymbol.gauge, K.inducedLSymbol_base, hb] at ht
  apply (mul_left_cancel (a :=
    γ ((a : G) * (b : G)) x₀ * β ((a : G), (b : G)) / (γ (a : G) x₀ * γ (b : G) x₀)))
  rw [ht]
  dsimp only [LSymbol.basepointExtension]
  (apply Units.ext; push_cast; field_simp)

/-- Actual trivializing gauges produce an exact cocycle extension of the
stabilizer representative, the converse scalar calculation in
arXiv:2502.20257, `prop:BI_psi`, lines 7057–7064. -/
theorem exists_extension_of_inducedLSymbol_hasTrivialGauge
    (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)}
    (hψ : groupCohomology.IsMulCocycle₂ ψ)
    (hL : LSymbol.HasTrivialGauge (K.inducedLSymbol ψ)) :
    ∃ Ψ : ScalarCocycle G, groupCohomology.IsMulCocycle₂ Ψ ∧
      ∀ a b : MulAction.stabilizer G x₀, Ψ ((a : G), (b : G)) = ψ (a, b) := by
  obtain ⟨β, γ, htriv⟩ := hL
  exact ⟨LSymbol.basepointExtension x₀ β γ,
    LSymbol.basepointExtension_isMulCocycle₂ x₀ (K.inducedLSymbol_isCompatible hψ) htriv,
    K.basepointExtension_restrict htriv⟩

/-- Scalar block independence of the induced L-symbol is equivalent to exact
extension of the chosen stabilizer cocycle representative. This is the scalar
representative form of arXiv:2502.20257, `prop:BI_psi`, lines 7042–7064. -/
theorem inducedLSymbol_isBlockIndependent_iff_exists_extension
    (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)}
    (hψ : groupCohomology.IsMulCocycle₂ ψ) :
    LSymbol.IsBlockIndependent (K.inducedLSymbol ψ) ↔
      ∃ Ψ : ScalarCocycle G, groupCohomology.IsMulCocycle₂ Ψ ∧
        ∀ a b : MulAction.stabilizer G x₀, Ψ ((a : G), (b : G)) = ψ (a, b) := by
  let : Nonempty X := ⟨x₀⟩
  constructor
  · intro hL
    exact K.exists_extension_of_inducedLSymbol_hasTrivialGauge hψ
      (hL.hasTrivialGauge (K.inducedLSymbol_isCompatible hψ))
  · rintro ⟨Ψ, hΨ, hext⟩
    exact (K.inducedLSymbol_hasTrivialGauge_of_extension hΨ hext).hasBlockConstantGauge
      |>.isBlockIndependent

/-- Scalar block independence is equivalent to the stabilizer class lying in
the image of the actual restriction map `H²(G, ℂˣ) → H²(Stab(x₀), ℂˣ)`.
This is the scalar class form of arXiv:2502.20257, `prop:BI_psi`, lines
7042–7064; the class is never evaluated as a cochain. -/
theorem inducedLSymbol_isBlockIndependent_iff_H2π_mem_range_map_subtype
    (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)}
    (hψ : groupCohomology.IsMulCocycle₂ ψ) :
    LSymbol.IsBlockIndependent (K.inducedLSymbol ψ) ↔
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hψ) ∈
        Set.range (groupCohomology.map (MulAction.stabilizer G x₀).subtype
          (scalarRepresentationRes (MulAction.stabilizer G x₀).subtype) 2) := by
  rw [K.inducedLSymbol_isBlockIndependent_iff_exists_extension hψ,
    ScalarCocycle.H2π_mem_range_map_subtype_iff _ hψ]

end StabilizerRepresentatives

end TNLean.Algebra
