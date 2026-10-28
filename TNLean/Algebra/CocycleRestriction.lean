/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TNLean.Algebra.CocycleCohomology

/-!
# Restriction of scalar cohomology and exact extension from a subgroup

Pullback of `ℂˣ`-valued cocycles along a group homomorphism `f` represents
Mathlib's restriction map `groupCohomology.map f (scalarRepresentationRes f) 2`
on `H²(-, ℂˣ)`, for the trivial actions.  A subgroup cocycle class lies in the
range of restriction precisely when its chosen representative extends exactly to
an ambient cocycle. The proof extends
a subgroup cochain and adjusts the ambient representative by its coboundary.

This is standard supporting representative adjustment implicit in
arXiv:2502.20257, Proposition `prop:BI_psi`
(`Papers/2502.20257/main.tex:7042--7064`), not the full block-independence
criterion. We work with `ℂˣ` coefficients; no comparison with `U(1)` is asserted.
No normality, finiteness, transitivity, or cocycle normalization is required.
-/

open CategoryTheory

namespace TNLean.Algebra

open scoped ScalarCohomology

variable {G K : Type} [Group G] [Group K]

/-- Pullback preserves the cocycle equation. -/
theorem ScalarCocycle.isMulCocycle₂_comap {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) (f : K →* G) :
    groupCohomology.IsMulCocycle₂ (ω.comap f) := by
  apply (isMulCocycle₂_iff _).mpr
  intro a b c
  simpa only [ScalarCocycle.comap_apply, map_mul] using
    (isMulCocycle₂_iff _).mp hω (f a) (f b) (f c)

/-- Pullback preserves a coboundary ratio between arbitrary scalar cochains. -/
theorem isMulCoboundary₂_div_comap {ω₁ ω₂ : G × G → ℂˣ}
    (h : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂)) (f : K →* G) :
    groupCohomology.IsMulCoboundary₂
      ((ω₁ ∘ Prod.map f f) / (ω₂ ∘ Prod.map f f)) := by
  obtain ⟨φ, hφ⟩ := (isMulCoboundary₂_div_iff ω₁ ω₂).mp h
  apply (isMulCoboundary₂_div_iff _ _).mpr
  refine ⟨φ ∘ f, fun a b ↦ ?_⟩
  change ω₁ (f a, f b) = φ (f a) * φ (f b) * (φ (f (a * b)))⁻¹ * ω₂ (f a, f b)
  simpa only [map_mul] using hφ (f a) (f b)

/-- Multiplying a genuine cocycle by a cochain coboundary preserves its equation. -/
theorem ScalarCocycle.isMulCocycle₂_coboundary_mul {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) (φ : G → ℂˣ) :
    groupCohomology.IsMulCocycle₂ (fun p ↦ φ p.1 * φ p.2 * (φ (p.1 * p.2))⁻¹ * ω p) := by
  apply isMulCocycle₂_of_isMulCoboundary₂_div hω
  exact (isMulCoboundary₂_div_iff _ ω).mpr ⟨φ, fun _ _ ↦ rfl⟩

/-- Mathlib's restriction of cocycles along `f` sends the cocycle of `ω` to the cocycle of
its pullback `ω.comap f`. -/
theorem ScalarCocycle.mapCocycles₂_cocyclesOfIsMulCocycle₂ {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) (f : K →* G) :
    groupCohomology.mapCocycles₂ f (scalarRepresentationRes f)
        (groupCohomology.cocyclesOfIsMulCocycle₂ hω) =
      groupCohomology.cocyclesOfIsMulCocycle₂ (ScalarCocycle.isMulCocycle₂_comap hω f) :=
  rfl

/-- Mathlib's restriction map on `H²(-, ℂˣ)` sends the class of `ω` to the class of its
pullback `ω.comap f`. -/
theorem ScalarCocycle.map_H2π {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) (f : K →* G) :
    groupCohomology.map f (scalarRepresentationRes f) 2
        (groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω)) =
      groupCohomology.H2π _
        (groupCohomology.cocyclesOfIsMulCocycle₂ (ScalarCocycle.isMulCocycle₂_comap hω f)) := by
  rw [groupCohomology.H2π_comp_map_apply, ScalarCocycle.mapCocycles₂_cocyclesOfIsMulCocycle₂ hω]

/-- Exact representative extension is equivalent to extension of the class: the class of a
subgroup cocycle `ψ` lies in the range of Mathlib's restriction map
`H²(G, ℂˣ) → H²(H, ℂˣ)` precisely when `ψ` itself is the restriction of an ambient cocycle.

This is the supporting cochain adjustment implicit in arXiv:2502.20257,
Proposition `prop:BI_psi` (`main.tex:7042--7064`), for `ℂˣ` coefficients.
The subgroup is arbitrary, and the cocycles need not be normalized. -/
theorem ScalarCocycle.H2π_mem_range_map_subtype_iff (H : Subgroup G)
    {ψ : ScalarCocycle H} (hψ : groupCohomology.IsMulCocycle₂ ψ) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hψ) ∈
        Set.range (groupCohomology.map H.subtype (scalarRepresentationRes H.subtype) 2) ↔
      ∃ Ψ : ScalarCocycle G, groupCohomology.IsMulCocycle₂ Ψ ∧
        ∀ a b : H, Ψ ((a : G), (b : G)) = ψ (a, b) := by
  classical
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨ω, hω, rfl⟩ := ScalarCocycle.exists_H2π_eq q
    rw [ScalarCocycle.map_H2π hω] at hq
    have hB : groupCohomology.IsMulCoboundary₂ (ψ / ω.comap H.subtype) :=
      (H2π_eq_iff_isMulCoboundary₂_div hψ
        (ScalarCocycle.isMulCocycle₂_comap hω H.subtype)).mp hq.symm
    obtain ⟨φ, hφ⟩ := (isMulCoboundary₂_div_iff _ _).mp hB
    let Φ : G → ℂˣ := Function.extend Subtype.val φ (fun _ ↦ 1)
    have hΦ (a : H) : Φ (a : G) = φ a :=
      Subtype.val_injective.extend_apply φ (fun _ ↦ 1) a
    refine ⟨fun p ↦ Φ p.1 * Φ p.2 * (Φ (p.1 * p.2))⁻¹ * ω p,
      ScalarCocycle.isMulCocycle₂_coboundary_mul hω Φ, ?_⟩
    intro a b
    change Φ (a : G) * Φ (b : G) * (Φ ((a : G) * (b : G)))⁻¹ * ω ((a : G), (b : G)) = ψ (a, b)
    rw [hΦ a, hΦ b, ← Subgroup.coe_mul, hΦ (a * b)]
    exact (hφ a b).symm
  · rintro ⟨Ψ, hΨ, heq⟩
    refine ⟨groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hΨ), ?_⟩
    rw [ScalarCocycle.map_H2π hΨ]
    have hp : Ψ.comap H.subtype = ψ := funext fun p ↦ heq p.1 p.2
    subst hp
    rfl

end TNLean.Algebra
