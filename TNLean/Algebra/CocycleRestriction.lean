/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology

/-!
# Pullback of scalar cohomology and exact extension from a subgroup

Pullback descends to the existing quotient of genuine `ℂˣ`-valued cocycles.
A subgroup cocycle class lies in the range of restriction precisely when its
chosen representative extends exactly to an ambient cocycle. The proof extends
a subgroup cochain and adjusts the ambient representative by its coboundary.

This is standard supporting representative adjustment implicit in
arXiv:2502.20257, Proposition `prop:BI_psi`
(`Papers/2502.20257/main.tex:7042--7064`), not the full block-independence
criterion. We work with `ℂˣ` coefficients; no comparison with `U(1)` is asserted.
No normality, finiteness, transitivity, or cocycle normalization is required.
-/

namespace TNLean.Algebra

variable {G K : Type*} [Group G] [Group K]

/-- Pull back a scalar 2-cochain along a group homomorphism. -/
def ScalarCocycle.pullback (f : K →* G) (ω : ScalarCocycle G) : ScalarCocycle K :=
  fun a b ↦ ω (f a) (f b)

/-- Evaluate a pulled-back cochain by applying the homomorphism to both arguments. -/
@[simp]
theorem ScalarCocycle.pullback_apply (f : K →* G) (ω : ScalarCocycle G) (a b : K) :
    ω.pullback f a b = ω (f a) (f b) := rfl

/-- Pullback preserves the cocycle equation. -/
theorem ScalarCocycle.IsCocycle.pullback {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (f : K →* G) : (ω.pullback f).IsCocycle := by
  intro a b c
  simpa only [ScalarCocycle.pullback_apply, map_mul] using hω (f a) (f b) (f c)

/-- Precomposing the witnessing cochain makes pullback respect cohomology. -/
theorem ScalarCocycle.CohomologousTo.pullback {ω₁ ω₂ : ScalarCocycle G}
    (h : ω₁.CohomologousTo ω₂) (f : K →* G) :
    (ω₁.pullback f).CohomologousTo (ω₂.pullback f) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ ∘ f, fun a b ↦ ?_⟩
  simpa only [ScalarCocycle.pullback_apply, Function.comp_apply, map_mul] using hφ (f a) (f b)

/-- Multiplying a genuine cocycle by a cochain coboundary preserves its equation. -/
theorem ScalarCocycle.IsCocycle.coboundary_mul {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (φ : G → ℂˣ) :
    ScalarCocycle.IsCocycle (fun a b ↦ φ a * φ b * (φ (a * b))⁻¹ * ω a b) := by
  intro a b c
  calc
    _ = (φ a * φ b * φ c * (φ (a * (b * c)))⁻¹) *
        (ω a b * ω (a * b) c) := by simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (φ a * φ b * φ c * (φ (a * (b * c)))⁻¹) *
        (ω a (b * c) * ω b c) := by rw [hω a b c]
    _ = _ := by simp [mul_assoc, mul_comm, mul_left_comm]

/-- Contravariant pullback on the existing genuine-cocycle cohomology quotient. -/
def H2.pullback (f : K →* G) : H2 G → H2 K :=
  Quotient.map (fun ω ↦ ⟨ω.1.pullback f, ω.2.pullback f⟩)
    (fun _ _ h ↦ ScalarCocycle.CohomologousTo.pullback h f)

/-- Pullback of a class is represented by pullback of its cocycle. -/
@[simp]
theorem H2.pullback_mk (f : K →* G) (ω : ScalarCocycle G) (hω : ω.IsCocycle) :
    H2.pullback f (Quotient.mk _ ⟨ω, hω⟩) =
      Quotient.mk _ ⟨ω.pullback f, hω.pullback f⟩ := rfl

/-- Exact representative extension is equivalent to extension of the class.

This is the supporting cochain adjustment implicit in arXiv:2502.20257,
Proposition `prop:BI_psi` (`main.tex:7042--7064`), for `ℂˣ` coefficients.
The subgroup is arbitrary, and the cocycles need not be normalized. -/
theorem H2.mem_range_pullback_subtype_iff (H : Subgroup G)
    (ψ : ScalarCocycle H) (hψ : ψ.IsCocycle) :
    Quotient.mk _ ⟨ψ, hψ⟩ ∈ Set.range (H2.pullback H.subtype) ↔
      ∃ Ψ : ScalarCocycle G, Ψ.IsCocycle ∧ ∀ a b : H, Ψ (a : G) (b : G) = ψ a b := by
  classical
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | _ ω =>
      have hcoh : ψ.CohomologousTo (ω.1.pullback H.subtype) :=
        Quotient.exact hq.symm
      obtain ⟨φ, hφ⟩ := hcoh
      let Φ : G → ℂˣ := Function.extend Subtype.val φ (fun _ ↦ 1)
      have hΦ (a : H) : Φ (a : G) = φ a :=
        Subtype.val_injective.extend_apply φ (fun _ ↦ 1) a
      refine ⟨fun a b ↦ Φ a * Φ b * (Φ (a * b))⁻¹ * ω.1 a b,
        ω.2.coboundary_mul Φ, ?_⟩
      intro a b
      change Φ (a : G) * Φ (b : G) * (Φ ((a : G) * (b : G)))⁻¹ *
        ω.1 (a : G) (b : G) = ψ a b
      rw [hΦ a, hΦ b, ← Subgroup.coe_mul, hΦ (a * b)]
      exact (hφ a b).symm
  · rintro ⟨Ψ, hΨ, heq⟩
    refine ⟨Quotient.mk _ ⟨Ψ, hΨ⟩, ?_⟩
    apply Quotient.sound
    have hp : Ψ.pullback H.subtype = ψ := funext fun a ↦ funext fun b ↦ heq a b
    change (Ψ.pullback H.subtype).CohomologousTo ψ
    rw [hp]
    exact ScalarCocycle.CohomologousTo.refl ψ

end TNLean.Algebra
