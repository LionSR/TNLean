/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StabilizerCocycleReconstruction

/-!
# L-symbols on a free transitive action

For a fixed three-cocycle, compatible scalar L-symbols on a free transitive
action are related by an action-tensor gauge. This is the trivial-stabilizer
case of arXiv:2203.12563, Section 4.2, and the uniqueness assertion used in
the four-block example of Section 6.
-/

namespace TNLean.Algebra.LSymbol

variable {G : Type} {X : Type*} [Group G] [MulAction G X]

/-- On a free transitive action, the action gauge relates any two L-symbols
compatible with the same three-cochain. This is the trivial-stabilizer case
of arXiv:2203.12563, Section 4.2, lines 740–761. -/
theorem actionGaugeEquiv_of_bijective_smul
    {L₁ L₂ : LSymbol G X} {ω : ScalarThreeCochain G}
    (h₁ : IsCompatible L₁ ω) (h₂ : IsCompatible L₂ ω)
    (x₀ : X) (hx : Function.Bijective (fun g : G ↦ g • x₀)) :
    ActionGaugeEquiv L₁ L₂ := by
  classical
  let e : G ≃ X := Equiv.ofBijective _ hx
  refine ⟨fun g x ↦ L₂ x₀ g (e.symm x) / L₁ x₀ g (e.symm x), ?_⟩
  funext x g h
  obtain ⟨k, rfl⟩ := hx.surjective x
  have he (k : G) : e.symm (k • x₀) = k := e.symm_apply_apply k
  simp only [gauge, ← mul_smul, he, mul_one]
  have hv (L : LSymbol G X) (hL : IsCompatible L ω) :
      L (k • x₀) g h = (L x₀ g (h * k) * L x₀ h k) /
        (ω g h k * L x₀ (g * h) k) := by
    apply (eq_div_iff_mul_eq').2
    calc
      _ = ω g h k * L (k • x₀) g h * L x₀ (g * h) k := by ac_rfl
      _ = _ := (hL x₀ g h k).symm
  rw [hv L₁ h₁, hv L₂ h₂]
  apply Units.ext
  push_cast
  field_simp

/-- The regular action admits the cocycle solution from arXiv:2203.12563,
Section 6, line 1888. The inverse reflects the compatibility convention
`eq:omega_and_Ls` of arXiv:2502.20257. -/
theorem isCompatible_regular {ω : ScalarThreeCochain G} (hω : ω.IsCocycle) :
    IsCompatible (fun x g h : G ↦ (ω g h x)⁻¹) ω := by
  intro x g h k
  have he := hω g h k x
  apply Units.ext
  have he' := congrArg Units.val he
  push_cast at he' ⊢
  field_simp
  simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using he'

end TNLean.Algebra.LSymbol
