/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.ContinuousMinimalRealization
import TNLean.MPS.Symmetry.ContinuousCanonicalNormalization

/-!
# Local continuous canonical realizations of periodic tensor rays

At a fixed positive minimal bond dimension, a continuous ambient tensor family
with pointwise injective realizations admits a local continuous unital realization
and a continuous normalized adjoint stationary density. The minimal representatives,
their gauges, and the scalar normalizations are not assumed continuous.

**Scope restriction (constant minimal dimension):** This is an auxiliary
construction for arXiv:1010.3732, Section II.F.2 and Appendix C, combined with
Wolf Theorems 6.3 and 6.11. The pointwise injective representatives have a fixed
positive bond dimension. Reconstruction through a change of minimal dimension
remains open; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder BigOperators Topology

namespace MPSTensor

/-- Local continuous canonical data for a continuous ambient family of periodic
rays with injective representatives of a fixed positive bond dimension. The
stationary density is positive semidefinite, trace one, and unique among all
trace-one adjoint fixed matrices. Auxiliary source context: arXiv:1010.3732,
Section II.F.2 and Appendix C; Wolf Theorems 6.3 and 6.11. -/
theorem exists_local_continuous_unitalTensor_of_samePositiveMpvRay
    {T : Type*} [TopologicalSpace T] {d D K : ℕ} [NeZero D]
    (B : T → MPSTensor d K) (hB : Continuous B)
    (A : T → MPSTensor d D) (hA : ∀ t, Kraus.IsInjective (A t))
    (hRay : ∀ t, SamePositiveMpvRay (B t) (A t)) (t₀ : T) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ (C : S → MPSTensor d D) (σ : S → Matrix (Fin D) (Fin D) ℂ),
        Continuous C ∧ Continuous σ ∧ ∀ t,
          Kraus.IsInjective (C t) ∧ Kraus.IsUnital (C t) ∧
          SamePositiveMpvRay (B t) (C t) ∧
          (σ t).PosSemidef ∧ Matrix.trace (σ t) = 1 ∧
          Kraus.adjointMap (C t) (σ t) = σ t ∧
          ∀ X : Matrix (Fin D) (Fin D) ℂ,
            Kraus.adjointMap (C t) X = X → Matrix.trace X = 1 → X = σ t := by
  obtain ⟨S, hS, ht₀, C, hC, hData⟩ :=
    exists_local_continuous_minimalTensor_of_samePositiveMpvRay B hB A hA hRay t₀
  obtain ⟨W, hW, hbase, L, ρ, r, σ, hL, hρ, hr, hσ, hNorm⟩ :=
    exists_local_continuous_canonicalNormalization_of_isInjective
      (fun t : S => C t) (continuousOn_iff_continuous_domRestrict.mp hC)
      ⟨t₀, ht₀⟩ (hData t₀ ht₀).2
  have hScale : ∀ t : W, (↑((Real.sqrt (r t))⁻¹) : ℂ) ≠ 0 := by
    intro t
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (hNorm t).1.2.2.1)
  have hGood : ∀ t : W,
      Kraus.IsInjective (L t) ∧ Kraus.IsUnital (L t) ∧
      SamePositiveMpvRay (B t) (L t) ∧
      (σ t).PosSemidef ∧ Matrix.trace (σ t) = 1 ∧
      Kraus.adjointMap (L t) (σ t) = σ t ∧
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        Kraus.adjointMap (L t) X = X → Matrix.trace X = 1 → X = σ t := by
    intro t
    exact ⟨isInjective_of_gaugeEquiv ((hData t t.val.property).2.smul (hScale t))
        (hNorm t).1.2.2.2.2.2.2,
      (hNorm t).1.2.2.2.2.2.1,
      (hData t t.val.property).1.trans
        (samePositiveMpvRay_of_smul_gaugeEquiv _ (hScale t) (hNorm t).1.2.2.2.2.2.2),
      (hNorm t).2⟩
  let V : Set T := Subtype.val '' W
  have hSub : V ⊆ S := by
    rintro t ⟨s, _, rfl⟩
    exact s.property
  let i : V → S := fun t => ⟨t.val, hSub t.property⟩
  have hiW : ∀ t, i t ∈ W := by
    rintro ⟨t, ⟨s, hs, rfl⟩⟩
    exact hs
  let j : V → W := fun t => ⟨i t, hiW t⟩
  have hi : Continuous i :=
    continuous_subtype_val.subtype_mk (fun t => hSub t.property)
  have hj : Continuous j := hi.subtype_mk hiW
  exact ⟨V, hS.isOpenMap_subtype_val W hW, ⟨⟨t₀, ht₀⟩, hbase, rfl⟩,
    L ∘ j, σ ∘ j, hL.comp hj, hσ.comp hj, fun t => hGood (j t)⟩

end MPSTensor
