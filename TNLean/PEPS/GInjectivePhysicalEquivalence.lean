/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectivePhysicalMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Invertible physical comparison of G-injective tensor maps

Two G-injective maps for the same virtual representation identify the same
invariant virtual space with their physical ranges. When these ranges are
finite-dimensional, their range comparison extends to an invertible map of a
common physical space. More generally, equal finite physical dimensions allow
an invertible comparison between different physical spaces.

These are local consequences of SCP10, arXiv:1001.3807, Definition 5.1,
lines 1278–1296. The comparison acts on physical coordinates; it is not a
virtual gauge relation inferred from equality of closed states.
-/

namespace TNLean.PEPS

variable {G W P Q : Type*} [Group G] [Finite G]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
variable [AddCommGroup Q] [Module ℂ Q]
variable {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P}

/-- Finite-dimensional physical ranges of two G-injective maps for the same
virtual representation are related by an ambient physical automorphism.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.exists_physicalEquiv {S : W →ₗ[ℂ] P}
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S) [Module.Finite ℂ T.range] :
    ∃ F : P ≃ₗ[ℂ] P, F.toLinearMap ∘ₗ T = S := by
  let _ := Fintype.ofFinite G
  obtain ⟨F, hF⟩ := Submodule.exists_linearEquiv_restrict_eq (hT.rangeEquiv hS)
  refine ⟨F, LinearMap.ext fun x => ?_⟩
  exact (hF (T.rangeRestrict x)).symm.trans (hT.rangeEquiv_apply hS x)

/-- Equal finite physical dimensions suffice for an invertible physical
comparison even when the ambient physical spaces differ.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.exists_physicalEquiv_of_finrank_eq {S : W →ₗ[ℂ] Q}
    [Module.Finite ℂ P] [Module.Finite ℂ Q]
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S)
    (hDim : Module.finrank ℂ P = Module.finrank ℂ Q) :
    ∃ F : P ≃ₗ[ℂ] Q, F.toLinearMap ∘ₗ T = S := by
  let E := LinearEquiv.ofFinrankEq P Q hDim
  obtain ⟨L, hL⟩ := hT.exists_physicalEquiv (hS.comp_equiv E.symm)
  refine ⟨L.trans E, LinearMap.ext fun x => ?_⟩
  have h := congrArg E (LinearMap.congr_fun hL x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using h

end TNLean.PEPS
