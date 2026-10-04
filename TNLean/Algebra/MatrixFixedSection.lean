/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Fixed sections of constant-rank matrix families

A complex matrix G of rank r admits a fixed matrix F with r columns such that
G F is injective. For a continuous family G(t) of constant rank r, a section
that is injective at t₀ stays injective on an open neighborhood of t₀, where
G(t) F parametrizes the full range of G(t).
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- A rank-r matrix admits a fixed section on which it is injective. -/
theorem exists_fixedSection_of_rank {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (hRank : G.rank = r) :
    ∃ F : Matrix (Fin d) (Fin r) ℂ, Function.Injective (G * F).mulVec := by
  classical
  let f := G.mulVecLin
  let e : (Fin r → ℂ) ≃ₗ[ℂ] LinearMap.range f :=
    (Module.finBasisOfFinrankEq ℂ (LinearMap.range f) hRank).equivFun.symm
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let F := LinearMap.toMatrix' (g.comp e.toLinearMap)
  have hFormula : ∀ x, (G * F) *ᵥ x = (e x : Fin d → ℂ) := by
    intro x
    rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    exact congrArg Subtype.val (LinearMap.congr_fun hg (e x))
  refine ⟨F, ?_⟩
  intro x y hxy
  rw [hFormula, hFormula] at hxy
  exact e.injective (Subtype.val_injective hxy)

/-- A fixed section of a constant-rank matrix range remains an injective
surjective parametrization of that range on an open neighborhood. -/
theorem exists_open_fixedSection_range
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hBase : Function.Injective (G t₀ * F).mulVec) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∀ t ∈ S,
      Function.Injective (G t * F).mulVec ∧
      LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  have hC : Continuous fun t => G t * F := hG.matrix_mul continuous_const
  have hGram : Continuous fun t => (G t * F)ᴴ * (G t * F) :=
    hC.matrix_conjTranspose.matrix_mul hC
  let S := {t | IsUnit ((G t * F)ᴴ * (G t * F))}
  refine ⟨S, Units.isOpen.preimage hGram, ?_, ?_⟩
  · exact (Matrix.PosDef.conjTranspose_mul_self _ hBase).isUnit
  · intro t ht
    have hInj : Function.Injective (G t * F).mulVec := by
      intro x y hxy
      apply (mulVec_injective_iff_isUnit.mpr ht)
      simpa only [mulVec_mulVec] using congrArg ((G t * F)ᴴ *ᵥ ·) hxy
    refine ⟨hInj, ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · simpa only [mulVecLin_mul] using
        LinearMap.range_comp_le_range F.mulVecLin (G t).mulVecLin
    · change (G t * F).rank = (G t).rank
      rw [hRank]
      change Module.finrank ℂ (LinearMap.range (G t * F).mulVecLin) = r
      rw [LinearMap.finrank_range_of_inj hInj]
      simp

end Matrix
