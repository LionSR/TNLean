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
# Coordinates for multiplication on a trace quotient

Let G be the complex-bilinear two-site trace form and F a fixed section of its
coefficient quotient. The matrix C = G F carries these coordinates into the
trace-dual space. The positive Hermitian Gram matrix C† C is used only to invert
this section; it is distinct from the bilinear form G. Contracted three-site
trace data R then give multiplication coefficients (C† C)⁻¹ C† R.

This file establishes continuity of those coefficients and persistence of a
fixed section on a constant-rank neighborhood. Identifying the coefficients
with the quotient product is a separate algebraic step.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- Multiplication coordinates obtained by inverting the positive Hermitian
Gram matrix of a fixed section of the trace quotient. -/
noncomputable def traceQuotientProductCoordinates {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ)
    (R : Matrix (Fin d) (Fin r × Fin r) ℂ) :
    Matrix (Fin r) (Fin r × Fin r) ℂ :=
  ((G * F)ᴴ * (G * F))⁻¹ * (G * F)ᴴ * R

/-- Continuous two- and three-site trace data yield continuous multiplication
coordinates whenever the chosen section is injective. -/
theorem continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (R : T → Matrix (Fin d) (Fin r × Fin r) ℂ) (hR : Continuous R)
    (hInj : ∀ t, Function.Injective (G t * F).mulVec) :
    Continuous fun t => traceQuotientProductCoordinates (G t) F (R t) := by
  have hC : Continuous fun t => G t * F := hG.matrix_mul continuous_const
  have hGram : Continuous fun t => (G t * F)ᴴ * (G t * F) :=
    hC.matrix_conjTranspose.matrix_mul hC
  have hInv : Continuous fun t => ((G t * F)ᴴ * (G t * F))⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hUnit := (Matrix.PosDef.conjTranspose_mul_self _ (hInj t)).isUnit
    have hUnitDet := (Matrix.isUnit_iff_isUnit_det _).mp hUnit
    obtain ⟨u, hu⟩ := hUnitDet
    have hDetInv : ContinuousAt Ring.inverse ((G t * F)ᴴ * (G t * F)).det := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact (continuousAt_matrix_inv _ hDetInv).comp'
      (f := fun s : T => (G s * F)ᴴ * (G s * F)) hGram.continuousAt
  exact (hInv.matrix_mul hC.matrix_conjTranspose).matrix_mul hR

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

/-- A constant-rank two-site trace family and continuous contracted three-site
trace data admit continuous multiplication coordinates on a fixed local section. -/
theorem exists_open_continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hBase : Function.Injective (G t₀ * F).mulVec)
    (R : T → Matrix (Fin d) (Fin r × Fin r) ℂ) (hR : Continuous R) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F (R t)) S ∧
      ∀ t ∈ S, Function.Injective (G t * F).mulVec ∧
        LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  obtain ⟨S, hS, ht₀, hSection⟩ := exists_open_fixedSection_range G hG hRank t₀ F hBase
  refine ⟨S, hS, ht₀, ?_, hSection⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_traceQuotientProductCoordinates
    (fun t : S => G t) (hG.comp continuous_subtype_val) F
    (fun t : S => R t) (hR.comp continuous_subtype_val)
    (fun t => (hSection t t.property).1)

/-- Continuous trace data of constant rank admit locally continuous quotient
multiplication coordinates, with the base section supplied as a conclusion. -/
theorem exists_local_continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (R : Matrix (Fin d) (Fin r) ℂ → T → Matrix (Fin d) (Fin r × Fin r) ℂ)
    (hR : ∀ F, Continuous (R F)) :
    ∃ (F : Matrix (Fin d) (Fin r) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F (R F t)) S ∧
      ∀ t ∈ S, Function.Injective (G t * F).mulVec ∧
        LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  obtain ⟨F, hF⟩ := exists_fixedSection_of_rank (G t₀) (hRank t₀)
  obtain ⟨S, hS⟩ := exists_open_continuous_traceQuotientProductCoordinates
    G hG hRank t₀ F hF (R F) (hR F)
  exact ⟨F, S, hS⟩

end Matrix
