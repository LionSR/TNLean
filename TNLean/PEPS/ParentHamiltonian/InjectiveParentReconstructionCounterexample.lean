/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.VirtualBondGroundSpace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.Order

/-!
# A nondegenerate counterexample to bare injective parent transport

Place the injective map `z ↦ (z, 0)` at both endpoints of a bond of
positive dimension one. The virtual Bell space is the entire
one-dimensional two-endpoint space, so its canonical parent is zero.
Bare inverse-adjoint transport is therefore zero on the four-dimensional
physical two-site space and annihilates a vector outside the site-map image.

**Local fix (physical reconstruction):** This disproves the exact-kernel
assertion following CPGSV21, arXiv:2011.12127,
equation `eq:4:deformed-parent-1`, local source lines 2031–2037, for
rectangular injective site maps. The corrected positive interaction is
separate, in `InjectiveRegionParentTransport`; the source correction is
recorded in `docs/paper-gaps/cpgsv21_injective_parent_reconstruction.tex`.
-/

open scoped BigOperators Kronecker Matrix ComplexOrder

namespace TNLean.PEPS.InjectiveParentReconstructionCounterexample

/-- The bond is the nonzero one-dimensional virtual space.
Source: the example in the reconstruction correction to CPGSV21,
`eq:4:deformed-parent-1`, lines 2031–2037. -/
abbrev bondDimension : ℕ := 1

/-- The site tensor is the injective inclusion of the first physical coordinate.
Source: the reconstruction correction to CPGSV21, lines 2031–2037. -/
def siteEmbedding : Matrix (Fin 2) (Fin bondDimension) ℂ :=
  fun i _ => if i = 0 then 1 else 0

/-- A genuine left inverse reads the first physical coordinate.
Source: the site inverse in CPGSV21, lines 2031–2037. -/
def siteLeftInverse : Matrix (Fin bondDimension) (Fin 2) ℂ :=
  fun _ i => if i = 0 then 1 else 0

/-- The actual product of the two site tensors on the endpoint spaces.
Source: CPGSV21, `eq:4:peps-as-peps`, lines 2017–2028. -/
def twoSiteEmbedding :
    Matrix (Fin 2 × Fin 2) (Fin bondDimension × Fin bondDimension) ℂ :=
  siteEmbedding ⊗ₖ siteEmbedding

/-- The product of the two site left inverses.
Source: the inverse-adjoint deformation in CPGSV21, lines 2031–2037. -/
def twoSiteLeftInverse :
    Matrix (Fin bondDimension × Fin bondDimension) (Fin 2 × Fin 2) ℂ :=
  siteLeftInverse ⊗ₖ siteLeftInverse

/-- The dimension-one Bell vector, in its actual two-endpoint coordinates.
Source: the virtual Bell pair of CPGSV21, lines 2017–2028. -/
def bellVector : Fin bondDimension × Fin bondDimension → ℂ :=
  fun p => virtualBondBell (fun _ : Unit => bondDimension) () p

/-- The virtual Bell parent is zero because its Bell line is the whole space.
Source: the virtual interaction preceding CPGSV21,
`eq:4:deformed-parent-1`, lines 2031–2037. -/
def virtualInteraction :
    Matrix (Fin bondDimension × Fin bondDimension)
      (Fin bondDimension × Fin bondDimension) ℂ := 0

/-- The bare printed inverse-adjoint transport, without physical reconstruction.
Source: CPGSV21, `eq:4:deformed-parent-1`, lines 2031–2037. -/
def barePhysicalInteraction : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  twoSiteLeftInverse.conjTranspose * virtualInteraction * twoSiteLeftInverse

/-- A physical basis vector outside the product-site image.
Source: the rectangular-map counterexample to CPGSV21, lines 2031–2037. -/
def unusedPhysicalVector : Fin 2 × Fin 2 → ℂ := Pi.single (1, 0) 1

/-- The virtual dimension in this example is strictly positive. -/
theorem bondDimension_pos : 0 < bondDimension := by decide

/-- The site map has an actual left inverse. -/
theorem siteLeftInverse_mul_siteEmbedding : siteLeftInverse * siteEmbedding = 1 := by
  ext i j
  simp [siteLeftInverse, siteEmbedding, Matrix.mul_apply, Matrix.one_apply,
    bondDimension, Subsingleton.elim i j]

/-- The actual two-site product also has its product left inverse. -/
theorem twoSiteLeftInverse_mul_twoSiteEmbedding : twoSiteLeftInverse * twoSiteEmbedding = 1 := by
  rw [twoSiteLeftInverse, twoSiteEmbedding, ← Matrix.mul_kronecker_mul,
    siteLeftInverse_mul_siteEmbedding, Matrix.one_kronecker_one]

private theorem injective_mulVec_of_leftInverse {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (T : Matrix J I ℂ) (L : Matrix I J ℂ) (h : L * T = 1) :
    Function.Injective (Matrix.mulVecLin T) := by
  have hleft : Function.LeftInverse (Matrix.mulVecLin L) (Matrix.mulVecLin T) := by
    intro x
    change L *ᵥ (T *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  exact hleft.injective

/-- Neither site map in the example is vacuously injective. -/
theorem siteEmbedding_injective : Function.Injective (Matrix.mulVecLin siteEmbedding) :=
  injective_mulVec_of_leftInverse _ _ siteLeftInverse_mul_siteEmbedding

/-- The actual two-site physical product map is injective. -/
theorem twoSiteEmbedding_injective : Function.Injective (Matrix.mulVecLin twoSiteEmbedding) :=
  injective_mulVec_of_leftInverse _ _ twoSiteLeftInverse_mul_twoSiteEmbedding

/-- The dimension-one Bell vector is the nonzero scalar vacuum on its endpoint pair. -/
theorem bellVector_eq_one : bellVector = 1 := by
  funext p
  simp [bellVector, virtualBondBell, bondDimension, Subsingleton.elim p.1 p.2]

/-- The virtual interaction is a genuine positive Bell parent. -/
theorem virtualInteraction_posSemidef : virtualInteraction.PosSemidef := Matrix.PosSemidef.zero

/-- Its kernel is exactly the Bell line, which is one-dimensional here. -/
theorem ker_virtualInteraction_eq_bellSpan :
    (Matrix.mulVecLin virtualInteraction).ker = Submodule.span ℂ {bellVector} := by
  rw [virtualInteraction, Matrix.mulVecLin_zero, LinearMap.ker_zero]
  apply le_antisymm
  · intro x _
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x (0, 0), funext fun p => ?_⟩
    have hp : p = (0, 0) := Subsingleton.elim _ _
    subst p
    simp [bellVector_eq_one]
  · exact le_top

/-- Bare inverse-adjoint transport is zero on the whole physical space. -/
theorem barePhysicalInteraction_eq_zero : barePhysicalInteraction = 0 := by
  simp [barePhysicalInteraction, virtualInteraction]

/-- The bare transported interaction is positive, despite its excessive kernel. -/
theorem barePhysicalInteraction_posSemidef : barePhysicalInteraction.PosSemidef := by
  rw [barePhysicalInteraction_eq_zero]
  exact Matrix.PosSemidef.zero

/-- Every product-site image has zero coefficient at the unused physical coordinate. -/
theorem twoSiteEmbedding_mulVec_unused (x : Fin bondDimension × Fin bondDimension → ℂ) :
    (twoSiteEmbedding *ᵥ x) (1, 0) = 0 := by
  simp [Matrix.mulVec, dotProduct, twoSiteEmbedding, siteEmbedding]

/-- The unused vector does not belong to the actual two-site PEPS image. -/
theorem unusedPhysicalVector_not_mem_range :
    unusedPhysicalVector ∉ (Matrix.mulVecLin twoSiteEmbedding).range := by
  rintro ⟨x, hx⟩
  have h := congrFun hx (1, 0)
  rw [Matrix.mulVecLin_apply, twoSiteEmbedding_mulVec_unused] at h
  simp [unusedPhysicalVector] at h

/-- Nevertheless the bare transported interaction annihilates the unused vector. -/
theorem unusedPhysicalVector_mem_bareKernel :
    unusedPhysicalVector ∈ (Matrix.mulVecLin barePhysicalInteraction).ker := by
  rw [barePhysicalInteraction_eq_zero, Matrix.mulVecLin_zero, LinearMap.ker_zero]
  trivial

/-- Positive bonds and injective site maps do not make the bare printed
transport have the exact regional physical kernel.
Source: counterexample to CPGSV21, `eq:4:deformed-parent-1`, lines 2031–2037. -/
theorem bareKernel_ne_productSiteRange :
    (Matrix.mulVecLin barePhysicalInteraction).ker ≠
      (Matrix.mulVecLin twoSiteEmbedding).range := by
  intro h
  exact unusedPhysicalVector_not_mem_range (h ▸ unusedPhysicalVector_mem_bareKernel)

/-- The intended physical PEPS range is one-dimensional. -/
theorem finrank_productSiteRange :
    Module.finrank ℂ (Matrix.mulVecLin twoSiteEmbedding).range = 1 := by
  rw [LinearMap.finrank_range_of_inj twoSiteEmbedding_injective, Module.finrank_pi]
  simp [bondDimension]

/-- The bare interaction instead has a four-dimensional physical kernel. -/
theorem finrank_bareKernel :
    Module.finrank ℂ (Matrix.mulVecLin barePhysicalInteraction).ker = 4 := by
  rw [barePhysicalInteraction_eq_zero, Matrix.mulVecLin_zero, LinearMap.ker_zero,
    finrank_top, Module.finrank_pi]
  simp

end TNLean.PEPS.InjectiveParentReconstructionCounterexample
