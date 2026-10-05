/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularCanonicalRegionProjector
import TNLean.PEPS.RegularPhysicalUnitaryTransport

/-!
# Actual regional range projectors through regular G-isometries

The original regional range is the image of the canonical regular range under
the product of the original site maps. The positive Gram identity derived
from local G-isometry transports its orthogonal projector and gives an exact
intertwining, without surjectivity onto the physical space.
Source: SCP10, arXiv:1001.3807, Theorem 6.12, lines 2131–2153.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- The actual physical regional range is the product-site image of the
actual canonical regular regional range. -/
theorem regularProjectorOpenRegionRange_map_physical
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) :
    (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) R).mulVecLin.range.map
        (regionPhysicalMap R (fun v => Matrix.of fun s α => a v α s)) =
      regionGroundSpace (groupBondTensor a) R := by
  classical
  rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp, regionGroundSpace_eq_span]
  congr 1
  ext ψ
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨fun e => Fintype.equivFin G (θ e), ?_⟩
    exact (regionPhysicalMap_regularProjectorOpenRegionMatrix a ha R θ).symm
  · rintro ⟨μ, rfl⟩
    let θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G :=
      fun e => (Fintype.equivFin G).symm (μ e)
    refine ⟨θ, ?_⟩
    have h := regionPhysicalMap_regularProjectorOpenRegionMatrix a ha R θ
    have hμ : (fun e => Fintype.equivFin G (θ e)) = μ := by
      funext e
      exact Equiv.apply_symm_apply (Fintype.equivFin G) (μ e)
    rw [hμ] at h
    change regionPhysicalMap R (fun v => Matrix.of fun s α => a v α s)
      ((regularProjectorOpenRegionMatrix R).col θ) = _
    have hcol : (regularProjectorOpenRegionMatrix R).col θ =
        fun α => regularProjectorOpenRegionMatrix R α θ := by
      funext α
      rfl
    rw [hcol]
    exact h

/-- The canonical regional range projector is supported on the product of
its local regular invariant subspaces. -/
theorem regularLocalProjector_mul_regularCanonicalRegionRangeProjector (R : Finset V) :
    regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) *
      regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R =
        regularCanonicalRegionRangeProjector R := by
  apply matrix_mul_eq_right_of_fixes_range
  intro f hf
  rw [regularCanonicalRegionRangeProjector, range_coordinateRangeProjector] at hf
  have hleft := (mem_regularProjectorOpenRegionRange_iff R f).mp hf |>.1
  funext α
  simpa only [regionPhysicalProductMatrix, Matrix.mulVec, dotProduct, mul_comm] using
    sum_regularRegionProjectorProduct_eq R f hleft α

/-- Actual regular G-isometry intertwines the physical orthogonal regional
range projector with the canonical regular one. The regional Gram identity
is derived from the local tensors. -/
theorem regularIsometric_regionRangeProjector_intertwine
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) :
    coordinateRangeProjector (regionGroundSpace (groupBondTensor a) R) *
        regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) =
      regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) *
        regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R := by
  classical
  let A := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let E := regionPhysicalProductMatrix R
    (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))
  let Q := regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R
  obtain ⟨c, hc, hA⟩ := exists_positive_regionPhysicalProductMatrix_gram a ha R
  have hA' : Aᴴ * A = (c : ℂ) • E := hA
  have hEQ : E * Q = Q := regularLocalProjector_mul_regularCanonicalRegionRangeProjector R
  have hQ : IsStarProjection Q := coordinateRangeProjector_isStarProjection _
  have hE : Eᴴ = E := by
    let : Invertible (c : ℂ) := invertibleOfNonzero
      (Complex.ofReal_ne_zero.mpr hc.ne')
    have hgram : ((c : ℂ) • E).IsHermitian := by
      rw [← hA']
      exact Matrix.isHermitian_conjTranspose_mul_self A
    exact (hgram.of_smul (show IsSelfAdjoint (c : ℂ) by
      change star (c : ℂ) = (c : ℂ)
      simp)).eq
  have hQadj : Qᴴ = Q := hQ.isSelfAdjoint.star_eq
  have hQE : Q * E = Q := by
    have h := congrArg Matrix.conjTranspose hEQ
    simpa only [Matrix.conjTranspose_mul, hE, hQadj] using h
  have hT := isStarProjection_smul_mul_mul_conjTranspose_of_gram A hc.ne' hA' hQ hEQ
  have hTrange : (Matrix.mulVecLin ((c : ℂ)⁻¹ • (A * Q * Aᴴ))).range =
      regionGroundSpace (groupBondTensor a) R := by
    rw [range_smul_mul_mul_conjTranspose_of_gram A hc.ne' hA' hQ hQE]
    change (coordinateRangeProjector _).mulVecLin.range.map _ = _
    rw [range_coordinateRangeProjector]
    exact regularProjectorOpenRegionRange_map_physical a (fun v => (ha v).toIsGInjective) R
  rw [← eq_coordinateRangeProjector_of_range hT _ hTrange]
  exact smul_mul_mul_conjTranspose_mul_of_gram A hc.ne' hA' hQE

end TNLean.PEPS
