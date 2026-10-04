/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularProjectorTwistedRegion
import TNLean.PEPS.RegularPhysicalUnitaryTransport

/-!
# Physical images of the actual canonical region cut

The canonical coefficients lie in the product of the local invariant ranges,
even when operators occur on crossing bonds. The original physical contraction
is obtained by applying the original site maps on the two sides of the cut.
Their positive local Gram factors cancel in the normalized reduced density.

Source: SCP10, arXiv:1001.3807, accessible virtual coordinates and the proof of
Theorem 6.9, local source lines 1765–1820 and 1935–1990. These are algebraic
transfer identities; no exterior routing or entropy conclusion is assumed.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The actual canonical twisted region is supported on the product of the
original local regular projectors. Source: SCP10, lines 1765–1820. -/
theorem regionPhysicalProductMatrix_mul_regularProjectorTwistedRegionMatrix
    (R : Finset V) (u : Edge Γ → G) :
    regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) *
      regularProjectorTwistedRegionMatrix R u = regularProjectorTwistedRegionMatrix R u := by
  classical
  ext α θ
  simp only [Matrix.mul_apply, regionPhysicalProductMatrix,
    regularProjectorTwistedRegionMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs with hb
  · simp only [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (w : {w : V // w ∈ R})
      (β : IncidentEdge Γ w.1 → G) =>
      regularLegProjector (IncidentEdge Γ w.1) (α w) β *
        regularLegProjector (IncidentEdge Γ w.1) β
          (regularTwistedLabels u w.1
            (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)))]
    apply Finset.prod_congr rfl
    intro w _
    exact isGIsometric_regularLegProjector.1.regularSiteMap_projector_coefficients
      (α w) _
  · simp only [mul_zero, Finset.sum_const_zero]

/-- The canonical coefficient matrix across a cut is the contraction of its two
actual projector regions, with each crossing group label summed once.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990. -/
noncomputable def regularProjectorTwistedCutMatrix (R : Finset V) (u : Edge Γ → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) ℂ :=
  fun α β => ∑ θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G,
    regularProjectorTwistedRegionMatrix R u α θ *
      regularProjectorTwistedRegionMatrix (Finset.univ \ R) u β
        (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f))

/-- The left physical rows of the canonical cut are in the genuine local
invariant range. Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem regionPhysicalProductMatrix_mul_regularProjectorTwistedCutMatrix
    (R : Finset V) (u : Edge Γ → G) :
    regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) *
      regularProjectorTwistedCutMatrix R u = regularProjectorTwistedCutMatrix R u := by
  classical
  ext α β
  simp only [Matrix.mul_apply, regularProjectorTwistedCutMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  exact congrArg (fun z => z * _) (congrFun (congrFun
    (regionPhysicalProductMatrix_mul_regularProjectorTwistedRegionMatrix R u) α) θ)

/-- The right physical rows of the canonical cut are likewise supported on the
local invariant ranges. Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem regularProjectorTwistedCutMatrix_mul_regionPhysicalProductMatrix_transpose
    (R : Finset V) (u : Edge Γ → G) :
    regularProjectorTwistedCutMatrix R u *
        (regionPhysicalProductMatrix (Finset.univ \ R)
          (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))).transpose =
      regularProjectorTwistedCutMatrix R u := by
  classical
  ext α β
  simp only [Matrix.mul_apply, regularProjectorTwistedCutMatrix, Finset.sum_mul,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  simp only [mul_assoc]
  simp_rw [mul_comm (regularProjectorTwistedRegionMatrix (Finset.univ \ R) u _ _)
    (regionPhysicalProductMatrix (Finset.univ \ R)
      (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) β _)]
  rw [← Finset.mul_sum]
  exact congrArg (fun z => _ * z) (congrFun (congrFun
    (regionPhysicalProductMatrix_mul_regularProjectorTwistedRegionMatrix
      (Finset.univ \ R) u) β) _)

variable {d : ℕ}

/-- The original physical cut is the image of the actual canonical cut under
its two product site maps. No tensor factorization is supplied as a hypothesis.
Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem regularPhysicalCutMatrix_eq_physicalImage_regularProjectorTwistedCutMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) (u : Edge Γ → G) :
    regularPhysicalCutMatrix (regularTwistedSite a u) R =
      regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) *
        regularProjectorTwistedCutMatrix R u *
        (regionPhysicalProductMatrix (Finset.univ \ R)
          (fun v => Matrix.of fun s α => a v α s)).transpose := by
  classical
  let B := regularProjectorTwistedRegionMatrix (G := G) R u
  let Q : Matrix (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R))
      ({f : Edge Γ // IsRegionBoundaryEdge R f} → G) ℂ :=
    fun β θ => regularProjectorTwistedRegionMatrix (Finset.univ \ R) u β
      (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f))
  let T := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let S := regionPhysicalProductMatrix (Finset.univ \ R)
    (fun v => Matrix.of fun s α => a v α s)
  have hC : B * Q.transpose = regularProjectorTwistedCutMatrix R u := rfl
  have hcut : regularPhysicalCutMatrix (regularTwistedSite a u) R =
      (T * B) * (S * Q).transpose := by
    ext σ τ
    rw [regularPhysicalCutMatrix,
      stateCoeff_eq_openRegionComplement_of_regularBonds (H := G)
        (groupBondTensor (regularTwistedSite a u)) R (fun _ => rfl)]
    rw [← Equiv.sum_comp (Equiv.piCongrRight
      (fun _ : {f : Edge Γ // IsRegionBoundaryEdge R f} => Fintype.equivFin G))]
    apply Finset.sum_congr rfl
    intro θ _
    have hR := congrFun (regionPhysicalMap_regularProjectorTwistedRegionMatrix
      a ha R u θ) σ
    have hS := congrFun (regionPhysicalMap_regularProjectorTwistedRegionMatrix
      a ha (Finset.univ \ R) u
        (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f))) τ
    exact congrArg₂ (· * ·) hR.symm hS.symm
  change _ = T * regularProjectorTwistedCutMatrix R u * S.transpose
  rw [hcut, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, ← hC]


private theorem supported_physicalImage_density
    {ι j α β : Type*} [Fintype ι] [Fintype j] [Fintype α] [Fintype β]
    (T : Matrix α ι ℂ) (S : Matrix β j ℂ) (P : Matrix ι ι ℂ)
    (Q : Matrix j j ℂ) (C : Matrix ι j ℂ) (cR cS : ℝ)
    (hcS : 0 < cS) (hT : T.conjTranspose * T = (cR : ℂ) • P)
    (hS : S.conjTranspose * S = (cS : ℂ) • Q)
    (hPC : P * C = C) (hCQ : C * Q.transpose = C) :
    let M := T * C * S.transpose
    M * M.conjTranspose = (cS : ℂ) • (T * (C * C.conjTranspose) * T.conjTranspose) ∧
      Matrix.trace (M * M.conjTranspose) =
        (cR : ℂ) * (cS : ℂ) * Matrix.trace (C * C.conjTranspose) ∧
      (Matrix.trace (M * M.conjTranspose))⁻¹ • (M * M.conjTranspose) =
        (cR : ℂ)⁻¹ • (T *
          ((Matrix.trace (C * C.conjTranspose))⁻¹ • (C * C.conjTranspose)) *
          T.conjTranspose) := by
  classical
  have hST : S.transpose * S.transpose.conjTranspose = (cS : ℂ) • Q.transpose := by
    simpa only [Matrix.transpose_mul,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hS
  have hinner : (C * S.transpose) * (C * S.transpose).conjTranspose =
      (cS : ℂ) • (C * C.conjTranspose) := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = (C * (S.transpose * S.transpose.conjTranspose)) * C.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hST, Matrix.mul_smul, hCQ, Matrix.smul_mul]
  have hτ : (T * C * S.transpose) * (T * C * S.transpose).conjTranspose =
      (cS : ℂ) • (T * (C * C.conjTranspose) * T.conjTranspose) := by
    calc
      _ = T * ((C * S.transpose) * (C * S.transpose).conjTranspose) * T.conjTranspose := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinner, Matrix.mul_smul, Matrix.smul_mul]
  have htr : Matrix.trace ((T * C * S.transpose) * (T * C * S.transpose).conjTranspose) =
      (cR : ℂ) * (cS : ℂ) * Matrix.trace (C * C.conjTranspose) := by
    rw [hτ, Matrix.trace_smul, Matrix.trace_mul_comm (T * (C * C.conjTranspose)),
      ← Matrix.mul_assoc, hT, Matrix.smul_mul,
      Matrix.trace_smul]
    simp only [← Matrix.mul_assoc, hPC, smul_eq_mul]
    ring
  refine ⟨hτ, htr, ?_⟩
  rw [htr, hτ]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_rev]
  have hc : (cS : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hcS)
  congr 1
  field_simp [hc]

/-- Coherent sums of actual twisted physical cuts have the normalized density
obtained from the canonical cut by the same supported physical embedding.
The positive factors and both support identities are derived from the local
G-isometry assumptions. Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem exists_positive_regularPhysicalCut_density_transfer
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) :
    ∃ cR cS : ℝ, 0 < cR ∧ 0 < cS ∧
      (regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)).conjTranspose *
          regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) =
        (cR : ℂ) • regionPhysicalProductMatrix R
          (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) ∧
      ∀ {I : Type*} [Fintype I] (u : I → Edge Γ → G) (μ : I → ℂ),
        let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R (u i)
        let M := ∑ i, μ i • regularPhysicalCutMatrix (regularTwistedSite a (u i)) R
        let T := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
        M * M.conjTranspose = (cS : ℂ) • (T * (C * C.conjTranspose) * T.conjTranspose) ∧
          Matrix.trace (M * M.conjTranspose) =
            (cR : ℂ) * (cS : ℂ) * Matrix.trace (C * C.conjTranspose) ∧
          (Matrix.trace (M * M.conjTranspose))⁻¹ • (M * M.conjTranspose) =
            (cR : ℂ)⁻¹ • (T *
              ((Matrix.trace (C * C.conjTranspose))⁻¹ • (C * C.conjTranspose)) *
              T.conjTranspose) := by
  classical
  obtain ⟨cR, hcR, hR⟩ := exists_positive_regionPhysicalProductMatrix_gram a ha R
  obtain ⟨cS, hcS, hS⟩ :=
    exists_positive_regionPhysicalProductMatrix_gram a ha (Finset.univ \ R)
  refine ⟨cR, cS, hcR, hcS, hR, ?_⟩
  intro I _ u μ
  dsimp only
  have hM : (∑ i, μ i • regularPhysicalCutMatrix (regularTwistedSite a (u i)) R) =
      regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) *
        (∑ i, μ i • regularProjectorTwistedCutMatrix R (u i)) *
        (regionPhysicalProductMatrix (Finset.univ \ R)
          (fun v => Matrix.of fun s α => a v α s)).transpose := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      regularPhysicalCutMatrix_eq_physicalImage_regularProjectorTwistedCutMatrix
        a (fun v => (ha v).1)]
  rw [hM]
  apply supported_physicalImage_density _ _ _ _ _ cR cS hcS hR hS
  · simp only [Matrix.mul_sum, Matrix.mul_smul,
      regionPhysicalProductMatrix_mul_regularProjectorTwistedCutMatrix]
  · simp only [Matrix.sum_mul, Matrix.smul_mul,
      regularProjectorTwistedCutMatrix_mul_regionPhysicalProductMatrix_transpose]

end TNLean.PEPS
