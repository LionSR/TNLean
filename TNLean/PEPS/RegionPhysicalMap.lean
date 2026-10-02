/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.OpenRegionContraction
import Mathlib.Algebra.BigOperators.Ring.Finset
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Physical maps on an actual open-region contraction

A physical linear map at each vertex commutes with contraction of the internal
virtual bonds. The output space may depend on the vertex. In particular, one may
expose all incident virtual coordinates after applying the local inverse without
changing the physical dimensions of the original tensor.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Observation `obs:iso:accessible-virt`
and its concatenation argument,
`Papers/1001.3807/paper_v3.tex`, lines 1765–1820. These are identities of the
actual finite sums; no block Gram identity is assumed.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {In Mid Out : V → Type*}

/-- The product matrix of the vertex-dependent physical maps in a finite region.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def regionPhysicalProductMatrix (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ) :
    Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → In w.1) ℂ :=
  fun τ σ => ∏ w : {w : V // w ∈ R}, F w.1 (τ w) (σ w)

omit [Fintype V] in
/-- Composition of physical product matrices is composition at each vertex.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionPhysicalProductMatrix_mul [∀ v, Fintype (Mid v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (Mid v) ℂ)
    (L : (v : V) → Matrix (Mid v) (In v) ℂ) :
    regionPhysicalProductMatrix R F * regionPhysicalProductMatrix R L =
      regionPhysicalProductMatrix R (fun v => F v * L v) := by
  classical
  ext τ σ
  simp only [regionPhysicalProductMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (w : {w : V // w ∈ R}) (j : Mid w.1) =>
    F w.1 (τ w) j * L w.1 j (σ w))).symm

omit [Fintype V] [LinearOrder V] in
/-- Identity maps at every vertex give the identity on the region's physical space. -/
theorem regionPhysicalProductMatrix_one [∀ v, DecidableEq (Out v)] (R : Finset V) :
    regionPhysicalProductMatrix R (fun v => (1 : Matrix (Out v) (Out v) ℂ)) = 1 := by
  classical
  ext τ σ
  simp only [regionPhysicalProductMatrix, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

omit [Fintype V] [LinearOrder V] in
/-- The adjoint of a physical product matrix is the product of the local adjoints. -/
theorem regionPhysicalProductMatrix_conjTranspose (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ) :
    (regionPhysicalProductMatrix R F).conjTranspose =
      regionPhysicalProductMatrix R (fun v => (F v).conjTranspose) := by
  ext τ σ
  simp only [regionPhysicalProductMatrix, Matrix.conjTranspose_apply, star_prod]

omit [Fintype V] in
/-- Isometries at the vertices give an isometry on the physical region.
Source: SCP10, the physical changes of coordinates in Observation
`obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionPhysicalProductMatrix_isIsometry [∀ v, Fintype (Out v)]
    [∀ v, DecidableEq (In v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ)
    (hF : ∀ v, Matrix.IsIsometry (F v)) :
    Matrix.IsIsometry (regionPhysicalProductMatrix R F) := by
  change (regionPhysicalProductMatrix R F).conjTranspose *
    regionPhysicalProductMatrix R F = 1
  rw [regionPhysicalProductMatrix_conjTranspose, regionPhysicalProductMatrix_mul]
  change ∀ v, (F v).conjTranspose * F v = 1 at hF
  simpa only [hF] using (regionPhysicalProductMatrix_one (Out := In) R)

/-- Apply one physical map at every vertex of the region. The output dimensions
may vary with the vertex. Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def regionPhysicalMap [∀ v, Fintype (In v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ) :
    (((w : {w : V // w ∈ R}) → In w.1) → ℂ) →ₗ[ℂ]
      (((w : {w : V // w ∈ R}) → Out w.1) → ℂ) :=
  Matrix.mulVecLin (regionPhysicalProductMatrix R F)

omit [Fintype V] in
/-- The coefficient of the product physical map is its literal finite contraction. -/
theorem regionPhysicalMap_apply [∀ v, Fintype (In v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ)
    (ψ : ((w : {w : V // w ∈ R}) → In w.1) → ℂ)
    (τ : (w : {w : V // w ∈ R}) → Out w.1) :
    regionPhysicalMap R F ψ τ =
      ∑ σ : (w : {w : V // w ∈ R}) → In w.1,
        (∏ w : {w : V // w ∈ R}, F w.1 (τ w) (σ w)) * ψ σ := rfl

omit [Fintype V] in
/-- Composition of region physical maps is composition at each vertex.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionPhysicalMap_comp [∀ v, Fintype (In v)] [∀ v, Fintype (Mid v)]
    (R : Finset V) (F : (v : V) → Matrix (Out v) (Mid v) ℂ)
    (L : (v : V) → Matrix (Mid v) (In v) ℂ) :
    regionPhysicalMap R F ∘ₗ regionPhysicalMap R L =
      regionPhysicalMap R (fun v => F v * L v) := by
  simp only [regionPhysicalMap, ← Matrix.mulVecLin_mul, regionPhysicalProductMatrix_mul]

/-- Applying the physical product map to the actual open-region coefficient
transforms each local coefficient inside the internal-bond sum.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionPhysicalMap_openRegionWeight (A : Tensor Γ d) (R : Finset V)
    (F : (v : V) → Matrix (Out v) (Fin d) ℂ) (μ : RegionBoundaryConfig A R)
    (τ : (w : {w : V // w ∈ R}) → Out w.1) :
    regionPhysicalMap R F (openRegionWeight A R μ) τ =
      ∑ η : RegionIncidentConfig A R,
        if regionIncidentBoundaryLabel A R η = μ then
          ∏ w : {w : V // w ∈ R}, ∑ s : Fin d, F w.1 (τ w) s *
            A.component w.1
              (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) s
        else 0 := by
  classical
  simp only [regionPhysicalMap_apply, openRegionWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun η _ => ?_
  by_cases h : regionIncidentBoundaryLabel A R η = μ
  · simp only [h, ite_true, regionIncidentWeight, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun (w : {w : V // w ∈ R}) (s : Fin d) =>
      F w.1 (τ w) s * A.component w.1
        (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) s)).symm
  · simp [h]

end TNLean.PEPS
