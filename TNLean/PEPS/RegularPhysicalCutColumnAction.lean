/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularOpenRegion

/-!
# A physical operation on all boundary columns acts on the actual cut

If a physical matrix acts with the same scalar on every open-region boundary
column, it acts with that scalar on the coefficient matrix of the actual
bipartite contraction. The conclusion follows from the actual factorization
into the open-region matrix and the transpose of its complementary matrix.

Source: SCP10, arXiv:1001.3807, cut contraction in lines 1935–1957 and flux
measurement in Theorem 6.15, lines 2217–2267. No unitary or eigenstate
hypothesis on the global contraction is used.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

/-- A uniform eigenidentity on actual open columns passes to the actual physical
cut matrix. Source: SCP10, lines 1935–1957 and Theorem 6.15, lines 2217–2267. -/
theorem mul_regularPhysicalCutMatrix_eq_smul_of_openRegion_eigen
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (z : ℂ) (hQ : ∀ μ : RegionBoundaryConfig (groupBondTensor a) R,
      Q *ᵥ openRegionWeight (groupBondTensor a) R μ =
        z • openRegionWeight (groupBondTensor a) R μ) :
    Q * regularPhysicalCutMatrix a R = z • regularPhysicalCutMatrix a R := by
  classical
  let E := Fintype.equivFin {f : Edge Γ // IsRegionBoundaryEdge R f}
  have hQB : Q * regularOpenRegionMatrix a R E = z • regularOpenRegionMatrix a R E := by
    ext σ x
    exact congrFun (hQ (regularRegionBoundaryConfigEquiv a R E x)) σ
  rw [regularPhysicalCutMatrix_eq_mul_transpose a R E, ← Matrix.mul_assoc, hQB,
    Matrix.smul_mul]

/-- A conditional identity on every actual group-valued boundary column gives
that conditional identity on the actual physical cut. The numbering of boundary
labels and the indicator scalar are derived internally. Source: SCP10,
Theorem 6.15, lines 2217–2267, and joint measurement, lines 2380–2415. -/
theorem mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (P : Prop) [Decidable P]
    (hQ : ∀ θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G,
      Q *ᵥ openRegionWeight (groupBondTensor a) R
          (fun f => Fintype.equivFin G (θ f)) =
        if P then openRegionWeight (groupBondTensor a) R
          (fun f => Fintype.equivFin G (θ f)) else 0) :
    Q * regularPhysicalCutMatrix a R = if P then regularPhysicalCutMatrix a R else 0 := by
  classical
  let z : ℂ := if P then 1 else 0
  have haction : Q * regularPhysicalCutMatrix a R = z • regularPhysicalCutMatrix a R := by
    apply mul_regularPhysicalCutMatrix_eq_smul_of_openRegion_eigen
    intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    simpa only [θ, Equiv.apply_symm_apply, z, ite_smul, one_smul, zero_smul] using hQ θ
  simpa only [z, ite_smul, one_smul, zero_smul] using haction

end TNLean.PEPS
