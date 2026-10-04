/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import TNLean.PEPS.RegularOpenRegion

/-!
# Coherent local operations and actual global contractions

An identity on every open boundary column passes through the native cut sum.
When the output is a finite coherent sum and all summands have the same exterior
site tensors as the input, the identity extends by the complementary physical
identity to the corresponding coherent sum of actual globally contracted states.
The coefficients may be arbitrary, and unitarity is not needed for this linear
contraction identity.

Source: SCP10, arXiv:1001.3807, the actual cut contraction in lines 1935–1957
and the coherent flux-pair creation in Theorem 6.17, lines 2304–2339.
These are auxiliary contraction identities; no energy or parent-Hamiltonian
membership statement is asserted.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {X I : Type*} [Fintype X] [Nonempty X] [Fintype I]

omit [Nonempty X] in
/-- Equal site tensors on a region give equal actual open-region coefficients.
Source: SCP10, the finite cut contraction, lines 1935–1957. -/
theorem openRegionWeight_groupBondTensor_congr_on (R : Finset V)
    (a b : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (hab : ∀ v ∈ R, a v = b v)
    (μ : {f : Edge Γ // IsRegionBoundaryEdge R f} → Fin (Fintype.card X)) :
    openRegionWeight (groupBondTensor a) R μ =
      openRegionWeight (groupBondTensor b) R μ := by
  funext σ
  unfold openRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  unfold regionIncidentWeight
  apply Finset.prod_congr rfl
  intro v _
  exact congrFun (congrFun (hab v v.2) _) _

/-- A finite coherent identity on every native boundary column gives the same
identity between actual globally contracted states when the exterior tensors agree.
Source: SCP10, lines 1935–1957 and Theorem 6.17, lines 2304–2339. -/
theorem regionLocalTerm_mulVec_stateCoeff_sum_of_openColumns (R : Finset V)
    (a : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (b : I → (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (c : I → ℂ)
    (W : Matrix ({v : V // v ∈ R} → Fin d) ({v : V // v ∈ R} → Fin d) ℂ)
    (hcols : ∀ μ, W *ᵥ openRegionWeight (groupBondTensor a) R μ =
      ∑ i, c i • openRegionWeight (groupBondTensor (b i)) R μ)
    (hout : ∀ i v, v ∉ R → a v = b i v) :
    regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor a) =
      ∑ i, c i • stateCoeff (groupBondTensor (b i)) := by
  classical
  funext ξ
  obtain ⟨⟨σ, τ⟩, rfl⟩ := (regionConfigEquiv (d := d) R).symm.surjective ξ
  change (regionLocalTerm R W *ᵥ _) (assembleRegionσ R σ τ) = _
  rw [regionLocalTerm_mulVec_assemble]
  simp only [Matrix.mulVec, dotProduct,
    stateCoeff_eq_openRegionComplement
      (groupBondTensor a) R (fun _ => Fintype.card_ne_zero), Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  change (∑ μ, (W *ᵥ openRegionWeight (groupBondTensor a) R μ) σ *
    openRegionWeight (groupBondTensor a) (Finset.univ \ R)
      (regionComplementBoundaryConfig (groupBondTensor a) R μ) τ) = _
  simp_rw [hcols]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  change _ = stateCoeff (groupBondTensor (b i)) (assembleRegionσ R σ τ)
  rw [stateCoeff_eq_openRegionComplement (groupBondTensor (b i)) R
    (fun _ => Fintype.card_ne_zero)]
  apply Finset.sum_congr rfl
  intro μ _
  rw [openRegionWeight_groupBondTensor_congr_on (Finset.univ \ R) a (b i)
    (fun v hv => hout i v (Finset.mem_sdiff.mp hv).2)]
  rfl
/-- An identity on every actual open boundary column passes to the globally
contracted state when the exterior site tensors agree.
Source: SCP10, finite cut contraction, lines 1935–1957. -/
theorem regionLocalTerm_mulVec_stateCoeff_of_openColumns (R : Finset V)
    (a b : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (W : Matrix ({v : V // v ∈ R} → Fin d) ({v : V // v ∈ R} → Fin d) ℂ)
    (hcols : ∀ μ, W *ᵥ openRegionWeight (groupBondTensor a) R μ =
      openRegionWeight (groupBondTensor b) R μ)
    (hout : ∀ v ∉ R, a v = b v) :
    regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor a) =
      stateCoeff (groupBondTensor b) := by
  simpa only [Fintype.sum_unique, one_smul] using
    regionLocalTerm_mulVec_stateCoeff_sum_of_openColumns R a
      (fun _ : Unit => b) (fun _ => 1) W
      (fun μ => by simpa only [Fintype.sum_unique, one_smul] using hcols μ)
      (fun _ v hv => hout v hv)

end TNLean.PEPS
