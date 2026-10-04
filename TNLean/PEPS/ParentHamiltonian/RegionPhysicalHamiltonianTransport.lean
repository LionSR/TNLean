/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Physical transport of regional Hamiltonians

Local intertwining identities extend to the full graph, because the physical
product map factors across every regional cut. In particular, unitary physical
changes of coordinates conjugate the full parent Hamiltonian.

Source: the concatenation of physical maps in SCP10, arXiv:1001.3807,
Observation `obs:iso:accessible-virt`, lines 1765–1820, and the general
regional Hamiltonian sum in arXiv:2011.12127, Section IV.C.1, lines 2003–2011.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d e : ℕ}

/-- Equality of every complementary slice determines a full physical vector. -/
theorem regionSliceMap_ext (R : Finset V) {ψ φ : (V → Fin d) → ℂ}
    (h : ∀ τ : RegionPhysicalConfig (d := d) (Finset.univ \ R),
      regionSliceMap R τ ψ = regionSliceMap R τ φ) : ψ = φ := by
  funext ξ
  obtain ⟨⟨σ, τ⟩, rfl⟩ := (regionConfigEquiv R).symm.surjective ξ
  exact congrFun (h τ) σ

/-- A regional interaction acts on each slice by its local matrix. -/
theorem regionSliceMap_regionLocalTerm (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (ψ : (V → Fin d) → ℂ)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    regionSliceMap R τ (regionLocalTerm R h *ᵥ ψ) = h *ᵥ regionSliceMap R τ ψ := by
  funext σ
  exact regionLocalTerm_mulVec_assemble R h ψ σ τ

/-- A local intertwining identity extends to the full graph under the product
physical map. No positivity or invertibility assumption is required. -/
theorem globalPhysicalMap_regionLocalTerm (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (k : Matrix (RegionPhysicalConfig (d := e) R) (RegionPhysicalConfig (d := e) R) ℂ)
    (hF : k * regionPhysicalProductMatrix R F = regionPhysicalProductMatrix R F * h)
    (ψ : (V → Fin d) → ℂ) :
    globalPhysicalMap F (regionLocalTerm R h *ᵥ ψ) =
      regionLocalTerm R k *ᵥ globalPhysicalMap F ψ := by
  apply regionSliceMap_ext R
  intro τ
  rw [regionSliceMap_globalPhysicalMap, regionSliceMap_regionLocalTerm,
    regionSliceMap_globalPhysicalMap]
  change _ = Matrix.mulVecLin k _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  rw [regionSliceMap_regionLocalTerm]
  change regionPhysicalProductMatrix R F *ᵥ (h *ᵥ regionSliceMap R β ψ) =
    k *ᵥ (regionPhysicalProductMatrix R F *ᵥ regionSliceMap R β ψ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hF]

/-- Matrix of the product physical map on the full graph. -/
noncomputable def globalPhysicalMatrix (F : V → Matrix (Fin e) (Fin d) ℂ) :
    Matrix (V → Fin e) (V → Fin d) ℂ :=
  LinearMap.toMatrix' (globalPhysicalMap F)

/-- The product physical matrix has one matrix coefficient per vertex. -/
@[simp]
theorem globalPhysicalMatrix_apply (F : V → Matrix (Fin e) (Fin d) ℂ)
    (τ : V → Fin e) (σ : V → Fin d) :
    globalPhysicalMatrix F τ σ = ∏ v, F v (τ v) (σ v) := by
  classical
  simp [globalPhysicalMatrix, LinearMap.toMatrix'_apply, globalPhysicalMap_apply,
    Pi.single_apply]

omit [Fintype V] in
/-- Products of vertex unitaries are unitary on every region. -/
theorem regionPhysicalProductMatrix_isUnitaryBetween (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (hF : ∀ v, (F v).IsUnitaryBetween) :
    (regionPhysicalProductMatrix R F).IsUnitaryBetween := by
  classical
  refine ⟨regionPhysicalProductMatrix_isIsometry R F (fun v => (hF v).1), ?_⟩
  change regionPhysicalProductMatrix R F * (regionPhysicalProductMatrix R F).conjTranspose = 1
  rw [regionPhysicalProductMatrix_conjTranspose,
    regionPhysicalProductMatrix_mul (In := fun _ => Fin e) (Mid := fun _ => Fin d)
      (Out := fun _ => Fin e)]
  have hprod : ∀ v, F v * (F v).conjTranspose = 1 := fun v => (hF v).2
  simpa only [hprod] using (regionPhysicalProductMatrix_one (Out := fun _ => Fin e) R)

/-- Products of vertex unitaries are unitary on the full graph. -/
theorem globalPhysicalMatrix_isUnitaryBetween (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, (F v).IsUnitaryBetween) : (globalPhysicalMatrix F).IsUnitaryBetween := by
  classical
  have hM : globalPhysicalMatrix F = Matrix.reindex
      (fullRegionConfigEquiv e).symm (fullRegionConfigEquiv d).symm
      (regionPhysicalProductMatrix Finset.univ F) := by
    ext τ σ
    rw [globalPhysicalMatrix_apply]
    exact Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
      (fun v => F v (τ v) (σ v))
  rw [hM]
  exact (regionPhysicalProductMatrix_isUnitaryBetween Finset.univ F hF).reindex _
    (fullRegionConfigEquiv e).symm (fullRegionConfigEquiv d).symm

omit [Fintype V] in
/-- The inverse regional map of a product of unitaries is its adjoint. -/
theorem toMatrix_regionPhysicalEquiv_symm
    (R : Finset V) (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (hF : ∀ v, (LinearMap.toMatrix' (F v).toLinearMap).IsUnitaryBetween) :
    LinearMap.toMatrix' (regionPhysicalEquiv R F).symm.toLinearMap =
      (regionPhysicalProductMatrix R
        (fun v => LinearMap.toMatrix' (F v).toLinearMap)).conjTranspose := by
  classical
  let U := regionPhysicalProductMatrix R (fun v => LinearMap.toMatrix' (F v).toLinearMap)
  let Q := LinearMap.toMatrix' (regionPhysicalEquiv R F).symm.toLinearMap
  have hU : LinearMap.toMatrix' (regionPhysicalEquiv R F).toLinearMap = U := by
    change LinearMap.toMatrix' (Matrix.mulVecLin U) = U
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  have hQU : Q * U = 1 := by
    rw [← hU]
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hUU : U * U.conjTranspose = 1 :=
    (regionPhysicalProductMatrix_isUnitaryBetween R _ hF).2
  change Q = U.conjTranspose
  calc
    Q = Q * (U * U.conjTranspose) := by rw [hUU, Matrix.mul_one]
    _ = U.conjTranspose := by rw [← Matrix.mul_assoc, hQU, Matrix.one_mul]

omit [Fintype V] in
/-- Under unitary physical maps, inverse-adjoint transport is unitary conjugation. -/
theorem deformedRegionInteraction_eq_unitary_conj (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (hF : ∀ v, (LinearMap.toMatrix' (F v).toLinearMap).IsUnitaryBetween)
    (h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    deformedRegionInteraction R F h =
      regionPhysicalProductMatrix R (fun v => LinearMap.toMatrix' (F v).toLinearMap) * h *
        (regionPhysicalProductMatrix R
          (fun v => LinearMap.toMatrix' (F v).toLinearMap)).conjTranspose := by
  rw [deformedRegionInteraction, toMatrix_regionPhysicalEquiv_symm R F hF,
    Matrix.conjTranspose_conjTranspose]

variable {ι : Type*} [Fintype ι]

/-- Intertwining identities for every regional interaction intertwine the full
Hamiltonian sums. -/
theorem globalPhysicalMap_regionParentHamiltonian (R : ι → Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (k : (i : ι) → Matrix (RegionPhysicalConfig (d := e) (R i))
      (RegionPhysicalConfig (d := e) (R i)) ℂ)
    (hF : ∀ i, k i * regionPhysicalProductMatrix (R i) F =
      regionPhysicalProductMatrix (R i) F * h i) (ψ : (V → Fin d) → ℂ) :
    globalPhysicalMap F (regionParentHamiltonian R h *ᵥ ψ) =
      regionParentHamiltonian R k *ᵥ globalPhysicalMap F ψ := by
  simp only [regionParentHamiltonian, Matrix.sum_mulVec, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    globalPhysicalMap_regionLocalTerm (R i) F (h i) (k i) (hF i) ψ

/-- Regional matrix intertwining identities extend to the full Hamiltonian matrices. -/
theorem globalPhysicalMatrix_regionParentHamiltonian (R : ι → Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (k : (i : ι) → Matrix (RegionPhysicalConfig (d := e) (R i))
      (RegionPhysicalConfig (d := e) (R i)) ℂ)
    (hF : ∀ i, k i * regionPhysicalProductMatrix (R i) F =
      regionPhysicalProductMatrix (R i) F * h i) :
    regionParentHamiltonian R k * globalPhysicalMatrix F =
      globalPhysicalMatrix F * regionParentHamiltonian R h := by
  classical
  have hLin : Matrix.mulVecLin (regionParentHamiltonian R k) ∘ₗ globalPhysicalMap F =
      globalPhysicalMap F ∘ₗ Matrix.mulVecLin (regionParentHamiltonian R h) :=
    LinearMap.ext fun ψ => (globalPhysicalMap_regionParentHamiltonian R F h k hF ψ).symm
  simpa only [globalPhysicalMatrix, LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin'] using
    congrArg LinearMap.toMatrix' hLin

/-- Unitary physical changes of coordinates conjugate the full regional Hamiltonian. -/
theorem regionParentHamiltonian_physicalDeform_unitary (R : ι → Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (hF : ∀ v, (LinearMap.toMatrix' (F v).toLinearMap).IsUnitaryBetween)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) :
    regionParentHamiltonian R (fun i => deformedRegionInteraction (R i) F (h i)) =
      globalPhysicalMatrix (fun v => LinearMap.toMatrix' (F v).toLinearMap) *
        regionParentHamiltonian R h *
          (globalPhysicalMatrix
            (fun v => LinearMap.toMatrix' (F v).toLinearMap)).conjTranspose := by
  classical
  let M := globalPhysicalMatrix (fun v => LinearMap.toMatrix' (F v).toLinearMap)
  let K := regionParentHamiltonian R (fun i => deformedRegionInteraction (R i) F (h i))
  have hMM : M * M.conjTranspose = 1 := (globalPhysicalMatrix_isUnitaryBetween _ hF).2
  have hInter : K * M = M * regionParentHamiltonian R h := by
    apply globalPhysicalMatrix_regionParentHamiltonian
    intro i
    rw [deformedRegionInteraction_eq_unitary_conj (R i) F hF,
      Matrix.mul_assoc, Matrix.mul_assoc,
      (regionPhysicalProductMatrix_isUnitaryBetween (R i) _ hF).1, Matrix.mul_one]
  change K = M * regionParentHamiltonian R h * M.conjTranspose
  calc
    K = K * (M * M.conjTranspose) := by rw [hMM, Matrix.mul_one]
    _ = M * regionParentHamiltonian R h * M.conjTranspose := by
      rw [← Matrix.mul_assoc, hInter]

/-- Unitary physical deformation preserves the characteristic polynomial of the
full parent Hamiltonian, including every eigenvalue multiplicity. -/
theorem charpoly_regionParentHamiltonian_physicalDeform_unitary (R : ι → Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (hF : ∀ v, (LinearMap.toMatrix' (F v).toLinearMap).IsUnitaryBetween)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) :
    (regionParentHamiltonian R (fun i => deformedRegionInteraction (R i) F (h i))).charpoly =
      (regionParentHamiltonian R h).charpoly := by
  classical
  let M := globalPhysicalMatrix (fun v => LinearMap.toMatrix' (F v).toLinearMap)
  have hM := globalPhysicalMatrix_isUnitaryBetween
    (fun v => LinearMap.toMatrix' (F v).toLinearMap) hF
  have hCard : Fintype.card (V → Fin e) = Fintype.card (V → Fin d) :=
    Nat.le_antisymm (hM.2.card_le _) (hM.1.card_le _)
  rw [regionParentHamiltonian_physicalDeform_unitary R F hF h]
  have hchar := Matrix.charpoly_mul_comm_of_le (M * regionParentHamiltonian R h)
    M.conjTranspose (hM.1.card_le _)
  rw [hCard, Nat.sub_self, pow_zero, one_mul,
    ← Matrix.mul_assoc, hM.1, Matrix.one_mul] at hchar
  exact hchar

/-- Unitary physical deformation preserves the full Hamiltonian spectrum. -/
theorem spectrum_regionParentHamiltonian_physicalDeform_unitary (R : ι → Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (hF : ∀ v, (LinearMap.toMatrix' (F v).toLinearMap).IsUnitaryBetween)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) :
    spectrum ℂ (regionParentHamiltonian R
      (fun i => deformedRegionInteraction (R i) F (h i))) =
      spectrum ℂ (regionParentHamiltonian R h) := by
  classical
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    charpoly_regionParentHamiltonian_physicalDeform_unitary R F hF h,
    Matrix.mem_spectrum_iff_isRoot_charpoly]

end TNLean.PEPS
