/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingProjectionGap
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding

/-!
# The uniform gap of an independent-bond Hamiltonian

In independent-bond coordinates, the parent Hamiltonian is the sum of a
one-bond orthogonal projection over all bonds. Its spectral gap above zero
is at least one for every chain length. If the projection is not the
identity, the tensor product of its complementary projections is nonzero
and is annihilated by the Hamiltonian, so zero is attained.

These are the spectral assertions for the bond interpolation of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
source lines 899–906. Locality and symmetry after regrouping the physical
registers are separate assertions.
-/

namespace MPSTensor

/-- The sum of a one-bond interaction over independent bonds.
Source: arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`,
and Section II.F.2, the parent Hamiltonian following `eq:sym:omega-gamma`. -/
noncomputable def independentBondHamiltonian {d N : ℕ} (hN : 1 ≤ N)
    (K : Matrix (Fin d) (Fin d) ℂ) : MPOTensor.ChainOperator d N :=
  ∑ i : Fin N, MPOTensor.embedLocalOperator 1 N hN i (MPOTensor.oneSiteOperator K)

/-- Every nonzero spectral value of the independent-bond projector sum is
at least one, uniformly in the chain length.
Source: arXiv:1010.3732, Section II.F.2, source lines 904–906. -/
theorem independentBondHamiltonian_spectrum_gap {d N : ℕ} (hN : 1 ≤ N)
    (K : Matrix (Fin d) (Fin d) ℂ) (hK : IsStarProjection K) :
    ∀ z ∈ spectrum ℂ (independentBondHamiltonian hN K),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  apply Matrix.spectrum_sum_separated_of_isStarProjection
  · intro i
    apply MPOTensor.embedLocalOperator_isStarProjection
    rw [MPOTensor.oneSiteOperator_eq_reindexAlgEquiv_symm, isStarProjection_iff']
    constructor
    · rw [← map_mul, hK.isIdempotentElem.eq]
    · exact (show K.IsHermitian from hK.isSelfAdjoint).submatrix _
  · exact MPOTensor.embedLocalOperator_one_commute hN K

/-- The product of the complementary one-bond projections is annihilated by
the independent-bond Hamiltonian.
Source: arXiv:1010.3732, Section II.F.2, the parent Hamiltonian of the
interpolating product of bonds, source lines 899–906. -/
theorem independentBondHamiltonian_mul_complement {d N : ℕ} (hN : 1 ≤ N)
    (K : Matrix (Fin d) (Fin d) ℂ) (hK : IsStarProjection K) :
    independentBondHamiltonian hN K *
      MPOTensor.sitewiseMatrixFamily (fun _ : Fin N => 1 - K) = 0 := by
  classical
  rw [independentBondHamiltonian, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [← MPOTensor.sitewiseMatrixFamily_mulSingle,
    MPOTensor.sitewiseMatrixFamily_mul]
  ext σ τ
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change ((Pi.mulSingle (M := fun _ : Fin N => Matrix (Fin d) (Fin d) ℂ)
    i K i) * (1 - K)) (σ i) (τ i) = 0
  simp only [Pi.mulSingle_eq_same, hK.mul_one_sub_self, Matrix.zero_apply]

/-- A non-identity one-bond projection gives an independent-bond Hamiltonian
whose spectrum contains zero at every positive chain length.
Source: arXiv:1010.3732, Section II.F.2, source lines 899–906. -/
theorem independentBondHamiltonian_zero_mem_spectrum {d N : ℕ} (hN : 1 ≤ N)
    (K : Matrix (Fin d) (Fin d) ℂ) (hK : IsStarProjection K) (hKne : K ≠ 1) :
    (0 : ℂ) ∈ spectrum ℂ (independentBondHamiltonian hN K) := by
  classical
  have hQ : 1 - K ≠ 0 := sub_ne_zero.mpr (Ne.symm hKne)
  obtain ⟨a, b, hab⟩ : ∃ a b, (1 - K) a b ≠ 0 := by
    by_contra! h
    apply hQ
    ext a b
    exact h a b
  have hQN : MPOTensor.sitewiseMatrixFamily (fun _ : Fin N => 1 - K) ≠ 0 := by
    intro hz
    have he := congrFun (congrFun hz (fun _ => a)) (fun _ => b)
    apply pow_ne_zero N hab
    simpa [MPOTensor.sitewiseMatrixFamily] using he
  rw [spectrum.zero_mem_iff]
  intro hu
  apply hQN
  apply hu.mul_left_cancel
  simpa only [mul_zero] using independentBondHamiltonian_mul_complement hN K hK

end MPSTensor
