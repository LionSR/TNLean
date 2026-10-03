/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductParentHamiltonian
import TNLean.MPS.Symmetry.BondProductContinuity
import TNLean.MPS.Symmetry.BondRegrouping

/-!
# Independent-bond parent Hamiltonian in physical coordinates

The incoming-bond permutation transports the commuting bond Hamiltonian
to the original cyclic chain of two-register physical sites. Unitary
conjugation preserves its gap and unique product ground state. Locality of
the transported summands is recorded separately in
`BondRegroupingLocality`.

Source: Schuch--Pérez-García--Cirac, arXiv:1010.3732,
Sections II.D.2 and II.F.2.
-/

open scoped Matrix InnerProductSpace

namespace MPSTensor

variable {D N : ℕ}

/-- The incoming-bond permutation acting on the finite-chain Hilbert space.
Source: arXiv:1010.3732, Section II.D.2. -/
noncomputable def incomingBondUnitaryLin (D N : ℕ) :
    EuclideanSpace ℂ (Fin N → Fin (D * D)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin N → Fin (D * D)) :=
  (bondMatrixEquiv (D * D) N).symm ((incomingBondPerm D N).permMatrix ℂ)

/-- The bond-product parent Hamiltonian in the original physical
configuration coordinates. Source: arXiv:1010.3732, Section II.D.2,
equation `eq:phase-nosym:iso-hamiltonian`. -/
noncomputable def physicalBondProductParentHamiltonianLin
    (η : Fin (D * D) → ℂ) (hN : 1 ≤ N) :
    EuclideanSpace ℂ (Fin N → Fin (D * D)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin N → Fin (D * D)) :=
  incomingBondUnitaryLin D N * bondProductParentHamiltonianLin η hN *
    star (incomingBondUnitaryLin D N)

/-- Matrix of the physical-coordinate parent Hamiltonian. This is the
unitary conjugate of the independent-bond Hamiltonian.
Source: arXiv:1010.3732, Section II.D.2. -/
noncomputable def physicalBondProductParentHamiltonian
    (η : Fin (D * D) → ℂ) (hN : 1 ≤ N) :
    MPOTensor.ChainOperator (D * D) N :=
  (incomingBondPerm D N).permMatrix ℂ *
    bondProductParentHamiltonian η hN *
    ((incomingBondPerm D N).permMatrix ℂ)ᴴ

/-- The physical matrix acts by the stated conjugate linear operator.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem physicalBondProductParentHamiltonianLin_eq_matrix
    (η : Fin (D * D) → ℂ) (hN : 1 ≤ N) :
    physicalBondProductParentHamiltonianLin η hN =
      (bondMatrixEquiv (D * D) N).symm
        (physicalBondProductParentHamiltonian η hN) := by
  let e := bondMatrixEquiv (D * D) N
  let P := (incomingBondPerm D N).permMatrix ℂ
  let H := bondProductParentHamiltonian η hN
  change e.symm P * e.symm H * star (e.symm P) =
    e.symm (P * H * Pᴴ)
  rw [← map_star e.symm, ← map_mul, ← map_mul]
  rfl

/-- The physical parent Hamiltonian varies continuously with the bond vector
on every finite chain. Source: arXiv:1010.3732, Section II.F.2. -/
theorem continuous_physicalBondProductParentHamiltonian
    {D N : ℕ} (hN : 1 ≤ N) :
    Continuous (fun η : Fin (D * D) → ℂ =>
      physicalBondProductParentHamiltonian η hN) := by
  unfold physicalBondProductParentHamiltonian
  exact (continuous_const.mul
    (continuous_bondProductParentHamiltonian hN)).mul continuous_const

/-- The normalized interpolation gives a continuous path of physical parent
Hamiltonians on every finite chain. Source: arXiv:1010.3732,
Section II.F.2. -/
theorem continuous_normalizedPhysicalBondInterpolation_parent
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (hN : 1 ≤ N) :
    Continuous (fun γ : ℝ => physicalBondProductParentHamiltonian
      (normalizedBondInterpolationVector D₀ D₁ γ) hN) :=
  (continuous_physicalBondProductParentHamiltonian hN).comp
    (continuous_normalizedBondInterpolationVector h₀ h₁)

/-- The incoming-bond operator is unitary. Source: arXiv:1010.3732,
Section II.D.2. -/
theorem incomingBondUnitaryLin_star_mul_self (D N : ℕ) :
    star (incomingBondUnitaryLin D N) * incomingBondUnitaryLin D N = 1 := by
  let e := bondMatrixEquiv (D * D) N
  let P := (incomingBondPerm D N).permMatrix ℂ
  have hP : star P * P = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (incomingBondPerm_mem_unitaryGroup D N)
  change star (e.symm P) * e.symm P = 1
  rw [← map_star e.symm, ← map_mul, hP, map_one]

/-- The incoming-bond operator has its adjoint as right inverse.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem incomingBondUnitaryLin_mul_star_self (D N : ℕ) :
    incomingBondUnitaryLin D N * star (incomingBondUnitaryLin D N) = 1 := by
  let e := bondMatrixEquiv (D * D) N
  let P := (incomingBondPerm D N).permMatrix ℂ
  have hP : P * star P = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp (incomingBondPerm_mem_unitaryGroup D N)
  change e.symm P * star (e.symm P) = 1
  rw [← map_star e.symm, ← map_mul, hP, map_one]

/-- Unitary regrouping preserves the inner product of finite-chain states.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem incomingBondUnitaryLin_inner (D N : ℕ)
    (x y : EuclideanSpace ℂ (Fin N → Fin (D * D))) :
    ⟪incomingBondUnitaryLin D N x, incomingBondUnitaryLin D N y⟫_ℂ =
      ⟪x, y⟫_ℂ := by
  let U := incomingBondUnitaryLin D N
  have hU := incomingBondUnitaryLin_star_mul_self D N
  calc
    ⟪U x, U y⟫_ℂ = ⟪x, U.adjoint (U y)⟫_ℂ :=
      (U.adjoint_inner_right x (U y)).symm
    _ = ⟪x, y⟫_ℂ := by
      rw [← LinearMap.star_eq_adjoint, ← Module.End.mul_apply, hU]
      rfl

/-- The physical-coordinate parent Hamiltonian retains the uniform
quadratic-form gap `H² ≥ H` for every chain length. Source:
arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem physicalBondProductParentHamiltonian_gap_one
    (η : Fin (D * D) → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N)
    (v : EuclideanSpace ℂ (Fin N → Fin (D * D))) :
    (⟪physicalBondProductParentHamiltonianLin η hN v, v⟫_ℂ).re ≤
      (⟪physicalBondProductParentHamiltonianLin η hN v,
        physicalBondProductParentHamiltonianLin η hN v⟫_ℂ).re := by
  let U := incomingBondUnitaryLin D N
  let H := bondProductParentHamiltonianLin η hN
  let w := star U v
  have hUw : U w = v := by
    change U (star U v) = v
    rw [← Module.End.mul_apply, incomingBondUnitaryLin_mul_star_self]
    rfl
  have hHv : physicalBondProductParentHamiltonianLin η hN v = U (H w) := by
    rfl
  rw [hHv, ← hUw]
  rw [incomingBondUnitaryLin_inner D N (H w) w,
    incomingBondUnitaryLin_inner D N (H w) (H w)]
  exact bondProductParentHamiltonian_gap_one η hη hN w

/-- The physical-coordinate ground space is the image of the independent-bond
ground space under the incoming-bond unitary. Source: arXiv:1010.3732,
Section II.D.2. -/
theorem physicalBondProductParentHamiltonian_groundSpace
    (η : Fin (D * D) → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    LinearMap.ker (physicalBondProductParentHamiltonianLin η hN) =
      Submodule.span ℂ
        {incomingBondUnitaryLin D N (bondProductState η N)} := by
  let U := incomingBondUnitaryLin D N
  let H := bondProductParentHamiltonianLin η hN
  have hleft := incomingBondUnitaryLin_star_mul_self D N
  have hright := incomingBondUnitaryLin_mul_star_self D N
  have hker : LinearMap.ker (physicalBondProductParentHamiltonianLin η hN) =
      (LinearMap.ker H).map U := by
    apply Submodule.ext
    intro v
    constructor
    · intro hv
      have hv' : U (H (star U v)) = 0 := by
        simpa [LinearMap.mem_ker, physicalBondProductParentHamiltonianLin,
          Module.End.mul_apply] using hv
      have hw : H (star U v) = 0 := by
        have hh := congrArg (fun z => (star U) z) hv'
        change (star U) (U (H (star U v))) = (star U) 0 at hh
        rw [← Module.End.mul_apply, hleft] at hh
        simpa using hh
      refine ⟨star U v, ?_, ?_⟩
      · exact LinearMap.mem_ker.mpr hw
      · rw [← Module.End.mul_apply, hright]
        rfl
    · rintro ⟨w, hw, rfl⟩
      change physicalBondProductParentHamiltonianLin η hN (U w) = 0
      have hw' : H w = 0 := LinearMap.mem_ker.mp hw
      have hsw : (star U) (U w) = w := by
        rw [← Module.End.mul_apply, hleft]
        rfl
      change U (H ((star U) (U w))) = 0
      rw [hsw, hw']
      exact map_zero U
  rw [hker, bondProductParentHamiltonian_groundSpace_eq_span η hη hN]
  rw [Submodule.map_span]
  simp [U]

/-- The normalized interpolation has a uniform gap in physical-site
coordinates. Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedPhysicalBondInterpolation_parent_gap_one
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ)
    {N : ℕ} (hN : 1 ≤ N)
    (v : EuclideanSpace ℂ
      (Fin N → Fin ((D₀ + D₁) * (D₀ + D₁)))) :
    (⟪physicalBondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ γ) hN v, v⟫_ℂ).re ≤
      (⟪physicalBondProductParentHamiltonianLin
        (normalizedBondInterpolationVector D₀ D₁ γ) hN v,
        physicalBondProductParentHamiltonianLin
          (normalizedBondInterpolationVector D₀ D₁ γ) hN v⟫_ℂ).re :=
  physicalBondProductParentHamiltonian_gap_one _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN v

/-- The normalized physical parent Hamiltonian has the transported product
state as its unique ground line. Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedPhysicalBondInterpolation_parent_groundSpace
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    LinearMap.ker (physicalBondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ γ) hN) =
      Submodule.span ℂ
        {incomingBondUnitaryLin (D₀ + D₁) N
          (bondProductState (normalizedBondInterpolationVector D₀ D₁ γ) N)} :=
  physicalBondProductParentHamiltonian_groundSpace _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN

end MPSTensor
