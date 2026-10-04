/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSCriticalMagnon
import TNLean.Algebra.CycleLaplacianFourier

/-!
# Thermodynamic gaplessness of the critical PVBS parent

The first Fourier one-particle mode of the actual critical parent Hamiltonian
has positive energy `1 - cos (2π/N)` on every ring with at least two sites.
These energies tend to zero as the ring grows. Positive energy and symmetry
place each vector in the orthogonal complement of the entire actual kernel,
not merely the vacuum complement. Thus no eventual positive uniform gap exists.

Source: Bachmann–Nachtergaele, arXiv:1112.4097, Section II, the one-particle
dispersion following equation (8), specialized to one species and zero phase.
No vanishing finite-volume gap above the enlarged critical kernel is asserted.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

/-- The first Fourier one-particle vector is nonzero at every positive length. -/
theorem pvbs_fourierMagnon_ne_zero (N : ℕ) [NeZero N] :
    WithLp.toLp 2 (SpinChain.oneMagnon
      (fun j : Fin N => ZMod.stdAddChar (ZMod.finEquiv N j))) ≠
        (0 : EuclideanSpace ℂ (Cfg 2 N)) := by
  intro h
  have hz := congrArg (fun v : EuclideanSpace ℂ (Cfg 2 N) =>
    v (SpinChain.singleDown ((ZMod.finEquiv N).symm 0))) h
  change SpinChain.oneMagnon (fun j => ZMod.stdAddChar (ZMod.finEquiv N j))
    (SpinChain.singleDown ((ZMod.finEquiv N).symm 0)) = 0 at hz
  exact one_ne_zero (by simpa only [SpinChain.oneMagnon_singleDown,
    RingEquiv.apply_symm_apply, AddChar.map_zero_eq_one] using hz)

/-- The actual critical PVBS parent has a Fourier magnon with energy
`1 - cos (2π/N)`, including the two-oriented-window convention at length two. -/
theorem parentHamiltonianES_pvbs_critical_fourierMagnon {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) :
    parentHamiltonianES (pvbsTensor 1) 2 N
      (WithLp.toLp 2 (SpinChain.oneMagnon
        (fun j : Fin N => ZMod.stdAddChar (ZMod.finEquiv N j)))) =
      (ZMod.cycleFourierGap N : ℂ) •
        WithLp.toLp 2 (SpinChain.oneMagnon
          (fun j : Fin N => ZMod.stdAddChar (ZMod.finEquiv N j))) := by
  rw [parentHamiltonianES_pvbs_critical_oneMagnon hN]
  ext σ
  have hc (j : Fin N) :
      ZMod.stdAddChar (ZMod.finEquiv N j) -
        (ZMod.stdAddChar (ZMod.finEquiv N (cyclicSuccessorEquiv N j)) +
          ZMod.stdAddChar (ZMod.finEquiv N ((cyclicSuccessorEquiv N).symm j))) / 2 =
      (ZMod.cycleFourierGap N : ℂ) * ZMod.stdAddChar (ZMod.finEquiv N j) := by
    simpa only [ZMod.cycleLaplacian, finEquiv_cyclicSuccessorEquiv,
      finEquiv_cyclicSuccessorEquiv_symm] using
        ZMod.cycleLaplacian_stdAddChar (ZMod.finEquiv N j)
  simp_rw [hc]
  exact SpinChain.oneMagnon_smul _ _ _

/-- A critical Fourier magnon is orthogonal to the entire ground-state kernel,
because its eigenvalue is positive and the parent Hamiltonian is symmetric. -/
theorem pvbs_fourierMagnon_mem_orthogonal_kernel {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    WithLp.toLp 2 (SpinChain.oneMagnon
      (fun j : Fin N => ZMod.stdAddChar (ZMod.finEquiv N j))) ∈
        (LinearMap.ker (parentHamiltonianES (pvbsTensor 1) 2 N))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have h := (parentHamiltonianES_isPositive (pvbsTensor 1) 2 N).isSymmetric w
    (WithLp.toLp 2 (SpinChain.oneMagnon
      (fun j : Fin N => ZMod.stdAddChar (ZMod.finEquiv N j))))
  rw [LinearMap.mem_ker.mp hw, inner_zero_left,
    parentHamiltonianES_pvbs_critical_fourierMagnon hN, inner_smul_right] at h
  exact (mul_eq_zero.mp h.symm).resolve_left
    (Complex.ofReal_ne_zero.mpr (ZMod.cycleFourierGap_pos hN).ne')

/-- The critical one-species PVBS parent has no positive gap uniform over all
sufficiently large periodic chains. The comparison is with the whole actual
kernel at every length; it does not assert a zero gap on any fixed finite ring. -/
theorem not_exists_eventual_uniform_gap_pvbs_critical :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (pvbsTensor 1) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (pvbsTensor 1) 2 N v‖ := by
  rintro ⟨δ, hδ, N₀, hgap⟩
  obtain ⟨N, hN₀, hN, hη, hsmall⟩ := ZMod.exists_large_cycleFourierGap_pos_lt hδ N₀
  let : NeZero N := ⟨by omega⟩
  let v : EuclideanSpace ℂ (Cfg 2 N) := WithLp.toLp 2 (SpinChain.oneMagnon
    (fun j : Fin N => ZMod.stdAddChar (ZMod.finEquiv N j)))
  have hbound := hgap N hN₀ v (pvbs_fourierMagnon_mem_orthogonal_kernel hN)
  rw [parentHamiltonianES_pvbs_critical_fourierMagnon hN, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη] at hbound
  have hδle : δ ≤ ZMod.cycleFourierGap N :=
    le_of_mul_le_mul_right hbound (norm_pos_iff.mpr (pvbs_fourierMagnon_ne_zero N))
  exact (not_le_of_gt hsmall) hδle

end MPSTensor
