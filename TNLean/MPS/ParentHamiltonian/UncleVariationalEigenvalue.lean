/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleKernelConditions
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The finite variational spectral step for the uncle Hamiltonian

A positive operator with a vector orthogonal to its kernel and Rayleigh
quotient below epsilon has an actual positive eigenvalue below epsilon.
Applied to the explicit finite uncle Hamiltonian, this is the spectral step
in arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
The preceding norm, energy, and ground-overlap estimates must still supply
such a vector; they are not assumed as a gaplessness conclusion here.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace MPSTensor

private theorem exists_small_pos_eigenvalue_of_rayleigh
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (v : E) (hv : v ∈ (LinearMap.ker T)ᗮ)
    (ε : ℝ) (hRayleigh : (⟪T v, v⟫_ℂ).re < ε * ‖v‖ ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧ Module.End.HasEigenvalue T (μ : ℂ) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
    hT.isSymmetric.eigenvectorBasis rfl
  let lam : Fin (Module.finrank ℂ E) → ℝ := hT.isSymmetric.eigenvalues rfl
  have hnonneg (i) : 0 ≤ lam i := hT.nonneg_eigenvalues rfl i
  have heig (i) : Module.End.HasEigenvalue T (lam i : ℂ) :=
    hT.isSymmetric.hasEigenvalue_eigenvalues rfl i
  have hcoord_zero (i) (hi : lam i = 0) : b.repr v i = 0 := by
    have hker : b i ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      change T (hT.isSymmetric.eigenvectorBasis rfl i) = 0
      rw [hT.isSymmetric.apply_eigenvectorBasis]
      change (lam i : ℂ) • b i = 0
      rw [hi, Complex.ofReal_zero, zero_smul]
    rw [b.repr_apply_apply]
    exact (Submodule.mem_orthogonal v).mp hv (b i) hker
  have hnorm : ‖v‖ ^ 2 = ∑ i, ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.norm_map v, PiLp.norm_sq_eq_of_L2]
  have henergy : (⟪T v, v⟫_ℂ).re = ∑ i, lam i * ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.inner_map_map (T v) v, PiLp.inner_apply]
    change Complex.reCLM (∑ i, inner ℂ (b.repr (T v) i) (b.repr v i)) = _
    rw [map_sum Complex.reCLM]
    apply Finset.sum_congr rfl
    intro i _
    have hdia : b.repr (T v) i = (lam i : ℂ) * b.repr v i :=
      hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
    rw [hdia]
    change (inner ℂ ((lam i : ℂ) • b.repr v i) (b.repr v i)).re = _
    rw [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq]
  suffices ∃ i, 0 < lam i ∧ lam i < ε by
    obtain ⟨i, hi, hε⟩ := this
    exact ⟨lam i, hi, hε, heig i⟩
  by_contra hnone
  have hweight (i) : ε * ‖b.repr v i‖ ^ 2 ≤ lam i * ‖b.repr v i‖ ^ 2 := by
    by_cases hi : lam i = 0
    · rw [hcoord_zero i hi]
      simp
    · have hpos : 0 < lam i := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
      have hlarge : ε ≤ lam i := by
        by_contra hlt
        exact hnone ⟨i, hpos, lt_of_not_ge hlt⟩
      exact mul_le_mul_of_nonneg_right hlarge (sq_nonneg _)
  have hlower : ε * ‖v‖ ^ 2 ≤ (⟪T v, v⟫_ℂ).re := by
    rw [hnorm, henergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hweight i
  exact (not_lt_of_ge hlower) hRayleigh

/-- The actual finite uncle Hamiltonian has a positive eigenvalue below a
strict Rayleigh bound from its kernel complement. Positivity is derived from
the actual interaction rather than supplied as another hypothesis.

This is the finite spectral argument of arXiv:1210.6613, proof of thm:gapless,
lines 1302–1314; constructing the variational vector remains a separate step. -/
theorem exists_pos_eigenvalue_uncleHamiltonianES_lt_of_rayleigh
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (uncleHamiltonianES A B R L N).toLinearMap)ᗮ)
    (ε : ℝ)
    (hRayleigh : (⟪uncleHamiltonianES A B R L N v, v⟫_ℂ).re < ε * ‖v‖ ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧
      Module.End.HasEigenvalue (uncleHamiltonianES A B R L N).toLinearMap (μ : ℂ) :=
  exists_small_pos_eigenvalue_of_rayleigh _ (uncleHamiltonianES_isPositive A B R L N)
    v hv ε hRayleigh

end MPSTensor
