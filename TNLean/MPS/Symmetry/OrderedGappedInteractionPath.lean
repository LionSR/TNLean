/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommonKernelSpectralGap
import TNLean.MPS.Symmetry.InteractionHamiltonianOrder
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A gapped path from ordered interactions with common ground spaces

Suppose two positive two-site interactions satisfy an operator inequality.
If their periodic Hamiltonians have the same zero modes and the smaller
Hamiltonian has a uniform gap above zero, affine interpolation preserves
that gap. Endpoint symmetry is also preserved throughout the path.

This is the comparison needed between independent-bond interactions and
canonical parent interactions after physical embedding in the fixed-point
construction of arXiv:1010.3732, Sections II.D.2 and II.F.2.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Sections II.D.2 and II.F.2
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- Ordered positive interactions with common periodic zero modes are
connected by affine interpolation with the original uniform spectral gap.
The zero modes and gap are hypotheses of this comparison theorem. Source:
arXiv:1010.3732, Sections II.D.2 and II.F.2, comparison of parent interactions
in the isometric fixed-point construction. -/
noncomputable def orderedGappedInteractionPath
    {G : Type} [Group G] {d : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A B : MPOTensor.ChainOperator d 2)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (hAnorm : ‖A‖ ≤ 1) (hBnorm : ‖B‖ ≤ 1)
    (hker : ∀ (N : ℕ) (hN : 2 ≤ N) (x : Cfg d N → ℂ),
      (interactionHamiltonian A hN).mulVec x = 0 →
        (interactionHamiltonian B hN).mulVec x = 0)
    (hzero : ∀ (N : ℕ) (hN : 2 ≤ N), ∃ x : EuclideanSpace ℂ (Cfg d N),
      x ≠ 0 ∧ Matrix.toEuclideanLin (interactionHamiltonian A hN) x = 0)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      ∀ z ∈ spectrum ℂ (interactionHamiltonian A hN), z.re = 0 ∨ δ ≤ z.re)
    (hSymA : ∀ (N : ℕ) (hN : 2 ≤ N) (g : G),
      Commute (interactionHamiltonian A hN)
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ)))
    (hSymB : ∀ (N : ℕ) (hN : 2 ≤ N) (g : G),
      Commute (interactionHamiltonian B hN)
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ))) :
    SymmetricGappedInteractionPath U A B := by
  have hAffine (γ : ℝ) : A + γ • (B - A) = (1 - γ) • A + γ • B := by module
  refine {
    interaction := fun γ => A + γ • (B - A)
    interaction_zero := by simp
    interaction_one := by simp
    hermitian := ?_
    norm_le_one := ?_
    continuous := by fun_prop
    gap := ?_
    symmetric := ?_
  }
  · intro γ hγ
    rw [hAffine]
    exact ((hA.smul (sub_nonneg.mpr hγ.2)).add (hB.smul hγ.1)).isHermitian
  · intro γ hγ
    rw [hAffine]
    calc
      ‖(1 - γ) • A + γ • B‖ ≤ (1 - γ) * ‖A‖ + γ * ‖B‖ :=
        convexOn_univ_norm.2 (Set.mem_univ A) (Set.mem_univ B)
          (sub_nonneg.mpr hγ.2) hγ.1 (by ring)
      _ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hAnorm (sub_nonneg.mpr hγ.2),
        mul_le_mul_of_nonneg_left hBnorm hγ.1]
  · obtain ⟨δ, hδ, hSpec⟩ := hgap
    refine ⟨δ, hδ, ?_⟩
    intro γ hγ N hN
    have hHA := interactionHamiltonian_posSemidef hA hN
    have h := Matrix.spectrum_gap_interpolation_of_le_of_nontrivial_kernel
      (interactionHamiltonian A hN) (interactionHamiltonian B hN)
      hHA (interactionHamiltonian_mono hAB hN) (hker N hN) δ γ hγ.1
      (Matrix.orthogonal_quadratic_gap_of_spectrum_separated _ hHA.isHermitian
        (hSpec N hN)) (hzero N hN)
    rw [← interactionHamiltonian_add_smul_sub] at h
    exact ⟨0, h.1, by simpa using h.2⟩
  · intro γ hγ g N hN
    rw [interactionHamiltonian_add_smul_sub]
    exact (hSymA N hN g).add_left (((hSymB N hN g).sub_left (hSymA N hN g)).smul_left γ)

end MPSTensor
