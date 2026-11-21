/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.KernelGap
import TNLean.MPS.Symmetry.GappedInteractionPath
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A gapped path from ordered interactions with common ground spaces

Suppose two positive two-site interactions satisfy an operator inequality.
If their periodic Hamiltonians have the same zero modes and the smaller
Hamiltonian has a uniform gap above zero, affine interpolation preserves
that gap. Endpoint symmetry is also preserved throughout the path.

The ordered affine comparison is a lemma proved here; it is not stated in
the cited source. It is applied to compare independent-bond interactions
with canonical parent interactions after physical embedding, in the
fixed-point construction of arXiv:1010.3732, Section II.F.2. That section
interpolates by parent Hamiltonians of interpolated bond states and assumes
no operator order between interactions; the conjugated path
`Λ_γ h₀ Λ_γ` of Section II.D.2 is a different construction.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Section II.F.2 (application
  context)
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

open ManyBody

namespace MPSTensor

/-- Ordered positive interactions with common periodic zero modes are
connected by affine interpolation with the original uniform spectral gap.
The zero modes and gap are hypotheses of this comparison. The comparison is
proved here and is not stated in the source; it is applied in the isometric
fixed-point construction of arXiv:1010.3732, Section II.F.2. -/
noncomputable def orderedGappedInteractionPath
    {G : Type} [Group G] {d : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A B : MPOTensor.ChainOperator d 2)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (hAnorm : ‖A‖ ≤ 1) (hBnorm : ‖B‖ ≤ 1)
    (hker : ∀ (N : ℕ) (hN : 2 ≤ N) (x : Cfg d N → ℂ),
      (Interaction.translationInvariant hN A).hamiltonian.mulVec x = 0 →
        (Interaction.translationInvariant hN B).hamiltonian.mulVec x = 0)
    (hzero : ∀ (N : ℕ) (hN : 2 ≤ N), ∃ x : EuclideanSpace ℂ (Cfg d N),
      x ≠ 0 ∧ Matrix.toEuclideanLin (Interaction.translationInvariant hN A).hamiltonian x = 0)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      ∀ z ∈ spectrum ℂ (Interaction.translationInvariant hN A).hamiltonian,
        z.re = 0 ∨ δ ≤ z.re)
    (hSymA : ∀ (N : ℕ) (hN : 2 ≤ N) (g : G),
      Commute (Interaction.translationInvariant hN A).hamiltonian
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ)))
    (hSymB : ∀ (N : ℕ) (hN : 2 ≤ N) (g : G),
      Commute (Interaction.translationInvariant hN B).hamiltonian
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ))) :
    SymmetricGappedInteractionPath U A B := by
  have hAffine (γ : ℝ) : A + γ • (B - A) = (1 - γ) • A + γ • B := by module
  have hHam (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) :
      (Interaction.translationInvariant hN (A + γ • (B - A))).hamiltonian =
        (Interaction.translationInvariant hN A).hamiltonian +
          γ • ((Interaction.translationInvariant hN B).hamiltonian -
            (Interaction.translationInvariant hN A).hamiltonian) := by
    have hmap (i : Fin N) :
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (A + γ • (B - A)) =
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A +
            γ • (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B -
              placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A) := by
      let f := (placeAlongHom (X := fun _ ↦ Fin d) (ringWindow hN i)).toAlgHom.toLinearMap
        |>.restrictScalars ℝ
      change f (A + γ • (B - A)) = f A + γ • (f B - f A)
      simp only [map_add, map_smul, map_sub]
    simp only [Interaction.hamiltonian, Interaction.translates_term, hmap]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum, smul_sub]
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
    have hHA : (Interaction.translationInvariant hN A).hamiltonian.PosSemidef :=
      Interaction.posSemidef_hamiltonian fun i ↦
        posSemidef_placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) hA
    have hHAB : (Interaction.translationInvariant hN A).hamiltonian ≤
        (Interaction.translationInvariant hN B).hamiltonian := by
      simp only [Interaction.hamiltonian]
      exact Finset.sum_le_sum fun i _ ↦
        placeAlong_le_placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) hAB
    have h := Matrix.spectrum_gap_interpolation_of_le_of_nontrivial_kernel
      (Interaction.translationInvariant hN A).hamiltonian
      (Interaction.translationInvariant hN B).hamiltonian
      hHA hHAB (hker N hN) δ γ hγ.1
      (Matrix.orthogonal_quadratic_gap_of_spectrum_separated _ hHA.isHermitian
        (hSpec N hN)) (hzero N hN)
    rw [← hHam] at h
    exact ⟨0, h.1, by simpa using h.2⟩
  · intro γ hγ g N hN
    rw [hHam]
    exact (hSymA N hN g).add_left (((hSymB N hN g).sub_left (hSymA N hN g)).smul_left γ)

end MPSTensor
