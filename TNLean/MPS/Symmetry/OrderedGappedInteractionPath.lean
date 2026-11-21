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
      haveI : NeZero N := ⟨by omega⟩;
      (Interaction.translationInvariant N A).hamiltonian.mulVec x = 0 →
        (Interaction.translationInvariant N B).hamiltonian.mulVec x = 0)
    (hzero : ∀ (N : ℕ) (hN : 2 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∃ x : EuclideanSpace ℂ (Cfg d N),
      x ≠ 0 ∧ Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian x = 0)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ z ∈ spectrum ℂ (Interaction.translationInvariant N A).hamiltonian,
        z.re = 0 ∨ δ ≤ z.re)
    (hSymA : ∀ (N : ℕ) (hN : 2 ≤ N) (g : G),
      haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N A).hamiltonian
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ)))
    (hSymB : ∀ (N : ℕ) (hN : 2 ≤ N) (g : G),
      haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N B).hamiltonian
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ))) :
    SymmetricGappedInteractionPath U A B := by
  have hAffine (γ : ℝ) : A + γ • (B - A) = (1 - γ) • A + γ • B := by module
  have hHam (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) :
      haveI : NeZero N := ⟨by omega⟩
      (Interaction.translationInvariant N (A + γ • (B - A))).hamiltonian =
        (Interaction.translationInvariant N A).hamiltonian +
          γ • ((Interaction.translationInvariant N B).hamiltonian -
            (Interaction.translationInvariant N A).hamiltonian) := by
    have : NeZero N := ⟨by omega⟩
    have hmap (i : Fin N) :
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (A + γ • (B - A)) =
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A +
            γ • (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B -
              placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) A) := by
      let f := (placeAlongHom (X := fun _ ↦ Fin d) (ringWindow hN i)).toAlgHom.toLinearMap
        |>.restrictScalars ℝ
      change f (A + γ • (B - A)) = f A + γ • (f B - f A)
      simp only [map_add, map_smul, map_sub]
    simp only [Interaction.hamiltonian_translationInvariant_of_le _ hN, hmap]
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
    have : NeZero N := ⟨by omega⟩
    have hHA : (Interaction.translationInvariant N A).hamiltonian.PosSemidef :=
      Interaction.posSemidef_hamiltonian fun _ ↦
        Matrix.LE.le.posSemidef (Interaction.translationInvariant_term_nonneg hA.nonneg _)
    have hHAB : (Interaction.translationInvariant N A).hamiltonian ≤
        (Interaction.translationInvariant N B).hamiltonian := by
      simp only [Interaction.hamiltonian_translationInvariant_of_le _ hN]
      exact Finset.sum_le_sum fun i _ ↦
        placeAlong_le_placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) hAB
    have hAC : (Interaction.translationInvariant N A).hamiltonian ≤
        (Interaction.translationInvariant N A).hamiltonian +
          γ • ((Interaction.translationInvariant N B).hamiltonian -
            (Interaction.translationInvariant N A).hamiltonian) := by
      rw [Matrix.le_iff]
      simpa using (Matrix.le_iff.mp hHAB).smul hγ.1
    have hHC := Matrix.nonneg_iff_posSemidef.mp
      ((Matrix.nonneg_iff_posSemidef.mpr hHA).trans hAC)
    have hgapA : IsGapped (Interaction.translationInvariant N A).hamiltonian 0 δ := by
      refine ⟨?_, fun μ hμ ↦ ?_⟩
      · obtain ⟨x, hx, hxA⟩ := hzero N hN
        rw [groundSpace_zero]
        exact fun hbot ↦ hx (by simpa [hbot] using LinearMap.mem_ker.mpr hxA)
      obtain ⟨k, rfl⟩ := hHA.isHermitian.hasEigenvalue_toEuclideanLin_iff.mp hμ
      have hz : ((hHA.isHermitian.eigenvalues k : ℝ) : ℂ) ∈
          spectrum ℂ (Interaction.translationInvariant N A).hamiltonian := by
        rw [← Matrix.spectrum_toLpLin (p := 2)]
        exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
      rcases hSpec N hN _ hz with h | h
      · left; simpa using h
      · right; exact Complex.real_le_real.mpr (by simpa using h)
    have hgapC := hgapA.of_le hHA hAC fun x hx ↦ by
      have hxB : (Interaction.translationInvariant N B).hamiltonian *ᵥ x.ofLp = 0 :=
        hker N hN _ (by simpa using mem_groundSpace_iff_mulVec.mp hx)
      rw [mem_groundSpace_iff_mulVec, Complex.ofReal_zero, zero_smul] at hx ⊢
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, hx, hxB]
    rw [hHam N hN]
    refine ⟨0, ?_, fun z hz ↦ ?_⟩
    · obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hgapC.1
      rw [← Matrix.spectrum_toLpLin (p := 2)]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)
    have hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin
        ((Interaction.translationInvariant N A).hamiltonian +
          γ • ((Interaction.translationInvariant N B).hamiltonian -
            (Interaction.translationInvariant N A).hamiltonian))) z := by
      rw [← Matrix.spectrum_toLpLin (p := 2)] at hz
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz
    obtain ⟨k, rfl⟩ := hHC.isHermitian.hasEigenvalue_toEuclideanLin_iff.mp hμ
    refine ⟨by simpa using hHC.eigenvalues_nonneg k, ?_⟩
    rcases hgapC.2 _ hμ with h | h
    · left; simpa using h
    · right; simpa using Complex.real_le_real.mp h
  · intro γ hγ g N hN
    have : NeZero N := ⟨by omega⟩
    rw [hHam N hN]
    exact (hSymA N hN g).add_left (((hSymB N hN g).sub_left (hSymA N hN g)).smul_left γ)

end MPSTensor
