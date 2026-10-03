/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.UnitaryVirtualGauge
import TNLean.MPS.Symmetry.PolarGappedInteractionPath
import TNLean.MPS.Symmetry.SymmetricMPS
import TNLean.MPS.Irreducible.PerronGauge

/-!
# Preparing the symmetric polar path from an injective tensor

Perron normalization replaces an injective tensor by a unital representative
without changing any canonical parent interaction. On-site symmetry is
preserved by the nonzero rescaling and the virtual gauge. The virtual
covariance can then be chosen unitary, and the polar deformation gives an
independent symmetric gapped interaction path to the isometric parent.

**Scope restriction (one-site injective tensors):** this is the single-block,
one-site injective case of arXiv:1010.3732, Section II.C and Appendix A.
The original tensor is not assumed normalized, and unitary virtual covariance
is derived rather than assumed. The several-block case is documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Section II.C
- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix Product State Representations*
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

/-- Every injective tensor has a unital representative with the same
canonical parent interactions, obtained by nonzero rescaling and virtual
gauge. Source: arXiv:1010.3732, Section II.C, standard form before the
symmetry-preserving polar decomposition; arXiv:quant-ph/0608197,
Theorem `Th:TIcanonical`, proof lines 765--770. -/
theorem exists_unital_parent_representative_of_isInjective
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A) :
    ∃ (B : MPSTensor d D) (c : ℂ), c ≠ 0 ∧ GaugeEquiv (c • A) B ∧
      Kraus.IsInjective B ∧ Kraus.transferMap B 1 = 1 ∧
      ∀ L, parentInteraction A L = parentInteraction B L := by
  have hIrr := Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (Kraus.injective_implies_irreducibleCP A hA)
  obtain ⟨B, r, _, _, hr, _, hSum, hGauge⟩ := exists_unital_data_of_irreducible
    A hIrr (exists_apply_ne_zero_of_isNormal hA.isNormal)
  let c : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr hr)
  refine ⟨B, c, hc, hGauge, isInjective_of_gaugeEquiv (hA.smul hc) hGauge, ?_, ?_⟩
  · simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hSum
  · intro L
    apply parentInteraction_eq_of_groundSpace_eq
    rw [← groundSpace_smul_eq A c hc L]
    exact hGauge.groundSpace_eq L

/-- An unital injective tensor with on-site symmetry has a unitary virtual
covariance for every symmetry element. No virtual matrices are assumed.
Source: arXiv:1010.3732, Section II.C, “Isometric form and symmetries”. -/
theorem exists_unitary_virtual_covariance_of_isOnSiteSymmetric_unital
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)) :
    ∃ X : G → Matrix.unitaryGroup (Fin D) ℂ, ∀ g,
      rotatePhysical (U g) A = fun i => (X g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (X g : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have hGauge := gaugeEquiv_twistedTensor_of_injective A hA _ hSym
  choose X hX using fun g => exists_unitary_covariance_of_isInjective_unital
    hA hNorm (U g) (SetLike.coe_mem _) (hGauge g)
  exact ⟨X, hX⟩

/-- The canonical parent of any on-site symmetric injective tensor is joined
to the isometric parent of a normalized representative by an independent
symmetric gapped interaction path. Source: arXiv:1010.3732, Section II.C,
“Isometric form and symmetries”, including the preceding gauge preparation. -/
theorem exists_prepared_polarGappedInteractionPath_of_isOnSiteSymmetric
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)) :
    ∃ (B : MPSTensor d D) (c : ℂ), c ≠ 0 ∧ GaugeEquiv (c • A) B ∧
      Kraus.IsInjective B ∧ Kraus.transferMap B 1 = 1 ∧
      (∀ L, parentInteraction A L = parentInteraction B L) ∧
      Nonempty (SymmetricGappedInteractionPath U
        (LinearMap.toMatrix' (parentInteraction (polarIsometricTensor B) 2))
        (LinearMap.toMatrix' (parentInteraction A 2))) := by
  obtain ⟨B, c, hc, hGauge, hB, hNorm, hParent⟩ :=
    exists_unital_parent_representative_of_isInjective A hA
  have hSymB := (hSym.smul c).of_gaugeEquiv hGauge
  obtain ⟨X, hX⟩ := exists_unitary_virtual_covariance_of_isOnSiteSymmetric_unital
    B hB hNorm U hSymB
  refine ⟨B, c, hc, hGauge, hB, hNorm, hParent, ?_⟩
  rw [hParent 2]
  exact ⟨polarGappedInteractionPath U B hB X hX⟩

end MPSTensor
