/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseSpectrum

/-!
# Relabelled ambient coordinates for the two-site BNT decomposition

The sector matching between the one-site and two-site vertical canonical
decompositions pulls the two-site bond dimensions, multiplicities, and positive
weights back to the one-site label set.  The induced equivalence of retained
coordinates turns the two-site vertical coisometry into a coisometry whose rows
are indexed by these relabelled sectors.

The relabelled coisometry carries native two-site block diagonals to the pulled-
back block diagonals.  The one-site and matched two-site multiplicity traces
coincide, giving the common normalization used by the outer maps of Appendix
C.4.

## Main definitions

* `relabeledTwoSiteBondDim`
* `relabeledTwoSiteMultiplicity`
* `relabeledTwoSiteWeight`
* `RelabeledTwoSiteSectorAlgebra`
* `RelabeledTwoSiteWeightedSectorSpace`
* `relabeledTwoSiteRetainedEquiv`
* `relabeledTwoSiteCoisometry`

## Main results

* `relabeledTwoSiteCoisometry_coisometry`
* `verticalSectorBlockDiagonal_relabel`
* `relabeledTwoSiteCoisometry_forward`
* `relabeledTwoSiteCoisometry_reconstruction`
* `relabeledTwoSiteMultiplicityTrace_eq_oneSite`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 2048--2064.
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteMultiplicitySpectrum

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- The two-site bond dimensions pulled back along the sector matching.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
abbrev relabeledTwoSiteBondDim (S : TwoSiteMultiplicitySpectrum H) :
    Fin H.labelCount → ℕ :=
  fun γ ↦ S.decomposition.bondDim (S.relabel γ)

/-- The two-site multiplicities pulled back along the sector matching.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
abbrev relabeledTwoSiteMultiplicity (S : TwoSiteMultiplicitySpectrum H) :
    Fin H.labelCount → ℕ :=
  fun γ ↦ S.decomposition.multiplicity (S.relabel γ)

/-- The two-site multiplicity weights pulled back along the sector matching.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2064. -/
abbrev relabeledTwoSiteWeight (S : TwoSiteMultiplicitySpectrum H) :
    (γ : Fin H.labelCount) → Fin (S.relabeledTwoSiteMultiplicity γ) → ℂ :=
  fun γ ↦ S.decomposition.weight (S.relabel γ)

/-- The two-site simple-sector algebra indexed by the matched one-site labels.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
abbrev RelabeledTwoSiteSectorAlgebra (S : TwoSiteMultiplicitySpectrum H) :=
  VerticalSectorAlgebra S.relabeledTwoSiteBondDim

/-- The two-site weighted-sector family indexed by the matched one-site labels.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
abbrev RelabeledTwoSiteWeightedSectorSpace
    (S : TwoSiteMultiplicitySpectrum H) :=
  VerticalWeightedSectorSpace S.relabeledTwoSiteBondDim
    S.relabeledTwoSiteMultiplicity

/-- Relabel the retained two-site coordinate from the matched one-site labels
to the native labels of the two-site vertical decomposition.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
def relabeledTwoSiteRetainedEquiv (S : TwoSiteMultiplicitySpectrum H) :
    Fin (∑ q : Fin (∑ γ : Fin H.labelCount,
      S.relabeledTwoSiteMultiplicity γ),
        verticalCopyDim S.relabeledTwoSiteBondDim
          S.relabeledTwoSiteMultiplicity q) ≃
      Fin (∑ q : Fin (∑ β : Fin S.decomposition.labelCount,
        S.decomposition.multiplicity β),
          verticalCopyDim S.decomposition.bondDim
            S.decomposition.multiplicity q) :=
  (verticalSectorFinEquiv S.relabeledTwoSiteBondDim
      S.relabeledTwoSiteMultiplicity).symm |>.trans
    ((Equiv.sigmaCongr S.relabel fun _ ↦ Equiv.refl _).trans
      (verticalSectorFinEquiv S.decomposition.bondDim
        S.decomposition.multiplicity))

/-- On a relabelled sector coordinate, the retained-coordinate equivalence
changes only the sector label.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
@[simp]
theorem relabeledTwoSiteRetainedEquiv_apply
    (S : TwoSiteMultiplicitySpectrum H) (γ : Fin H.labelCount)
    (x : Fin (S.relabeledTwoSiteMultiplicity γ) ×
      Fin (S.relabeledTwoSiteBondDim γ)) :
    S.relabeledTwoSiteRetainedEquiv
        (verticalSectorFinEquiv S.relabeledTwoSiteBondDim
          S.relabeledTwoSiteMultiplicity ⟨γ, x⟩) =
      verticalSectorFinEquiv S.decomposition.bondDim
        S.decomposition.multiplicity ⟨S.relabel γ, x⟩ := by
  simp only [relabeledTwoSiteRetainedEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  unfold Equiv.sigmaCongr
  rfl

/-- The two-site vertical coisometry with its retained rows indexed by the
matched one-site labels.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
def relabeledTwoSiteCoisometry (S : TwoSiteMultiplicitySpectrum H) :
    Matrix
      (Fin (∑ q : Fin (∑ γ : Fin H.labelCount,
        S.relabeledTwoSiteMultiplicity γ),
          verticalCopyDim S.relabeledTwoSiteBondDim
            S.relabeledTwoSiteMultiplicity q))
      (Fin (d * d)) ℂ :=
  Matrix.reindex S.relabeledTwoSiteRetainedEquiv.symm (Equiv.refl _)
    S.decomposition.verticalCoisometry

/-- Relabelling the retained rows preserves the coisometry identity.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
theorem relabeledTwoSiteCoisometry_coisometry
    (S : TwoSiteMultiplicitySpectrum H) :
    S.relabeledTwoSiteCoisometry * S.relabeledTwoSiteCoisometryᴴ = 1 := by
  rw [relabeledTwoSiteCoisometry, Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ
      S.relabeledTwoSiteRetainedEquiv.symm (Equiv.refl _)
        S.decomposition.verticalCoisometry *
    Matrix.reindexLinearEquiv ℂ ℂ
      (Equiv.refl _) S.relabeledTwoSiteRetainedEquiv.symm
        S.decomposition.verticalCoisometryᴴ = 1
  rw [Matrix.reindexLinearEquiv_mul, S.decomposition.coisometry,
    Matrix.reindexLinearEquiv_one]

/-- Relabelling the retained coordinate pulls a native two-site block diagonal
back along the sector matching.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
theorem verticalSectorBlockDiagonal_relabel
    (S : TwoSiteMultiplicitySpectrum H)
    (Y : VerticalWeightedSectorSpace S.decomposition.bondDim
      S.decomposition.multiplicity) :
    Matrix.reindex S.relabeledTwoSiteRetainedEquiv.symm
        S.relabeledTwoSiteRetainedEquiv.symm
        (verticalSectorBlockDiagonal S.decomposition.bondDim
          S.decomposition.multiplicity Y) =
      verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity (fun γ ↦ Y (S.relabel γ)) := by
  ext i j
  obtain ⟨⟨γ, x⟩, rfl⟩ :=
    (verticalSectorFinEquiv S.relabeledTwoSiteBondDim
      S.relabeledTwoSiteMultiplicity).surjective i
  obtain ⟨⟨δ, y⟩, rfl⟩ :=
    (verticalSectorFinEquiv S.relabeledTwoSiteBondDim
      S.relabeledTwoSiteMultiplicity).surjective j
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  change verticalSectorBlockDiagonal S.decomposition.bondDim
      S.decomposition.multiplicity Y
        (S.relabeledTwoSiteRetainedEquiv
          (verticalSectorFinEquiv S.relabeledTwoSiteBondDim
            S.relabeledTwoSiteMultiplicity ⟨γ, x⟩))
        (S.relabeledTwoSiteRetainedEquiv
          (verticalSectorFinEquiv S.relabeledTwoSiteBondDim
            S.relabeledTwoSiteMultiplicity ⟨δ, y⟩)) = _
  rw [S.relabeledTwoSiteRetainedEquiv_apply,
    S.relabeledTwoSiteRetainedEquiv_apply]
  by_cases hγδ : γ = δ
  · subst δ
    simp
  · rw [verticalSectorBlockDiagonal_apply_ne _ _ _
      (S.relabel.injective.ne hγδ)]
    rw [verticalSectorBlockDiagonal_apply_ne _ _ _ hγδ]

/-- A native two-site compression identity becomes the corresponding identity
in the relabelled retained coordinates.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
theorem relabeledTwoSiteCoisometry_forward
    (S : TwoSiteMultiplicitySpectrum H)
    (X : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (Y : VerticalWeightedSectorSpace S.decomposition.bondDim
      S.decomposition.multiplicity)
    (hForward : S.decomposition.verticalCoisometry * X *
      S.decomposition.verticalCoisometryᴴ =
        verticalSectorBlockDiagonal S.decomposition.bondDim
          S.decomposition.multiplicity Y) :
    S.relabeledTwoSiteCoisometry * X * S.relabeledTwoSiteCoisometryᴴ =
      verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity (fun γ ↦ Y (S.relabel γ)) := by
  rw [relabeledTwoSiteCoisometry, Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ
        S.relabeledTwoSiteRetainedEquiv.symm (Equiv.refl _)
        S.decomposition.verticalCoisometry *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) X *
      Matrix.reindexLinearEquiv ℂ ℂ
        (Equiv.refl _) S.relabeledTwoSiteRetainedEquiv.symm
        S.decomposition.verticalCoisometryᴴ = _
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul,
    hForward]
  exact S.verticalSectorBlockDiagonal_relabel Y

/-- A native two-site reconstruction identity becomes the corresponding
identity in the relabelled retained coordinates.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058. -/
theorem relabeledTwoSiteCoisometry_reconstruction
    (S : TwoSiteMultiplicitySpectrum H)
    (X : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (Y : VerticalWeightedSectorSpace S.decomposition.bondDim
      S.decomposition.multiplicity)
    (hReconstruct : X = S.decomposition.verticalCoisometryᴴ *
      verticalSectorBlockDiagonal S.decomposition.bondDim
        S.decomposition.multiplicity Y *
      S.decomposition.verticalCoisometry) :
    X = S.relabeledTwoSiteCoisometryᴴ *
      verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity (fun γ ↦ Y (S.relabel γ)) *
      S.relabeledTwoSiteCoisometry := by
  rw [relabeledTwoSiteCoisometry, Matrix.conjTranspose_reindex,
    ← S.verticalSectorBlockDiagonal_relabel Y]
  change X = Matrix.reindexLinearEquiv ℂ ℂ
        (Equiv.refl _) S.relabeledTwoSiteRetainedEquiv.symm
        S.decomposition.verticalCoisometryᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ
        S.relabeledTwoSiteRetainedEquiv.symm
        S.relabeledTwoSiteRetainedEquiv.symm
        (verticalSectorBlockDiagonal S.decomposition.bondDim
          S.decomposition.multiplicity Y) *
      Matrix.reindexLinearEquiv ℂ ℂ
        S.relabeledTwoSiteRetainedEquiv.symm (Equiv.refl _)
        S.decomposition.verticalCoisometry
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
  exact hReconstruct

/-- The matched one-site and two-site multiplicity matrices have the same
trace \(m_\gamma\).

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2064. -/
theorem relabeledTwoSiteMultiplicityTrace_eq_oneSite
    (S : TwoSiteMultiplicitySpectrum H) (γ : Fin H.labelCount) :
    verticalMultiplicityTrace S.relabeledTwoSiteWeight γ =
      verticalMultiplicityTrace H.weight γ := by
  have h := H.algebraClause.twoMultiplicityTrace_eq_traceScalar
    S.toComparison γ
  change (∑ r, S.decomposition.weight (S.relabel γ) r) =
    ∑ q, H.weight γ q
  exact h

end BNTAlgebraTensorClause.TwoSiteMultiplicitySpectrum

end MPOTensor
