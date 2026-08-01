/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseCorner
import TNLean.MPS.MPDO.CPSVBlocking
import TNLean.MPS.MPDO.CPSVFigureEight

/-!
# Conditional Gram identity for an exact two-site sector gauge

An identity-dressed marked realization in the physical-letter span, with the
same reflected target as the gauge-dressed corner, determines the Gram
conjugation of an exact two-site sector gauge.  Normality then makes the gauge
Gram matrix a positive scalar multiple of the identity.

The identity-dressed realization is assumed here, not constructed.  Thus these
results isolate the remaining implication in Appendix C.4 and do not complete
the two-site unitary-gauge argument.

## Main results

* `TwoSiteExactSectorGauge.IdentityMarkedRealization`
* `TwoSiteExactSectorGauge.gramDressing_gauge_eq_one_of_identityMarkedRealization`
* `TwoSiteExactSectorGauge.gauge_gram_eq_pos_smul_one_of_identityMarkedRealization`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, Figures 7--8, lines 1898--1921, and Appendix C.4,
  lines 2048--2057
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- An identity-dressed marked realization in the physical-letter span, with
the same reflected target as the gauge-dressed marked chains.

**Scope restriction (conditional identity-dressed marked realization):** This
structure packages the local realization implicit at CPSV16 Appendix C.4,
line 2048; it is supplied as data rather than derived from the tensor-attached
algebra clause.  See
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and lines
1898--1921, applied at Appendix C.4, lines 2048--2057. -/
structure IdentityMarkedRealization (S : TwoSiteExactSectorGauge H)
    (γ : Fin H.labelCount) where
  /-- Coefficients realizing the identity-dressed horizontal slices as
  physical letters of the two-site blocking.

  Source: arXiv:1606.00608, Appendix C.4, line 2048. -/
  fId : Fin (S.decomposition.bondDim (S.relabel γ) *
      S.decomposition.bondDim (S.relabel γ)) →
    Fin ((d * d) * (d * d)) → ℂ
  /-- The coefficients realize each identity-dressed open-bond matrix.

  Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and
  lines 1898--1921, applied at Appendix C.4, line 2048. -/
  physical : ∀ u,
    MPSTensor.linearMarkedTensor fId (blockTwo M).toMPSTensor u =
      horizontalSlice
        (gramDressing (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ))) u.divNat u.modNat
  /-- At every positive tail length, the identity-dressed marked chains have the
  reflected-adjoint target used for the gauge-dressed marked chains.

  Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and
  lines 1898--1921, applied at Appendix C.4, lines 2048--2057. -/
  target : ∀ (N : ℕ), 0 < N → ∀
    (r s : Fin (S.decomposition.bondDim (S.relabel γ)))
    (σ τ : Fin N → Fin (d * d)),
    markedChainCoefficient
        (gramDressing
          (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (blockTwo M) r s (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient
        (reflectedAdjoint
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (adjointTensor (blockTwo M)) r s
        (List.ofFn σ).reverse (List.ofFn τ).reverse

/-- An identity-dressed physical-letter marked realization with the same
reflected target as the exact gauge-dressed corner at every positive tail
length forces the two Gram dressings to agree.

**Scope restriction (conditional identity-dressed marked realization):** The
theorem assumes the physical-letter realization implicit at CPSV16 Appendix
C.4, line 2048; it is not derived from the algebra clause and does not resolve
the unconditional realization or conclusion of Appendix C.4.  See
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and lines
1898--1921, applied at Appendix C.4, lines 2048--2057. -/
theorem gramDressing_gauge_eq_one_of_identityMarkedRealization
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount)
    (R : IdentityMarkedRealization S γ) :
    gramDressing (S.gauge γ)
        (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ)) =
      gramDressing (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
        (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ)) := by
  classical
  obtain ⟨V, c, _, hc, hCorner⟩ := S.exists_blockTwo_gauge_sector_corner γ
  let fGauge := cornerGramCoefficients V (S.gauge γ) c
  have hTrace : ∀ (L : ℕ), 0 < L → ∀
      (u : Fin (S.decomposition.bondDim (S.relabel γ) *
        S.decomposition.bondDim (S.relabel γ)))
      (w : Fin L → Fin ((d * d) * (d * d))),
      Matrix.trace
          (MPSTensor.linearMarkedTensor fGauge (blockTwo M).toMPSTensor u *
            MPSTensor.evalWord (blockTwo M).toMPSTensor (List.ofFn w)) =
        Matrix.trace
          (MPSTensor.linearMarkedTensor R.fId (blockTwo M).toMPSTensor u *
            MPSTensor.evalWord (blockTwo M).toMPSTensor (List.ofFn w)) := by
    intro L hL u w
    rw [show MPSTensor.linearMarkedTensor fGauge (blockTwo M).toMPSTensor u =
        horizontalSlice
          (gramDressing (S.gauge γ)
            (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ))) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ))
        V (S.gauge γ) c hc hCorner u]
    rw [R.physical u]
    rw [evalWord_toMPSTensor_ofFn]
    exact
      (S.markedChainCoefficient_gauge_eq_reflectedAdjoint hM γ L
        u.divNat u.modNat (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat)).trans
      (R.target L hL u.divNat u.modNat
        (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat)).symm
  have hMarks :
      MPSTensor.linearMarkedTensor fGauge (blockTwo M).toMPSTensor =
        MPSTensor.linearMarkedTensor R.fId (blockTwo M).toMPSTensor :=
    (IsCPSVCanonicalForm_toMPSTensor_blockTwo hCanonical).linearMarkedTensor_eq_of_trace_agree
      (blockTwo M).toMPSTensor fGauge R.fId hTrace
  funext v
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  ext r s
  have hSlice := congrFun hMarks (finProdFinEquiv (r, s))
  rw [show MPSTensor.linearMarkedTensor fGauge (blockTwo M).toMPSTensor
        (finProdFinEquiv (r, s)) =
      horizontalSlice
        (gramDressing (S.gauge γ)
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (finProdFinEquiv (r, s)).divNat (finProdFinEquiv (r, s)).modNat by
    exact linearMarkedTensor_cornerGramCoefficients
      (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ))
      V (S.gauge γ) c hc hCorner (finProdFinEquiv (r, s)),
    R.physical] at hSlice
  simpa only [horizontalSlice, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] using congrFun (congrFun hSlice a) b

/-- Under the same conditional identity-dressed marked realization, the Gram
matrix of the exact two-site sector gauge is a positive real scalar multiple
of the identity.

**Scope restriction (conditional identity-dressed marked realization):** The
theorem assumes the physical-letter realization implicit at CPSV16 Appendix
C.4, line 2048; it is not derived from the algebra clause and does not establish
the unconditional realization or conclusion of Appendix C.4.  See
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and lines
1898--1921, applied at Appendix C.4, lines 2048--2057. -/
theorem gauge_gram_eq_pos_smul_one_of_identityMarkedRealization
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount)
    (R : IdentityMarkedRealization S γ) :
    ∃ ω : ℝ, 0 < ω ∧
      (S.gauge γ : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
          (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ * S.gauge γ =
        (ω : ℂ) • 1 := by
  have hDress := S.gramDressing_gauge_eq_one_of_identityMarkedRealization
    hCanonical hM γ R
  have hNormalTensor : MPSTensor.IsNormalTensor
      (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ)) :=
    (MPSTensor.isNormalTensor_cast_iff (S.bondDim_eq γ) (H.tensor γ)).2
      (H.isCPSVBNT.blocks_normal γ)
  apply hNormalTensor.isNormal.gram_eq_pos_smul_one_of_gram_conj_eq
    (Matrix.isUnits_det_units (S.gauge γ))
  intro v
  simpa [gramDressing] using congrFun hDress v

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
