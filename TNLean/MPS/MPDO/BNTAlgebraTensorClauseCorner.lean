/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseSpectrum
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.VerticalProductPairBlocks

/-!
# The blocked physical corner of the exact two-site sector gauge

The distinguished copy in the two-site vertical decomposition gives an
isometric physical inclusion for the exact gauge-dressed algebra-side sector.
The corresponding Gram-dressed marked chain therefore has the reflected form
appearing on the right-hand side of Figures 7--8.

This constructs only the gauge-dressed physical corner.  It does not construct
an identity-dressed physical corner for the algebra-side representative and
does not prove the common-target Gram identity required for the unitary gauge
conclusion.

## Main results

* `TwoSiteExactSectorGauge.exists_blockTwo_gauge_sector_corner`
* `TwoSiteExactSectorGauge.markedChainCoefficient_gauge_eq_reflectedAdjoint`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, Figures 7--8, lines 1909--1919, and Appendix C.4,
  lines 2048--2057
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- Every matched two-site sector has an isometric physical corner whose
compression is a positive scalar multiple of the exact gauge-dressed
algebra-side representative.

This is the gauge-dressed half of the marked sector comparison in CPSV16,
Proposition 4.13, Figures 7--8, lines 1909--1919, applied to the two-site
decomposition in Appendix C.4, lines 2048--2057.

**Scope restriction (gauge-dressed corner):** This does not construct an
identity-dressed corner and therefore does not prove the common-target Gram
identity.  The remaining comparison is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1909--1919, and Appendix C.4,
lines 2048--2057. -/
theorem exists_blockTwo_gauge_sector_corner
    (S : TwoSiteExactSectorGauge H) (γ : Fin H.labelCount) :
    ∃ (V : Matrix (Fin (d * d))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) (c : ℂ),
      Vᴴ * V = 1 ∧ (0 : ℂ) < c ∧
        ∀ v : Fin (D * D),
          Vᴴ * verticalTensor (blockTwo M) v * V =
            c • ((S.gauge γ : Matrix
                (Fin (S.decomposition.bondDim (S.relabel γ)))
                (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
              (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
                (H.tensor γ)) v *
              (↑((S.gauge γ)⁻¹) : Matrix
                (Fin (S.decomposition.bondDim (S.relabel γ)))
                (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)) := by
  classical
  let V := blockedReferenceInclusion S.decomposition.bondDim
    S.decomposition.multiplicity S.decomposition.multiplicity_pos
    S.decomposition.verticalCoisometry (S.relabel γ)
  let c := S.decomposition.weight (S.relabel γ)
    ⟨0, S.decomposition.multiplicity_pos (S.relabel γ)⟩
  refine ⟨V, c, ?_, ?_, ?_⟩
  · exact blockedReferenceInclusion_isometry S.decomposition.bondDim
      S.decomposition.multiplicity S.decomposition.multiplicity_pos
      S.decomposition.verticalCoisometry S.decomposition.coisometry (S.relabel γ)
  · exact S.decomposition.weight_pos (S.relabel γ)
      ⟨0, S.decomposition.multiplicity_pos (S.relabel γ)⟩
  · intro v
    rw [← S.tensor_eq γ v]
    exact (blockedReference_compression M S.decomposition.bondDim
      S.decomposition.multiplicity S.decomposition.multiplicity_pos
      S.decomposition.weight S.decomposition.tensor
      S.decomposition.verticalCoisometry S.decomposition.coisometry
      S.decomposition.reconstruction (S.relabel γ) v).symm

/-- The marked chain of the exact gauge-dressed algebra-side sector equals
the reflected-adjoint marked chain of the same representative in the adjoint
two-site blocking.

This is the gauge-dressed Figure 7 identity used on one side of Figure 8 in
CPSV16, Proposition 4.13, lines 1909--1919, for the sector matching of
Appendix C.4, lines 2048--2057.

**Scope restriction (gauge-dressed corner):** The theorem does not compare
this expression with the identity-dressed algebra-side representative and
hence does not prove the common-target Gram identity.  The remaining
comparison is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1909--1919, and Appendix C.4,
lines 2048--2057. -/
theorem markedChainCoefficient_gauge_eq_reflectedAdjoint
    (S : TwoSiteExactSectorGauge H) (hM : IsMPDO M)
    (γ : Fin H.labelCount) (N : ℕ)
    (r s : Fin (S.decomposition.bondDim (S.relabel γ)))
    (σ τ : Fin N → Fin (d * d)) :
    markedChainCoefficient
        (gramDressing (S.gauge γ)
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (blockTwo M) r s (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient
        (reflectedAdjoint
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (adjointTensor (blockTwo M)) r s
        (List.ofFn σ).reverse (List.ofFn τ).reverse := by
  obtain ⟨V, c, _, hc, hcorner⟩ := S.exists_blockTwo_gauge_sector_corner γ
  exact hM.blockTwo.markedChainCoefficient_gramDressing_eq_reflectedAdjoint
    (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ))
    V (S.gauge γ) c hc hcorner N r s σ τ

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
