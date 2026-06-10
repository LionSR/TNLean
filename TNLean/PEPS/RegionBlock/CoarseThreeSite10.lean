import TNLean.PEPS.RegionBlock.CoarseThreeSite9

/-!
# The relaxed-triple merge collapse: the final assembly

This file completes the relaxed-triple merge collapse begun in
`TNLean.PEPS.RegionBlock.CoarseThreeSite9`. The merged-summand layer (the host merge, the
host-merge fiber count, and the per-triple merged summand) is assembled with the
configuration expansion of the whole-bundle red inserted coefficient into the collapse: the
M-coupled relaxed-triple sum is the host-merge fiber product times the whole-bundle red
inserted coefficient of the bond-model-conjugated matrix.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

open scoped Classical in
/-- **The configuration expansion of the whole-bundle red inserted coefficient.** The
whole-bundle red inserted coefficient of the bond-model-conjugated matrix, with the host
physical leg the fused blue/complement leg, expands as a double sum over global virtual
configurations: the red configuration `ζr` carries the red index, a second configuration `η`
the host index, coupled diagonally on the red-to-complement crossings by the agreement and on
the red-to-blue crossings by the matrix.

Source: arXiv:1804.04964, Section 3, lines 254--583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem redBundleInsertedCoeff_bondModelMatrix_eq_configSum
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    redBundleInsertedCoeff (G := G) A F.frame.red F.frame.blue (bondModelMatrix (G := G) F M)
        σr ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc) =
      ∑ ζr : VirtualConfig A, ∑ η : VirtualConfig A,
        (if ∀ g : Edge G, IsCrossingEdge (G := G) A F.frame.red F.frame.complement g →
              ζr g = η g then
            bondModelMatrix (G := G) F M
              (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                (regionBoundaryLabel (G := G) A F.frame.red ζr))
              (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                (regionBoundaryLabel (G := G) A F.frame.red η))
          else 0) *
          (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => ζr ie.1) (σr w)) *
          (∏ w : {w : V // w ∈ Finset.univ \ F.frame.red},
            A.component w.1 (fun ie => η ie.1)
              ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc w)) := by
  classical
  rw [redBundleInsertedCoeff_eq]
  -- Pull the red blocked-region weight out of the inner host sum, then group the red
  -- configurations through `blockedWeight_as_configSum`.
  have hred : ∀ μ : RegionBoundaryConfig (G := G) A F.frame.red,
      (∑ ν : RegionBoundaryConfig (G := G) A F.frame.red,
          (if SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue μ ν then
              bondModelMatrix (G := G) F M
                (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue μ)
                (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue ν)
            else 0) *
            regionBlockedWeight (G := G) A F.frame.red μ σr *
            regionBlockedWeight (G := G) A (Finset.univ \ F.frame.red)
              (regionComplementBoundaryConfig (G := G) A F.frame.red ν)
              ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc)) =
        (∑ ν : RegionBoundaryConfig (G := G) A F.frame.red,
            (if SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue μ ν then
                bondModelMatrix (G := G) F M
                  (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue μ)
                  (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue ν)
              else 0) *
              regionBlockedWeight (G := G) A (Finset.univ \ F.frame.red)
                (regionComplementBoundaryConfig (G := G) A F.frame.red ν)
                ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc)) *
          regionBlockedWeight (G := G) A F.frame.red μ σr := by
    intro μ; rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun ν _ => ?_); ring
  rw [Finset.sum_congr rfl (fun μ _ => hred μ),
    blockedWeight_as_configSum (R := F.frame.red) σr]
  refine Finset.sum_congr rfl (fun ζr _ => ?_)
  -- Collapse the host boundary configuration sum to a host configuration sum, keeping the
  -- red vertex product factored out.
  have hhost : (∑ ν : RegionBoundaryConfig (G := G) A F.frame.red,
        (if SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue
              (regionBoundaryLabel (G := G) A F.frame.red ζr) ν then
            bondModelMatrix (G := G) F M
              (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                (regionBoundaryLabel (G := G) A F.frame.red ζr))
              (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue ν)
          else 0) *
          regionBlockedWeight (G := G) A (Finset.univ \ F.frame.red)
            (regionComplementBoundaryConfig (G := G) A F.frame.red ν)
            ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc)) =
      ∑ η : VirtualConfig A,
        (if ∀ g : Edge G, IsCrossingEdge (G := G) A F.frame.red F.frame.complement g →
              ζr g = η g then
            bondModelMatrix (G := G) F M
              (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                (regionBoundaryLabel (G := G) A F.frame.red ζr))
              (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                (regionBoundaryLabel (G := G) A F.frame.red η))
          else 0) *
          ∏ w : {w : V // w ∈ Finset.univ \ F.frame.red},
            A.component w.1 (fun ie => η ie.1)
              ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc w) := by
    -- Reindex the host boundary sum through the complement boundary equivalence.
    rw [← Equiv.sum_comp (regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm
      (fun ν => (if SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue
            (regionBoundaryLabel (G := G) A F.frame.red ζr) ν then
          bondModelMatrix (G := G) F M
            (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
              (regionBoundaryLabel (G := G) A F.frame.red ζr))
            (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue ν)
        else 0) *
        regionBlockedWeight (G := G) A (Finset.univ \ F.frame.red)
          (regionComplementBoundaryConfig (G := G) A F.frame.red ν)
          ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc))]
    -- Normalize the host weight argument `compl (e.symm νh) = νh`, then group.
    rw [Finset.sum_congr rfl (g := fun νh => (if SameAwayFromRBBundle (G := G) A F.frame.red
          F.frame.blue (regionBoundaryLabel (G := G) A F.frame.red ζr)
          ((regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm νh) then
        bondModelMatrix (G := G) F M
          (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
            (regionBoundaryLabel (G := G) A F.frame.red ζr))
          (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
            ((regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm νh))
      else 0) *
      regionBlockedWeight (G := G) A (Finset.univ \ F.frame.red) νh
        ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc))
      (fun νh _ => by
        rw [show regionComplementBoundaryConfig (G := G) A F.frame.red
              ((regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm νh) = νh from
          (regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).apply_symm_apply νh])]
    rw [blockedWeight_as_configSum (R := Finset.univ \ F.frame.red)
      ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc)
      (fun νh => (if SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue
            (regionBoundaryLabel (G := G) A F.frame.red ζr)
            ((regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm νh) then
          bondModelMatrix (G := G) F M
            (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
              (regionBoundaryLabel (G := G) A F.frame.red ζr))
            (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
              ((regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm νh))
        else 0))]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    -- The symm-reindexed host label of `η` is the red boundary label of `η`.
    rw [show (regionComplementBoundaryConfigEquiv (G := G) A F.frame.red).symm
          (regionBoundaryLabel (G := G) A (Finset.univ \ F.frame.red) η) =
        regionBoundaryLabel (G := G) A F.frame.red η from by
      funext f
      simp only [regionComplementBoundaryConfigEquiv, Equiv.coe_fn_symm_mk,
        regionBoundaryLabel_apply, regionBoundaryEdgeComplEquiv_apply_coe]]
    by_cases hag : SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue
        (regionBoundaryLabel (G := G) A F.frame.red ζr)
        (regionBoundaryLabel (G := G) A F.frame.red η)
    · rw [if_pos hag,
        if_pos ((sameAwayFromRBBundle_regionBoundaryLabel_iff F hP ζr η).mp hag)]
    · rw [if_neg hag,
        if_neg (fun h => hag
          ((sameAwayFromRBBundle_regionBoundaryLabel_iff F hP ζr η).mpr h)), zero_mul]
  -- Multiply the host collapse by the factored red vertex product.
  rw [hhost, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  ring

open scoped Classical in
/-- **The relaxed-triple merge collapse.** The M-coupled relaxed-triple sum equals the
host-merge fiber product times the whole-bundle red inserted coefficient of the
bond-model-conjugated matrix, with the host physical leg the fused blue/complement leg. This
is the matrix-carrying analogue of `TNLean.PEPS.agreeingTripleSum_collapse`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 254--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem relaxedTripleSum_collapse
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    (∑ t ∈ (Finset.univ : Finset (VirtualConfig A × VirtualConfig A × VirtualConfig A)).filter
        (fun t => CrossTripleAgreesAwayRB F t.1 t.2.1 t.2.2),
      bondModelMatrix (G := G) F M
          (crossingLabel (G := G) A F.frame.red F.frame.blue t.1)
          (fun g => t.2.1 g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue) *
        (∏ w : {w : V // w ∈ F.frame.red},
            A.component w.1 (fun ie => t.1 ie.1) (σr w)) *
        (∏ w : {w : V // w ∈ F.frame.complement},
            A.component w.1 (fun ie => t.2.2 ie.1) (σc w)) *
        (∏ w : {w : V // w ∈ F.frame.blue},
            A.component w.1 (fun ie => t.2.1 ie.1) (σb w))) =
      hostMergeFiberProd F •
        redBundleInsertedCoeff (G := G) A F.frame.red F.frame.blue (bondModelMatrix (G := G) F M)
          σr ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc) := by
  classical
  -- Replace each summand by its merged form.
  rw [relaxedTripleSum_mergedSummand_eq F hP M σr σb σc]
  -- Reindex the triple `(ζr, (ζb, ζc))` and split the relaxed agreement filter.
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [redBundleInsertedCoeff_bondModelMatrix_eq_configSum F hP M σr σb σc, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun ζr _ => ?_)
  -- For fixed `ζr`, collapse the `(ζb, ζc)` pair sum through the host merge, with the
  -- red-to-complement agreement carried as an indicator inside the summand.
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  -- The configuration summand of the host index, as a function of one global configuration.
  let hostCoeff : VirtualConfig A → ℂ := fun η =>
    (if ∀ gg : Edge G,
          IsCrossingEdge (G := G) A F.frame.red F.frame.complement gg → ζr gg = η gg then
        bondModelMatrix (G := G) F M
            (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
              (regionBoundaryLabel (G := G) A F.frame.red ζr))
            (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
              (regionBoundaryLabel (G := G) A F.frame.red η))
      else 0) *
      (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => ζr ie.1) (σr w)) *
      ∏ w : {w : V // w ∈ Finset.univ \ F.frame.red},
        A.component w.1 (fun ie => η ie.1)
          ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc w)
  -- The triple sum equals the host-pair sum of `G ∘ hostMerge`; its fiberwise collapse is the
  -- configuration sum, the host index of the configuration expansion.
  have hpair : (∑ ζb : VirtualConfig A, ∑ ζc : VirtualConfig A,
        (if CrossTripleAgreesAwayRB F ζr ζb ζc then
            bondModelMatrix (G := G) F M
                (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                  (regionBoundaryLabel (G := G) A F.frame.red ζr))
                (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
                  (regionBoundaryLabel (G := G) A F.frame.red (hostMerge F ζb ζc))) *
              (∏ w : {w : V // w ∈ F.frame.red},
                  A.component w.1 (fun ie => ζr ie.1) (σr w)) *
              ∏ w : {w : V // w ∈ Finset.univ \ F.frame.red},
                A.component w.1 (fun ie => hostMerge F ζb ζc ie.1)
                  ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc w)
          else 0)) =
      ∑ p ∈ Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          HostPairAgrees F p.1 p.2),
        hostCoeff (hostMerge F p.1 p.2) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun ζb _ => Finset.sum_congr rfl (fun ζc _ => ?_))
    change _ = (if HostPairAgrees F ζb ζc then hostCoeff (hostMerge F ζb ζc) else 0)
    by_cases hbc : HostPairAgrees F ζb ζc
    · by_cases hrh : RedHostAgrees F ζr ζb ζc
      · rw [if_pos ((crossTripleAgreesAwayRB_iff F ζr ζb ζc).mpr ⟨hbc, hrh⟩), if_pos hbc]
        change _ = (if ∀ gg : Edge G,
            IsCrossingEdge (G := G) A F.frame.red F.frame.complement gg →
              ζr gg = hostMerge F ζb ζc gg then _ else _) * _ * _
        rw [if_pos (fun gg hgg => hrh gg hgg)]
      · rw [if_neg (fun h => hrh ((crossTripleAgreesAwayRB_iff F ζr ζb ζc).mp h).2), if_pos hbc]
        change _ = (if ∀ gg : Edge G,
            IsCrossingEdge (G := G) A F.frame.red F.frame.complement gg →
              ζr gg = hostMerge F ζb ζc gg then _ else _) * _ * _
        rw [if_neg (fun h => hrh (fun gg hgg => h gg hgg)), zero_mul, zero_mul]
    · rw [if_neg (fun h => hbc ((crossTripleAgreesAwayRB_iff F ζr ζb ζc).mp h).1), if_neg hbc]
  rw [hpair, hostMerge_fiberwise_collapse F hostCoeff, Finset.smul_sum]

end PEPS
end TNLean
