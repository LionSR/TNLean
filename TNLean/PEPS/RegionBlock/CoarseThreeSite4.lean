import TNLean.PEPS.RegionBlock.CoarseThreeSite3

/-!
# The global fiber-collapse bijection for the normal PEPS theorem

The coarse three-site tensor of `TNLean.PEPS.RegionBlock.CoarseThreeSite` has its
closed-state coefficient written, through the coherent bond models of
`TNLean.PEPS.RegionBlock.CoarseThreeSite2`, as a sum over coarse virtual
configurations of a product of three original blocked-region weights
(`stateCoeff_coarseTensor_eq_threeRegionSum`), and the region boundary
configurations induced by a coarse configuration are read off the bond models
(`TNLean.PEPS.RegionBlock.CoarseThreeSite3`). This file collapses that triple sum
to a constant times the original closed-state coefficient.

The route mirrors the landed two-block collapse
`TNLean.PEPS.stateCoeff_eq_regionComplement`: a coarse virtual configuration `η`
together with the three constrained inner sums of the blocked-region weights is
reindexed by a triple of global virtual configurations of the original tensor
`(ζ_red, ζ_blue, ζ_compl)` whose region boundary labels agree on the shared
crossing edges; merging that triple into one global configuration (the red-incident
edges read `ζ_red`, the remaining blue-incident edges read `ζ_blue`, the rest read
`ζ_compl`) collapses the sum to the closed-state coefficient with the three
regions' interior bond products as multiplicity.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1205--1210 (the one-region-against-complement gluing) and
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Enumeration of the coarse super-edges

The coarse graph is the complete graph on `Fin 3`; its edge set is exactly the
three super-edges `r-b`, `r-c`, `b-c`. A coarse virtual configuration is therefore
determined by its three super-bond values, the fact the reindexing of the triple
sum consumes. -/

/-- Every super-edge of the coarse graph is one of the three named super-edges. -/
theorem coarse_edge_cases (f : Edge coarseGraph) :
    f = coarseEdgeRB ∨ f = coarseEdgeRC ∨ f = coarseEdgeBC := by
  revert f; decide

/-- A coarse virtual configuration is determined by its three super-bond values. -/
theorem coarse_virtualConfig_ext {A : Tensor G d}
    (F : CoarseBlockingFrame (G := G) (d := d) A)
    {η η' : VirtualConfig (F.coarseTensor)}
    (hrb : η coarseEdgeRB = η' coarseEdgeRB)
    (hrc : η coarseEdgeRC = η' coarseEdgeRC)
    (hbc : η coarseEdgeBC = η' coarseEdgeBC) : η = η' := by
  funext f
  rcases coarse_edge_cases f with h | h | h <;> subst h <;> assumption

variable {A : Tensor G d}

/-! ### The crossing-triple reindexing of coarse virtual configurations

The bond models of a coherent frame are equivalences between the three coarse
super-bonds and the three original inter-region crossing configurations. Since a
coarse virtual configuration is determined by its three super-bond values, the
bond models assemble into one product equivalence between coarse virtual
configurations and triples of crossing configurations. This is the change of
variables that turns the triple sum over coarse configurations into a sum over the
original crossing data the merge collapse contracts. -/

/-- **The crossing-triple reindexing.** The product equivalence between coarse
virtual configurations and triples of original crossing configurations, one per
coarse super-edge, assembled from the three bond models. -/
def crossingTripleEquiv (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) :
    VirtualConfig (F.frame.coarseTensor) ≃
      (CrossingConfig (G := G) A F.frame.red F.frame.blue ×
        CrossingConfig (G := G) A F.frame.red F.frame.complement ×
        CrossingConfig (G := G) A F.frame.blue F.frame.complement) where
  toFun η := (F.bondModel coarseEdgeRB (η coarseEdgeRB),
              F.bondModel coarseEdgeRC (η coarseEdgeRC),
              F.bondModel coarseEdgeBC (η coarseEdgeBC))
  invFun t := fun f =>
    if h : f = coarseEdgeRB then h ▸ (F.bondModel coarseEdgeRB).symm t.1
    else if h2 : f = coarseEdgeRC then h2 ▸ (F.bondModel coarseEdgeRC).symm t.2.1
    else if h3 : f = coarseEdgeBC then h3 ▸ (F.bondModel coarseEdgeBC).symm t.2.2
    else absurd ((coarse_edge_cases f).resolve_left h |>.resolve_left h2) h3
  left_inv η := by
    funext f
    dsimp only
    rcases coarse_edge_cases f with h | h | h <;> subst h
    · rw [dif_pos rfl]; exact (F.bondModel coarseEdgeRB).symm_apply_apply _
    · rw [dif_neg (by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeRC).symm_apply_apply _
    · rw [dif_neg (by decide), dif_neg (by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeBC).symm_apply_apply _
  right_inv t := by
    obtain ⟨a, b, c⟩ := t
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · dsimp only; rw [dif_pos rfl]; exact (F.bondModel coarseEdgeRB).apply_symm_apply _
    · dsimp only; rw [dif_neg (show coarseEdgeRC ≠ coarseEdgeRB by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeRC).apply_symm_apply _
    · dsimp only
      rw [dif_neg (show coarseEdgeBC ≠ coarseEdgeRB by decide),
        dif_neg (show coarseEdgeBC ≠ coarseEdgeRC by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeBC).apply_symm_apply _

@[simp] theorem crossingTripleEquiv_apply (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (η : VirtualConfig (F.frame.coarseTensor)) :
    crossingTripleEquiv F η =
      (F.bondModel coarseEdgeRB (η coarseEdgeRB),
        F.bondModel coarseEdgeRC (η coarseEdgeRC),
        F.bondModel coarseEdgeBC (η coarseEdgeBC)) := rfl

/-! ### Crossing labels of a global configuration

The crossing label of a global virtual configuration on a region pair reads its
values on the edges crossing between the two regions. Through the partition every
region boundary edge crosses to exactly one partner region, so a region boundary
configuration is recovered from the two crossing labels on its incident super-edges.
Matching a coarse configuration's induced region boundary configuration against a
global configuration's region boundary label therefore decomposes, per super-edge,
into matching the corresponding crossing label against the bond model. -/

/-- The crossing label of a global virtual configuration on the region pair `R, R'`:
its values on the edges crossing between the two regions. -/
def crossingLabel (A : Tensor G d) (R R' : Finset V) (ζ : VirtualConfig A) :
    CrossingConfig (G := G) A R R' := fun g => ζ g.1

omit [DecidableEq V] [Fintype V] in
@[simp] theorem crossingLabel_apply (A : Tensor G d) (R R' : Finset V) (ζ : VirtualConfig A)
    (g : {g : Edge G // IsCrossingEdge (G := G) A R R' g}) :
    crossingLabel (G := G) A R R' ζ g = ζ g.1 := rfl

omit [Fintype V] [DecidableEq V] in
/-- An edge crossing between `R` and `R''` does not also cross between `R` and `R'`
when the three regions are pairwise disjoint: the shared out-of-`R` endpoint would
lie in both `R'` and `R''`. -/
theorem not_crossing_of_crossing_disjoint {R R' R'' : Finset V}
    (hRR' : Disjoint R R') (hRR'' : Disjoint R R'') (hR'R'' : Disjoint R' R'') {g : Edge G}
    (h : IsCrossingEdge (G := G) A R R'' g) :
    ¬ IsCrossingEdge (G := G) A R R' g := by
  rintro hbad
  rcases h.1 with ⟨hR1, hR2⟩ | ⟨hR1, hR2⟩
  · have hg1n'' : g.1.1 ∉ R'' := (Finset.disjoint_left.mp hRR'') hR1
    have hg1n' : g.1.1 ∉ R' := (Finset.disjoint_left.mp hRR') hR1
    have hg2'' : g.1.2 ∈ R'' := by
      rcases h.2 with ⟨hc1, _⟩ | ⟨_, hc2⟩
      · exact absurd hc1 hg1n''
      · exact hc2
    have hg2' : g.1.2 ∈ R' := by
      rcases hbad.2 with ⟨hc1, _⟩ | ⟨_, hc2⟩
      · exact absurd hc1 hg1n'
      · exact hc2
    exact (Finset.disjoint_left.mp hR'R'') hg2' hg2''
  · have hg2n'' : g.1.2 ∉ R'' := (Finset.disjoint_left.mp hRR'') hR2
    have hg2n' : g.1.2 ∉ R' := (Finset.disjoint_left.mp hRR') hR2
    have hg1'' : g.1.1 ∈ R'' := by
      rcases h.2 with ⟨hc1, _⟩ | ⟨_, hc2⟩
      · exact hc1
      · exact absurd hc2 hg2n''
    have hg1' : g.1.1 ∈ R' := by
      rcases hbad.2 with ⟨hc1, _⟩ | ⟨_, hc2⟩
      · exact hc1
      · exact absurd hc2 hg2n'
    exact (Finset.disjoint_left.mp hR'R'') hg1' hg1''

variable (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)

/-- **Red boundary match, `r-b` super-bond.** If a coarse configuration's induced red
boundary configuration equals a global configuration's red boundary label, the `r-b`
bond model reads `η`'s `r-b` super-bond as the global configuration's red-to-blue
crossing label. -/
theorem bondModel_rb_eq_of_legEquivRed_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζr : VirtualConfig A)
    (h : F.frame.legEquivRed (fun ie => η ie.1) = regionBoundaryLabel (G := G) A F.frame.red ζr) :
    F.bondModel coarseEdgeRB (η coarseEdgeRB) =
        crossingLabel (G := G) A F.frame.red F.frame.blue ζr := by
  funext g
  have hcross : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g.1 := g.2
  have hbdry : IsRegionBoundaryEdge (G := G) F.frame.red g.1 := hcross.1
  have hkey := congrFun h ⟨g.1, hbdry⟩
  rw [F.legEquivRed_apply_eq hP η ⟨g.1, hbdry⟩, dif_pos hcross] at hkey
  simp only [regionBoundaryLabel_apply] at hkey
  rw [crossingLabel]; exact hkey

/-- **Red boundary match, `r-c` super-bond.** -/
theorem bondModel_rc_eq_of_legEquivRed_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζr : VirtualConfig A)
    (h : F.frame.legEquivRed (fun ie => η ie.1) = regionBoundaryLabel (G := G) A F.frame.red ζr) :
    F.bondModel coarseEdgeRC (η coarseEdgeRC) =
        crossingLabel (G := G) A F.frame.red F.frame.complement ζr := by
  funext g
  have hcross : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g.1 := g.2
  have hbdry : IsRegionBoundaryEdge (G := G) F.frame.red g.1 := hcross.1
  -- This edge crosses to the complement, not to blue, so the dichotomy resolves right.
  have hnb : ¬ IsCrossingEdge (G := G) A F.frame.red F.frame.blue g.1 :=
    not_crossing_of_crossing_disjoint (A := A) hP.red_disjoint_blue
      hP.red_disjoint_complement hP.blue_disjoint_complement hcross
  have hkey := congrFun h ⟨g.1, hbdry⟩
  rw [F.legEquivRed_apply_eq hP η ⟨g.1, hbdry⟩, dif_neg hnb] at hkey
  simp only [regionBoundaryLabel_apply] at hkey
  rw [crossingLabel]; exact hkey

/-- **Blue boundary match, `r-b` super-bond.** -/
theorem bondModel_rb_eq_of_legEquivBlue_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζb : VirtualConfig A)
    (h : F.frame.legEquivBlue (fun ie => η ie.1) =
      regionBoundaryLabel (G := G) A F.frame.blue ζb) :
    F.bondModel coarseEdgeRB (η coarseEdgeRB) =
        (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue) := by
  funext g
  have hcross : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g.1 := g.2
  have hbdry : IsRegionBoundaryEdge (G := G) F.frame.blue g.1 := hcross.2
  have hkey := congrFun h ⟨g.1, hbdry⟩
  rw [F.legEquivBlue_apply_eq hP η ⟨g.1, hbdry⟩, dif_pos hcross] at hkey
  simp only [regionBoundaryLabel_apply] at hkey
  exact hkey

/-- **Blue boundary match, `b-c` super-bond.** -/
theorem bondModel_bc_eq_of_legEquivBlue_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζb : VirtualConfig A)
    (h : F.frame.legEquivBlue (fun ie => η ie.1) =
      regionBoundaryLabel (G := G) A F.frame.blue ζb) :
    F.bondModel coarseEdgeBC (η coarseEdgeBC) =
        crossingLabel (G := G) A F.frame.blue F.frame.complement ζb := by
  funext g
  have hcross : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g.1 := g.2
  have hbdry : IsRegionBoundaryEdge (G := G) F.frame.blue g.1 := hcross.1
  have hnb : ¬ IsCrossingEdge (G := G) A F.frame.red F.frame.blue g.1 := fun hbad =>
    not_crossing_of_crossing_disjoint (A := A) hP.red_disjoint_blue.symm
      hP.blue_disjoint_complement hP.red_disjoint_complement hcross hbad.symm
  have hkey := congrFun h ⟨g.1, hbdry⟩
  rw [F.legEquivBlue_apply_eq hP η ⟨g.1, hbdry⟩, dif_neg hnb] at hkey
  simp only [regionBoundaryLabel_apply] at hkey
  rw [crossingLabel]; exact hkey

/-- **Complement boundary match, `r-c` super-bond.** -/
theorem bondModel_rc_eq_of_legEquivComplement_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζc : VirtualConfig A)
    (h : F.frame.legEquivComplement (fun ie => η ie.1) =
      regionBoundaryLabel (G := G) A F.frame.complement ζc) :
    F.bondModel coarseEdgeRC (η coarseEdgeRC) =
        (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.red F.frame.complement) := by
  funext g
  have hcross : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g.1 := g.2
  have hbdry : IsRegionBoundaryEdge (G := G) F.frame.complement g.1 := hcross.2
  have hkey := congrFun h ⟨g.1, hbdry⟩
  rw [F.legEquivComplement_apply_eq hP η ⟨g.1, hbdry⟩, dif_pos hcross] at hkey
  simp only [regionBoundaryLabel_apply] at hkey
  exact hkey

/-- **Complement boundary match, `b-c` super-bond.** -/
theorem bondModel_bc_eq_of_legEquivComplement_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζc : VirtualConfig A)
    (h : F.frame.legEquivComplement (fun ie => η ie.1) =
      regionBoundaryLabel (G := G) A F.frame.complement ζc) :
    F.bondModel coarseEdgeBC (η coarseEdgeBC) =
        (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.blue F.frame.complement) := by
  funext g
  have hcross : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g.1 := g.2
  have hbdry : IsRegionBoundaryEdge (G := G) F.frame.complement g.1 := hcross.2
  have hnr : ¬ IsCrossingEdge (G := G) A F.frame.red F.frame.complement g.1 := fun hbad =>
    not_crossing_of_crossing_disjoint (A := A) hP.red_disjoint_complement.symm
      hP.blue_disjoint_complement.symm hP.red_disjoint_blue hcross.symm hbad.symm
  have hkey := congrFun h ⟨g.1, hbdry⟩
  rw [F.legEquivComplement_apply_eq hP η ⟨g.1, hbdry⟩, dif_neg hnr] at hkey
  simp only [regionBoundaryLabel_apply] at hkey
  exact hkey

end PEPS
end TNLean
