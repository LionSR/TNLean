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

/-! ### Recovering the region boundary configs from the bond models

The converse of the boundary matches: a coarse configuration whose two incident bond
models read a global configuration's crossing labels induces exactly that global
configuration's region boundary label. This is the existence half of the inner
super-bond count: a pairwise-agreeing triple of global configurations is realised by
a coarse configuration. -/

/-- **Red boundary recovery.** If the `r-b` and `r-c` bond models of `η` read `ζr`'s
red-to-blue and red-to-complement crossing labels, the red boundary configuration
induced by `η` is `ζr`'s red boundary label. -/
theorem legEquivRed_eq_of_bondModel (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζr : VirtualConfig A)
    (hrb : F.bondModel coarseEdgeRB (η coarseEdgeRB) =
      crossingLabel (G := G) A F.frame.red F.frame.blue ζr)
    (hrc : F.bondModel coarseEdgeRC (η coarseEdgeRC) =
      crossingLabel (G := G) A F.frame.red F.frame.complement ζr) :
    F.frame.legEquivRed (fun ie => η ie.1) = regionBoundaryLabel (G := G) A F.frame.red ζr := by
  funext b
  rw [F.legEquivRed_apply_eq hP η b]
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dif_pos hb]
    have := congrFun hrb ⟨b.1, hb⟩
    rw [crossingLabel_apply] at this; rw [this]; rfl
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_red_complement hP b.2).resolve_left hb
    have := congrFun hrc ⟨b.1, hc⟩
    rw [crossingLabel_apply] at this; rw [this]; rfl

/-- **Blue boundary recovery.** -/
theorem legEquivBlue_eq_of_bondModel (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζb : VirtualConfig A)
    (hrb : F.bondModel coarseEdgeRB (η coarseEdgeRB) =
      (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue))
    (hbc : F.bondModel coarseEdgeBC (η coarseEdgeBC) =
      crossingLabel (G := G) A F.frame.blue F.frame.complement ζb) :
    F.frame.legEquivBlue (fun ie => η ie.1) =
      regionBoundaryLabel (G := G) A F.frame.blue ζb := by
  funext b
  rw [F.legEquivBlue_apply_eq hP η b]
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dif_pos hb]
    have := congrFun hrb ⟨b.1, hb⟩; rw [this]; rfl
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb
    have := congrFun hbc ⟨b.1, hc⟩
    rw [crossingLabel_apply] at this; rw [this]; rfl

/-- **Complement boundary recovery.** -/
theorem legEquivComplement_eq_of_bondModel (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor)) (ζc : VirtualConfig A)
    (hrc : F.bondModel coarseEdgeRC (η coarseEdgeRC) =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.red F.frame.complement))
    (hbc : F.bondModel coarseEdgeBC (η coarseEdgeBC) =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.blue F.frame.complement)) :
    F.frame.legEquivComplement (fun ie => η ie.1) =
      regionBoundaryLabel (G := G) A F.frame.complement ζc := by
  funext b
  rw [F.legEquivComplement_apply_eq hP η b]
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1
  · rw [dif_pos hb]
    have := congrFun hrc ⟨b.1, hb⟩; rw [this]; rfl
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_complement_or_blue_complement hP b.2).resolve_left hb
    have := congrFun hbc ⟨b.1, hc⟩
    rw [this]; rfl

/-! ### The crossing-triple agreement and its realising coarse configuration

A triple of global virtual configurations agrees on the crossing edges when its
three pairwise crossing labels coincide. Such a triple is realised by exactly one
coarse virtual configuration, recovered through the bond models. This is the
combinatorial heart of the reindexing: the super-bond count of the boundary-coupled
triple sum is the indicator of crossing agreement. -/

/-- **Crossing agreement of a triple.** Three global virtual configurations agree on
the crossing edges when the red and blue agree on the red-to-blue crossings, the red
and complement on the red-to-complement crossings, and the blue and complement on the
blue-to-complement crossings. -/
def TripleAgrees (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb ζc : VirtualConfig A) : Prop :=
  crossingLabel (G := G) A F.frame.red F.frame.blue ζr =
      (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue) ∧
    crossingLabel (G := G) A F.frame.red F.frame.complement ζr =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.red F.frame.complement) ∧
    crossingLabel (G := G) A F.frame.blue F.frame.complement ζb =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.blue F.frame.complement)

instance (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (ζr ζb ζc : VirtualConfig A) :
    Decidable (TripleAgrees F ζr ζb ζc) := by unfold TripleAgrees; infer_instance

/-- **The realising coarse configuration.** The coarse virtual configuration whose
three super-bonds the bond models read as the three crossing labels of an agreeing
triple. -/
noncomputable def tripleToEta (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb : VirtualConfig A) : VirtualConfig (F.frame.coarseTensor) :=
  (crossingTripleEquiv F).symm
    (crossingLabel (G := G) A F.frame.red F.frame.blue ζr,
     crossingLabel (G := G) A F.frame.red F.frame.complement ζr,
     crossingLabel (G := G) A F.frame.blue F.frame.complement ζb)

theorem tripleToEta_rb (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb : VirtualConfig A) :
    F.bondModel coarseEdgeRB ((tripleToEta F ζr ζb) coarseEdgeRB) =
      crossingLabel (G := G) A F.frame.red F.frame.blue ζr := by
  unfold tripleToEta
  have := (crossingTripleEquiv F).apply_symm_apply
    (crossingLabel (G := G) A F.frame.red F.frame.blue ζr,
     crossingLabel (G := G) A F.frame.red F.frame.complement ζr,
     crossingLabel (G := G) A F.frame.blue F.frame.complement ζb)
  rw [crossingTripleEquiv_apply] at this
  exact congrArg (·.1) this

theorem tripleToEta_rc (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb : VirtualConfig A) :
    F.bondModel coarseEdgeRC ((tripleToEta F ζr ζb) coarseEdgeRC) =
      crossingLabel (G := G) A F.frame.red F.frame.complement ζr := by
  unfold tripleToEta
  have := (crossingTripleEquiv F).apply_symm_apply
    (crossingLabel (G := G) A F.frame.red F.frame.blue ζr,
     crossingLabel (G := G) A F.frame.red F.frame.complement ζr,
     crossingLabel (G := G) A F.frame.blue F.frame.complement ζb)
  rw [crossingTripleEquiv_apply] at this
  exact congrArg (·.2.1) this

theorem tripleToEta_bc (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb : VirtualConfig A) :
    F.bondModel coarseEdgeBC ((tripleToEta F ζr ζb) coarseEdgeBC) =
      crossingLabel (G := G) A F.frame.blue F.frame.complement ζb := by
  unfold tripleToEta
  have := (crossingTripleEquiv F).apply_symm_apply
    (crossingLabel (G := G) A F.frame.red F.frame.blue ζr,
     crossingLabel (G := G) A F.frame.red F.frame.complement ζr,
     crossingLabel (G := G) A F.frame.blue F.frame.complement ζb)
  rw [crossingTripleEquiv_apply] at this
  exact congrArg (·.2.2) this

/-- **The super-bond constraint set.** For a fixed triple `(ζr, ζb, ζc)`, the coarse
virtual configurations whose three induced region boundary configurations equal the
triple's region boundary labels: the singleton of the realising coarse configuration
when the triple agrees on the crossings, and empty otherwise. This is the indicator
content of the super-bond count. -/
theorem coarseConfig_constraint_set (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (ζr ζb ζc : VirtualConfig A) :
    (Finset.univ.filter (fun η : VirtualConfig (F.frame.coarseTensor) =>
        F.frame.legEquivRed (fun ie => η ie.1) =
            regionBoundaryLabel (G := G) A F.frame.red ζr ∧
          F.frame.legEquivBlue (fun ie => η ie.1) =
            regionBoundaryLabel (G := G) A F.frame.blue ζb ∧
          F.frame.legEquivComplement (fun ie => η ie.1) =
            regionBoundaryLabel (G := G) A F.frame.complement ζc)) =
      if TripleAgrees F ζr ζb ζc then {tripleToEta F ζr ζb} else ∅ := by
  by_cases hag : TripleAgrees F ζr ζb ζc
  · rw [if_pos hag]
    obtain ⟨hab, hac, hbc⟩ := hag
    ext η
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hb, hc⟩
      apply coarse_virtualConfig_ext F.frame
      · apply (F.bondModel coarseEdgeRB).injective
        rw [bondModel_rb_eq_of_legEquivRed_eq F hP η ζr hr, tripleToEta_rb]
      · apply (F.bondModel coarseEdgeRC).injective
        rw [bondModel_rc_eq_of_legEquivRed_eq F hP η ζr hr, tripleToEta_rc]
      · apply (F.bondModel coarseEdgeBC).injective
        rw [bondModel_bc_eq_of_legEquivBlue_eq F hP η ζb hb, tripleToEta_bc]
    · rintro rfl
      refine ⟨?_, ?_, ?_⟩
      · exact legEquivRed_eq_of_bondModel F hP _ ζr (tripleToEta_rb F ζr ζb)
          (tripleToEta_rc F ζr ζb)
      · refine legEquivBlue_eq_of_bondModel F hP _ ζb ?_ (tripleToEta_bc F ζr ζb)
        rw [tripleToEta_rb]; exact hab
      · refine legEquivComplement_eq_of_bondModel F hP _ ζc ?_ ?_
        · rw [tripleToEta_rc]; exact hac
        · rw [tripleToEta_bc]; exact hbc
  · rw [if_neg hag]
    ext η
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hr, hb, hc⟩
    apply hag
    refine ⟨?_, ?_, ?_⟩
    · rw [← bondModel_rb_eq_of_legEquivRed_eq F hP η ζr hr,
        bondModel_rb_eq_of_legEquivBlue_eq F hP η ζb hb]
    · rw [← bondModel_rc_eq_of_legEquivRed_eq F hP η ζr hr,
        bondModel_rc_eq_of_legEquivComplement_eq F hP η ζc hc]
    · rw [← bondModel_bc_eq_of_legEquivBlue_eq F hP η ζb hb,
        bondModel_bc_eq_of_legEquivComplement_eq F hP η ζc hc]

/-! ### The crossing-triple reindexing of the coarse state sum

The triple sum over coarse virtual configurations of the boundary-coupled product of
the three region weights equals the sum, over triples of global virtual
configurations agreeing on the crossing edges, of the product of the three regions'
vertex products. The coarse super-bond sum collapses to the crossing-agreement
indicator (`coarseConfig_constraint_set`), reindexing the coarse state sum onto the
original crossing data the merge collapse contracts. -/

/-- A product of three scalar selectors is the selector of their conjunction. -/
theorem mul_three_ite {α : Type*} [MulZeroClass α] (P Q R : Prop)
    [Decidable P] [Decidable Q] [Decidable R] (a b c : α) :
    (if P then a else 0) * (if Q then b else 0) * (if R then c else 0) =
      if P ∧ Q ∧ R then a * b * c else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- The boundary-coupled product of the three region weights at a fixed coarse
configuration `η`, expanded as a triple sum over global configurations with the three
region boundary labels matched to `η`'s induced boundary configurations. -/
theorem perEta_threeRegionProduct_eq (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (s : Fin 3 → Fin (coarseDim V d)) (η : VirtualConfig (F.frame.coarseTensor)) :
    regionBlockedWeight (G := G) A F.frame.red
          (F.frame.legEquivRed (fun ie => η ie.1)) (coarseProj F.frame.red (s 0)) *
        regionBlockedWeight (G := G) A F.frame.blue
          (F.frame.legEquivBlue (fun ie => η ie.1)) (coarseProj F.frame.blue (s 1)) *
        regionBlockedWeight (G := G) A F.frame.complement
          (F.frame.legEquivComplement (fun ie => η ie.1)) (coarseProj F.frame.complement (s 2)) =
      ∑ ζr : VirtualConfig A, ∑ ζb : VirtualConfig A, ∑ ζc : VirtualConfig A,
        (if F.frame.legEquivRed (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.red ζr ∧
            F.frame.legEquivBlue (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.blue ζb ∧
            F.frame.legEquivComplement (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.complement ζc then
          (∏ w : {w : V // w ∈ F.frame.red},
              A.component w.1 (fun ie => ζr ie.1) (coarseProj F.frame.red (s 0) w)) *
            (∏ w : {w : V // w ∈ F.frame.blue},
              A.component w.1 (fun ie => ζb ie.1) (coarseProj F.frame.blue (s 1) w)) *
            (∏ w : {w : V // w ∈ F.frame.complement},
              A.component w.1 (fun ie => ζc ie.1) (coarseProj F.frame.complement (s 2) w))
        else 0) := by
  classical
  rw [show regionBlockedWeight (G := G) A F.frame.red
        (F.frame.legEquivRed (fun ie => η ie.1)) (coarseProj F.frame.red (s 0)) =
      ∑ ζr : VirtualConfig A, if regionBoundaryLabel (G := G) A F.frame.red ζr =
          F.frame.legEquivRed (fun ie => η ie.1) then
        ∏ w : {w : V // w ∈ F.frame.red},
          A.component w.1 (fun ie => ζr ie.1) (coarseProj F.frame.red (s 0) w) else 0 from by
      rw [regionBlockedWeight, Finset.sum_filter],
    show regionBlockedWeight (G := G) A F.frame.blue
        (F.frame.legEquivBlue (fun ie => η ie.1)) (coarseProj F.frame.blue (s 1)) =
      ∑ ζb : VirtualConfig A, if regionBoundaryLabel (G := G) A F.frame.blue ζb =
          F.frame.legEquivBlue (fun ie => η ie.1) then
        ∏ w : {w : V // w ∈ F.frame.blue},
          A.component w.1 (fun ie => ζb ie.1) (coarseProj F.frame.blue (s 1) w) else 0 from by
      rw [regionBlockedWeight, Finset.sum_filter],
    show regionBlockedWeight (G := G) A F.frame.complement
        (F.frame.legEquivComplement (fun ie => η ie.1)) (coarseProj F.frame.complement (s 2)) =
      ∑ ζc : VirtualConfig A, if regionBoundaryLabel (G := G) A F.frame.complement ζc =
          F.frame.legEquivComplement (fun ie => η ie.1) then
        ∏ w : {w : V // w ∈ F.frame.complement},
          A.component w.1 (fun ie => ζc ie.1) (coarseProj F.frame.complement (s 2) w)
          else 0 from by
      rw [regionBlockedWeight, Finset.sum_filter]]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ζr _ => ?_)
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ζb _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ζc _ => ?_)
  rw [← mul_assoc, mul_three_ite]
  refine if_congr ?_ rfl rfl
  rw [eq_comm (a := F.frame.legEquivRed fun ie => η ↑ie),
    eq_comm (a := F.frame.legEquivBlue fun ie => η ↑ie),
    eq_comm (a := F.frame.legEquivComplement fun ie => η ↑ie)]

/-- **The crossing-triple reindexing of the coarse state sum.** The triple sum over
coarse virtual configurations of the boundary-coupled product of the three region
weights equals the sum, over triples of global virtual configurations agreeing on the
crossing edges, of the product of the three regions' vertex products.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1205--1210 and
1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeRegionSum_eq_agreeingTripleSum
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (s : Fin 3 → Fin (coarseDim V d)) :
    (∑ η : VirtualConfig (F.frame.coarseTensor),
        regionBlockedWeight (G := G) A F.frame.red
            (F.frame.legEquivRed (fun ie => η ie.1)) (coarseProj F.frame.red (s 0)) *
          regionBlockedWeight (G := G) A F.frame.blue
            (F.frame.legEquivBlue (fun ie => η ie.1)) (coarseProj F.frame.blue (s 1)) *
          regionBlockedWeight (G := G) A F.frame.complement
            (F.frame.legEquivComplement (fun ie => η ie.1))
              (coarseProj F.frame.complement (s 2))) =
      ∑ t ∈ (Finset.univ : Finset (VirtualConfig A × VirtualConfig A × VirtualConfig A)).filter
          (fun t => TripleAgrees F t.1 t.2.1 t.2.2),
        (∏ w : {w : V // w ∈ F.frame.red},
            A.component w.1 (fun ie => t.1 ie.1) (coarseProj F.frame.red (s 0) w)) *
          (∏ w : {w : V // w ∈ F.frame.blue},
            A.component w.1 (fun ie => t.2.1 ie.1) (coarseProj F.frame.blue (s 1) w)) *
          (∏ w : {w : V // w ∈ F.frame.complement},
            A.component w.1 (fun ie => t.2.2 ie.1) (coarseProj F.frame.complement (s 2) w)) := by
  classical
  -- Expand each summand into the triple sum.
  simp_rw [perEta_threeRegionProduct_eq F s]
  -- Exchange to bring the coarse configuration sum innermost.
  have hswap : (∑ η : VirtualConfig (F.frame.coarseTensor), ∑ ζr : VirtualConfig A,
        ∑ ζb : VirtualConfig A, ∑ ζc : VirtualConfig A,
        (if F.frame.legEquivRed (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.red ζr ∧
            F.frame.legEquivBlue (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.blue ζb ∧
            F.frame.legEquivComplement (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.complement ζc then
          (∏ w : {w : V // w ∈ F.frame.red},
              A.component w.1 (fun ie => ζr ie.1) (coarseProj F.frame.red (s 0) w)) *
            (∏ w : {w : V // w ∈ F.frame.blue},
              A.component w.1 (fun ie => ζb ie.1) (coarseProj F.frame.blue (s 1) w)) *
            (∏ w : {w : V // w ∈ F.frame.complement},
              A.component w.1 (fun ie => ζc ie.1) (coarseProj F.frame.complement (s 2) w))
        else 0)) =
      ∑ ζr : VirtualConfig A, ∑ ζb : VirtualConfig A, ∑ ζc : VirtualConfig A,
        ∑ η : VirtualConfig (F.frame.coarseTensor),
        (if F.frame.legEquivRed (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.red ζr ∧
            F.frame.legEquivBlue (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.blue ζb ∧
            F.frame.legEquivComplement (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.complement ζc then
          (∏ w : {w : V // w ∈ F.frame.red},
              A.component w.1 (fun ie => ζr ie.1) (coarseProj F.frame.red (s 0) w)) *
            (∏ w : {w : V // w ∈ F.frame.blue},
              A.component w.1 (fun ie => ζb ie.1) (coarseProj F.frame.blue (s 1) w)) *
            (∏ w : {w : V // w ∈ F.frame.complement},
              A.component w.1 (fun ie => ζc ie.1) (coarseProj F.frame.complement (s 2) w))
        else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ζr _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ζb _ => ?_)
    rw [Finset.sum_comm]
  rw [hswap]
  -- Collapse the innermost coarse sum to the crossing-agreement selector, triple by triple.
  have hcollapse : ∀ ζr ζb ζc : VirtualConfig A,
      (∑ η : VirtualConfig (F.frame.coarseTensor),
        (if F.frame.legEquivRed (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.red ζr ∧
            F.frame.legEquivBlue (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.blue ζb ∧
            F.frame.legEquivComplement (fun ie => η ie.1) =
              regionBoundaryLabel (G := G) A F.frame.complement ζc then
          (∏ w : {w : V // w ∈ F.frame.red},
              A.component w.1 (fun ie => ζr ie.1) (coarseProj F.frame.red (s 0) w)) *
            (∏ w : {w : V // w ∈ F.frame.blue},
              A.component w.1 (fun ie => ζb ie.1) (coarseProj F.frame.blue (s 1) w)) *
            (∏ w : {w : V // w ∈ F.frame.complement},
              A.component w.1 (fun ie => ζc ie.1) (coarseProj F.frame.complement (s 2) w))
        else 0)) =
      if TripleAgrees F ζr ζb ζc then
        (∏ w : {w : V // w ∈ F.frame.red},
            A.component w.1 (fun ie => ζr ie.1) (coarseProj F.frame.red (s 0) w)) *
          (∏ w : {w : V // w ∈ F.frame.blue},
            A.component w.1 (fun ie => ζb ie.1) (coarseProj F.frame.blue (s 1) w)) *
          (∏ w : {w : V // w ∈ F.frame.complement},
            A.component w.1 (fun ie => ζc ie.1) (coarseProj F.frame.complement (s 2) w))
      else 0 := by
    intro ζr ζb ζc
    rw [← Finset.sum_filter, coarseConfig_constraint_set F hP ζr ζb ζc]
    by_cases hag : TripleAgrees F ζr ζb ζc
    · rw [if_pos hag, if_pos hag, Finset.sum_singleton]
    · rw [if_neg hag, if_neg hag, Finset.sum_empty]
  simp_rw [hcollapse]
  -- Reassemble the three sums as a selector sum over triples, then drop the selector.
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun ζr _ => ?_)
  rw [Fintype.sum_prod_type]

end PEPS
end TNLean
