import TNLean.PEPS.RegionBlock.CoarseThreeSite5

/-!
# The inserted-coefficient descent for the normal PEPS theorem

The fiber-collapse `TNLean.PEPS.stateCoeff_coarseTensor_collapse` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite5` glues the coarse three-site closed state to
the original closed state: the coarse state coefficient is a constant times the
original state coefficient of the assembled physical configuration. This file mirrors
that collapse with a matrix inserted on the coarse `r-b` super-bond, descending the
coarse edge-inserted coefficient to the original region-inserted coefficient of the
red region against its set complement.

The coarse `r-b` super-bond is the whole bundle of red-to-blue crossing edges
(`CrossingConfig red blue`, the codomain of `bondModel coarseEdgeRB`), so a matrix on
that super-bond couples every red-to-blue crossing, not a single boundary edge. The
descent therefore lands on the whole-crossing-bundle inserted coefficient
`crossingInsertedCoeff`, the analogue of `regionInsertedCoeff` whose inserted matrix
acts on the whole red-to-blue crossing bundle rather than a single boundary edge.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 (the injective three-site comparison) and 1205--1210,
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The red-to-blue crossing-bundle agreement

The fiber-collapse `agreeingTripleSum_collapse` sums the product of the three regions'
vertex products over crossing triples that agree on *all three* super-bonds. With a
matrix inserted on the `r-b` super-bond the red and blue configurations are no longer
forced to agree on the red-to-blue crossings: their two crossing labels there are
coupled through the inserted matrix instead. The remaining two agreements, on the
red-to-complement and blue-to-complement crossings, are unchanged.

This predicate records that relaxed agreement: the red and complement configurations
agree on the red-to-complement crossings, and the blue and complement configurations
agree on the blue-to-complement crossings, with the red-to-blue crossings left free. -/

/-- **Relaxed crossing agreement of a triple.** The red and complement configurations
agree on the red-to-complement crossings, and the blue and complement configurations
agree on the blue-to-complement crossings; the red-to-blue crossings are left free for
the inserted matrix to couple. -/
def CrossTripleAgreesAwayRB (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb ζc : VirtualConfig A) : Prop :=
  crossingLabel (G := G) A F.frame.red F.frame.complement ζr =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.red F.frame.complement) ∧
    crossingLabel (G := G) A F.frame.blue F.frame.complement ζb =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.blue F.frame.complement)

instance (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (ζr ζb ζc : VirtualConfig A) :
    Decidable (CrossTripleAgreesAwayRB F ζr ζb ζc) := by
  unfold CrossTripleAgreesAwayRB; infer_instance

/-- A fully agreeing triple agrees away from the `r-b` super-bond. -/
theorem CrossTripleAgreesAwayRB.of_tripleAgrees
    {F : CoherentCoarseBlockingFrame (G := G) (d := d) A} {ζr ζb ζc : VirtualConfig A}
    (h : TripleAgrees F ζr ζb ζc) : CrossTripleAgreesAwayRB F ζr ζb ζc :=
  ⟨h.2.1, h.2.2⟩

/-! ### The red-to-blue crossing label of a region boundary configuration

The red region's boundary edges split, under the partition, into red-to-blue crossings
and red-to-complement crossings. A red boundary configuration therefore restricts to a
red-to-blue crossing configuration: its values on the boundary edges that cross to the
blue region. The inserted matrix on the `r-b` super-bond couples two red (and host)
boundary configurations only through these red-to-blue crossing values. -/

/-- The red-to-blue crossing label of a red boundary configuration: its values on the
boundary edges of the red region that cross to the blue region. -/
noncomputable def redBoundaryRBCrossing (A : Tensor G d) (red blue : Finset V)
    (μ : RegionBoundaryConfig (G := G) A red) :
    CrossingConfig (G := G) A red blue :=
  fun g => μ ⟨g.1, g.2.1⟩

omit [Fintype V] in
@[simp] theorem redBoundaryRBCrossing_apply (A : Tensor G d) (red blue : Finset V)
    (μ : RegionBoundaryConfig (G := G) A red)
    (g : {g : Edge G // IsCrossingEdge (G := G) A red blue g}) :
    redBoundaryRBCrossing (G := G) A red blue μ g = μ ⟨g.1, g.2.1⟩ := rfl

/-! ### The whole-bundle red inserted coefficient

The descent target of the coarse edge-inserted coefficient. The coarse `r-b`
super-bond carries the whole red-to-blue crossing bundle, so the inserted matrix
couples two red (and host) boundary configurations through their red-to-blue crossing
labels, with the remaining boundary edges (the red-to-complement crossings) contracted
diagonally. This is the whole-bundle analogue of `regionInsertedCoeff`, where the
single boundary edge of the coupling is replaced by the whole red-to-blue crossing
bundle.

Two boundary configurations agree away from the red-to-blue crossings when they carry
the same value on every red boundary edge that does not cross to the blue region. -/

/-- Two red boundary configurations agree away from the red-to-blue crossings: they
carry the same value on every red boundary edge not crossing to the blue region. -/
def SameAwayFromRBBundle (A : Tensor G d) (red blue : Finset V)
    (μ ν : RegionBoundaryConfig (G := G) A red) : Prop :=
  ∀ f : {f : Edge G // IsRegionBoundaryEdge (G := G) red f},
    ¬ IsCrossingEdge (G := G) A red blue f.1 → μ f = ν f

instance (A : Tensor G d) (red blue : Finset V)
    (μ ν : RegionBoundaryConfig (G := G) A red) :
    Decidable (SameAwayFromRBBundle (G := G) A red blue μ ν) := by
  unfold SameAwayFromRBBundle; infer_instance

/-- **The whole-bundle red inserted coefficient.** Insert the matrix `M` on the whole
red-to-blue crossing bundle of the red region's boundary, contract the red region on
one side and the host `univ \ red` on the other, with the red-to-complement crossings
contracted diagonally. This is the descent target of the coarse edge-inserted
coefficient at the coarse `r-b` super-bond.

The sum has two red boundary configurations `μ` (read by the red region) and `ν` (read
by the host), agreeing away from the red-to-blue crossings; `M` couples their
red-to-blue crossing labels.

Source: arXiv:1804.04964, Section 3, lines 254--583 and 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def redBundleInsertedCoeff (A : Tensor G d) (red blue : Finset V)
    (M : Matrix (CrossingConfig (G := G) A red blue)
      (CrossingConfig (G := G) A red blue) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ red)) : ℂ :=
    ∑ μ : RegionBoundaryConfig (G := G) A red,
      ∑ ν : RegionBoundaryConfig (G := G) A red,
        (if SameAwayFromRBBundle (G := G) A red blue μ ν then
            M (redBoundaryRBCrossing (G := G) A red blue μ)
              (redBoundaryRBCrossing (G := G) A red blue ν)
          else 0) *
          regionBlockedWeight (G := G) A red μ σ *
          regionBlockedWeight (G := G) A (Finset.univ \ red)
            (regionComplementBoundaryConfig (G := G) A red ν) τ

/-- Unfolding lemma for `redBundleInsertedCoeff`. -/
theorem redBundleInsertedCoeff_eq (A : Tensor G d) (red blue : Finset V)
    (M : Matrix (CrossingConfig (G := G) A red blue)
      (CrossingConfig (G := G) A red blue) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ red)) :
    redBundleInsertedCoeff (G := G) A red blue M σ τ =
      ∑ μ : RegionBoundaryConfig (G := G) A red,
        ∑ ν : RegionBoundaryConfig (G := G) A red,
          (if SameAwayFromRBBundle (G := G) A red blue μ ν then
              M (redBoundaryRBCrossing (G := G) A red blue μ)
                (redBoundaryRBCrossing (G := G) A red blue ν)
            else 0) *
            regionBlockedWeight (G := G) A red μ σ *
            regionBlockedWeight (G := G) A (Finset.univ \ red)
              (regionComplementBoundaryConfig (G := G) A red ν) τ := by
  rw [redBundleInsertedCoeff]

/-- The whole-bundle red inserted coefficient is additive in the inserted matrix. -/
theorem redBundleInsertedCoeff_add (A : Tensor G d) (red blue : Finset V)
    (M M' : Matrix (CrossingConfig (G := G) A red blue)
      (CrossingConfig (G := G) A red blue) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ red)) :
    redBundleInsertedCoeff (G := G) A red blue (M + M') σ τ =
      redBundleInsertedCoeff (G := G) A red blue M σ τ +
        redBundleInsertedCoeff (G := G) A red blue M' σ τ := by
  classical
  rw [redBundleInsertedCoeff_eq, redBundleInsertedCoeff_eq, redBundleInsertedCoeff_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  by_cases h : SameAwayFromRBBundle (G := G) A red blue μ ν
  · simp only [if_pos h, Matrix.add_apply]; ring
  · simp only [if_neg h]; ring

/-- The whole-bundle red inserted coefficient is homogeneous in the inserted matrix. -/
theorem redBundleInsertedCoeff_smul (A : Tensor G d) (red blue : Finset V) (c : ℂ)
    (M : Matrix (CrossingConfig (G := G) A red blue)
      (CrossingConfig (G := G) A red blue) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ red)) :
    redBundleInsertedCoeff (G := G) A red blue (c • M) σ τ =
      c * redBundleInsertedCoeff (G := G) A red blue M σ τ := by
  classical
  rw [redBundleInsertedCoeff_eq, redBundleInsertedCoeff_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  by_cases h : SameAwayFromRBBundle (G := G) A red blue μ ν
  · simp only [if_pos h, Matrix.smul_apply, smul_eq_mul]; ring
  · simp only [if_neg h]; ring

end PEPS
end TNLean
