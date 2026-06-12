import TNLean.PEPS.NormalBondDimension
import TNLean.PEPS.NormalComparisonScalar
import TNLean.PEPS.RegionScalarCondition
import TNLean.PEPS.TorusGaugeUniqueness

/-!
# The Fundamental Theorem for normal PEPS on a connected graph

This file assembles the general normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, theorem labelled `normal`, lines 1576--1583 of
`Papers/1804.04964/paper_normal.tex`): two normal PEPS on a connected finite
simple graph generating the same state, blocked into three partite injective
chains around every edge and admitting one-site-different injective regions
with injective complements at every site, have gauge-equivalent defining
tensors; and the gauges are unique up to a multiplicative constant on each
edge.

The route follows the source.  The blocking hypotheses force equal bond
dimensions on every edge (`bondDim_eq_of_normalBlocking`, the isomorphism
rigidity of the source's Lemma `inj_isomorph`, lines 560--583, inherited
through the blocked coarse chains); they produce a per-edge absorbing gauge
family with the bare-edge absorbed equality at every edge
(`exists_normalAbsorbedGaugeFamily`); the one-site comparisons give a nonzero
scalar `λ_v` at every vertex with `A_v = λ_v · (gauge action of B at v)`
(`exists_normalPerVertexScalar`); the closed state pins `∏_v λ_v = 1`
(`prod_perVertexScalar_eq_one_of_regionInjective`); and on the connected graph
the scalars are absorbed into the edge gauges by the oriented-incidence solve
of the injective Fundamental Theorem (`exists_edgeScalars_of_connected`,
`perVertex_gauge_identity`), leaving the scalar-free gauge relation
`GaugeEquiv A B`.  This matches the source remark after the theorem: the
statement holds at fixed system size with no translation invariance, the
proportionality constants being absorbed into the gauges.

The hypotheses beyond the source's wording are documented:

* **Shared blockings (the source's pair reading):** the blocking hypotheses
  are instantiated at the conjunction predicate
  (`regionInjectivityDataPair`): one family of regions, each injective for
  both tensors at once.  This is the source's hypothesis, not an added
  restriction: the theorem blocks both states by one blocking ("*they* can be
  blocked into three partite injective MPS around every edge", lines
  1577--1579 of `Papers/1804.04964/paper_normal.tex`); the proof it
  generalizes chooses the regions once and feeds the two blocked chains, over
  the same tripartition, to the isomorphism lemma, whose statement requires
  all six blocks injective (lines 254--278, applied at lines 1475--1498); and
  the final comparison contracts both tensors over the same
  one-site-different regions, with all four blocked tensors injective by its
  comparison lemma (lines 1067--1093, applied at lines 1519--1544).  See
  `TNLean.PEPS.NormalPairBlocking` and
  `docs/paper-gaps/peps_normal_ft_section3_route.tex`.
* **Single crossing edge (the source's chain blocking):** the hypothesis
  `hsingle` — each distinguished edge is the entire bond between the red and
  blue blocks — is the chain structure carried by the source's "blocked into
  three partite injective MPS around every edge", not an added restriction:
  the source's blocking around an edge takes the edge as the bond between its
  first two parties, and the proof reads the resulting gauge as living on that
  edge (lines 981--1009, 1037, and 1475--1498 of
  `Papers/1804.04964/paper_normal.tex`).  It is stated explicitly because the
  recorded blocking bundle does not carry it as a field (see
  `TNLean.PEPS.NormalAbsorbedFamily` and
  `docs/paper-gaps/peps_normal_ft_section3_route.tex`).
* Positive bond dimensions and connectivity are the faithfulness fixes of the
  injective Fundamental Theorem, both backed by machine-checked
  counterexamples (`docs/paper-gaps/peps_injective_ft_section3_route.tex`,
  `docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`); the scalar
  absorption is exactly the step that requires connectivity.

The source's remark following the theorem (line 1584 of
`Papers/1804.04964/paper_normal.tex`) — for a translationally invariant
system the gauges are also translationally invariant, provided the
proportionality constants are not absorbed into the gauges — is delivered on
the torus, the development's translation-invariant setting:
`exists_torusCovariantAbsorbedGaugeFamily` constructs a translation-covariant
gauge family (`IsTranslationCovariantGaugeFamily`), and the unconditional
torus theorem (`fundamentalTheorem_normalTorusPEPS_unconditional`) keeps the
single scalar `λ` with `λ^{nm} = 1` separate from the gauges, exactly the
source's parenthetical.  The present connected-graph statement takes the
other branch of the remark: the per-vertex constants are absorbed into the
edge gauges.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, theorem labelled `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Existence of the local gauge -/

/-- **Fundamental Theorem for normal PEPS on a connected graph**
(arXiv:1804.04964, Section 3, theorem labelled `normal`).

Two tensors on a connected finite simple graph satisfying the general normal
PEPS blocking hypotheses over the pair predicate — every edge carries a
three-region injective blocking shared by both tensors, and every site admits
one-site-different injective regions with injective complements, also shared —
with each distinguished edge the single red-to-blue crossing of its frame,
the same state, and positive bond dimensions, are gauge equivalent: there are
invertible edge matrices relating the defining tensors with no leftover
scalar.

The bond-dimension equality is not assumed: the blocking hypotheses force it
on every edge (`bondDim_eq_of_normalBlocking`), as in the source, where the
insertion correspondence of Lemma `inj_isomorph` is an algebra isomorphism
between the two full bond matrix algebras, so the bond dimensions agree
(lines 560--583 of `Papers/1804.04964/paper_normal.tex`).

The per-vertex scalars `λ_v` produced by the one-site comparisons satisfy
`∏_v λ_v = 1` by the closed state equality, so on the connected graph they are
absorbed into the edge gauges, as in the source's remark that the
proportionality constants can be incorporated into the gauge transformations.

**Shared blockings (the source's pair reading):** the pair predicate
instantiates one blocking for the two states, each region injective for both
tensors, as in the source, where one choice of regions blocks both networks
and the two comparison lemmas take the blocked chains of both tensors over
the same regions (arXiv:1804.04964, lines 1577--1579, 1475--1498, and
1519--1544 of `Papers/1804.04964/paper_normal.tex`); see
`TNLean.PEPS.NormalPairBlocking` and the module docstring.

**Single crossing edge (the source's chain blocking):** the hypothesis
`hsingle` is the formal content of blocking *around* each edge — the
distinguished edge is the entire bond between the first two parties of the
three-site chain, as the source's blocking construction and the Theorem 3
regions realize it (arXiv:1804.04964, lines 981--1009 and 1475--1498 of
`Papers/1804.04964/paper_normal.tex`); see
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.  Positive bonds and
connectivity are the counterexample-backed faithfulness fixes of the
injective Fundamental Theorem
(`docs/paper-gaps/peps_injective_ft_section3_route.tex`,
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`).

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalPEPS
    (A B : Tensor G d)
    (h : NormalPEPSBlockingHypotheses
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G)
    (hsingle : ∀ e g : Edge G,
      IsCrossingEdge (G := G) A (h.edgeBlocking.red e) (h.edgeBlocking.blue e) g ↔ g = e)
    (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g)
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hconn : G.Connected) :
    GaugeEquiv A B := by
  classical
  -- The blocking hypotheses force equal bond dimensions on every edge.
  have hbond : A.bondDim = B.bondDim :=
    bondDim_eq_of_normalBlocking A B h hsingle hAB hd hposA hposB
  -- The absorbing gauge family with the bare-edge absorbed equality everywhere.
  obtain ⟨Z, hedge⟩ :=
    exists_normalAbsorbedGaugeFamily A B h hsingle hbond hAB hd hposA hposB
  -- The per-vertex scalars from the one-site comparisons.
  have hpvs : ∀ v : V, ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        A.component v η σ =
          lam * gaugeVertex B Z v
            (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ :=
    fun v => exists_normalPerVertexScalar A B h hconn hbond hAB hposA Z hedge v
  choose c hcne hcPV using hpvs
  -- The closed state pins the product of the scalars to one.
  obtain ⟨v₀⟩ := hconn.nonempty
  have hRA0 : RegionBlockedTensorInjective (G := G) A
      (h.oneSiteSeparation.withoutSite v₀) := by
    have hi := (h.oneSiteSeparation.withoutSite_injective v₀).1
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCA0 : RegionBlockedTensorInjective (G := G) A
      (Finset.univ \ h.oneSiteSeparation.withoutSite v₀) := by
    have hi := (h.oneSiteSeparation.withoutSite_complement_injective v₀).1
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hprod : (∏ v, c v) = 1 :=
    prod_perVertexScalar_eq_one_of_regionInjective A B
      (h.oneSiteSeparation.withoutSite v₀) hRA0 hCA0 hposA hAB Z hbond c hcPV
  -- The scalars are absorbed into the gauges on the connected graph.
  set t : V → ℂˣ := fun v => (Units.mk0 (c v) (hcne v))⁻¹ with ht
  have htprod : (∏ v, t v) = 1 := by
    have hmk : (∏ v, (Units.mk0 (c v) (hcne v))) = 1 := by
      apply Units.ext
      rw [Units.val_one, Units.coe_prod]
      simp only [Units.val_mk0]
      exact hprod
    rw [ht]
    simp only
    rw [Finset.prod_inv_distrib, hmk, inv_one]
  obtain ⟨s, hs⟩ := exists_edgeScalars_of_connected hconn t htprod
  refine ⟨hbond, globalGauge A B hbond Z s, ?_⟩
  intro v η σ
  have hcs : ∏ ie : IncidentEdge G v, (edgeScalarUnit (G := G) s v ie : ℂ) = (c v)⁻¹ := by
    have hsv := hs v
    rw [orientedIncidence] at hsv
    have hval : ((∏ ie : IncidentEdge G v, edgeScalarUnit (G := G) s v ie : ℂˣ) : ℂ)
        = (c v)⁻¹ := by
      rw [hsv, ht]
      simp [Units.val_mk0]
    rwa [Units.coe_prod] at hval
  exact perVertex_gauge_identity A B hbond Z s v (c v) (hcne v) hcs
    (fun η σ => hcPV v η σ) η σ

/-! ### Uniqueness of the gauges up to a multiplicative constant

The last clause of the source theorem.  Two gauge families realizing the
scalar-free per-vertex relation each induce the bare-edge absorbed equality at
every edge, and on the single boundary edge of any region at which the first
tensor is region- and complement-injective the absorbing gauges induce the same
conjugation map, hence differ by a nonzero scalar. -/

open scoped Classical in
/-- **Per-edge uniqueness of an absorbing gauge family, from a comparison
region.**

Two gauge families `X`, `X'` both realizing the bare-edge absorbed equality at
the boundary edge `f.1` of a region `R` at which `B` is region- and
complement-injective are proportional at that edge: `X' f.1 = c · X f.1` for a
nonzero scalar `c`.  This is the graph-general form of
`torusAbsorbedGauge_unique_scalar_of_region`: both families induce the
conjugation-form coefficient identity at `R`, `f`
(`regionConjIdentity_of_edgeAbsorbed`), the region-insertion transfer map is
determined by the identity (`gaugeConj_eq_of_coeffIdentities`), so the two
absorbing gauges differ by a scalar (`gl_conj_unique_scalar`), and unwinding
the orientation adaptation gives the proportionality of the gauges themselves.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 (the gauges are unique up to a multiplicative constant), via the
conjugator determinacy of the isomorphism lemma, lines 560--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem absorbedGauge_unique_scalar_of_region
    (A B : Tensor G d) (hbd : A.bondDim = B.bondDim)
    (R : Finset V) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (X X' : (g : Edge G) → GL (Fin (B.bondDim g)) ℂ)
    (hedgeX : ∀ (σ : V → Fin d)
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      edgeInsertedCoeff (G := G) A f.1 σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) f.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N))
    (hedgeX' : ∀ (σ : V → Fin d)
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      edgeInsertedCoeff (G := G) A f.1 σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X') f.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N)) :
    ∃ c : ℂˣ, (X' f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
      (c : ℂ) • (X f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := by
  -- The two absorbing gauges induce the same conjugation map.
  have hconj : ∀ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      (absorbedBoundaryGauge (G := G) B R f (X f.1) :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑(absorbedBoundaryGauge (G := G) B R f (X f.1))⁻¹ :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
      (absorbedBoundaryGauge (G := G) B R f (X' f.1) :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑(absorbedBoundaryGauge (G := G) B R f (X' f.1))⁻¹ :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := by
    intro N
    obtain ⟨M, rfl⟩ :=
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1))).surjective N
    exact gaugeConj_eq_of_coeffIdentities A B R f hRB hCB hposB
      (hE₁ := congr_fun hbd f.1) (hE₂ := congr_fun hbd f.1)
      (absorbedBoundaryGauge (G := G) B R f (X f.1))
      (absorbedBoundaryGauge (G := G) B R f (X' f.1))
      (fun M σ τ => regionConjIdentity_of_edgeAbsorbed A B hbd X R f hedgeX M σ τ)
      (fun M σ τ => regionConjIdentity_of_edgeAbsorbed A B hbd X' R f hedgeX' M σ τ) M
  obtain ⟨c, hc⟩ := gl_conj_unique_scalar
    (absorbedBoundaryGauge (G := G) B R f (X f.1))
    (absorbedBoundaryGauge (G := G) B R f (X' f.1)) hconj
  -- Unwind the orientation adaptation on each branch.
  by_cases hmem : f.1.1.1 ∈ R
  · refine ⟨c, ?_⟩
    have hZ : absorbedBoundaryGauge (G := G) B R f (X f.1) = glTranspose (X f.1) := by
      unfold absorbedBoundaryGauge; rw [if_pos hmem]
    have hZ' : absorbedBoundaryGauge (G := G) B R f (X' f.1) = glTranspose (X' f.1) := by
      unfold absorbedBoundaryGauge; rw [if_pos hmem]
    rw [hZ, hZ', glTranspose_coe, glTranspose_coe] at hc
    have htr := congrArg Matrix.transpose hc
    rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose] at htr
  · refine ⟨c⁻¹, ?_⟩
    have hZ : absorbedBoundaryGauge (G := G) B R f (X f.1) = (X f.1)⁻¹ := by
      unfold absorbedBoundaryGauge; rw [if_neg hmem]
    have hZ' : absorbedBoundaryGauge (G := G) B R f (X' f.1) = (X' f.1)⁻¹ := by
      unfold absorbedBoundaryGauge; rw [if_neg hmem]
    rw [hZ, hZ'] at hc
    have hinv := gl_inv_coe_smul (W := (X f.1)⁻¹) (W' := (X' f.1)⁻¹) hc
    rwa [inv_inv, inv_inv] at hinv

open scoped Classical in
/-- **The bare-edge absorbed equality from a scalar per-vertex relation.**

If `A` satisfies `A_v = λ · (gauge action of B at v)` at every vertex with
`λ^{|V|} = 1`, then the bare-edge absorbed equality holds at every edge.  This
is the graph-general form of the torus `edgeAbsorbed_of_perVertex`: the
edge-inserted coefficient picks up one factor of `λ` per site
(`edgeInsertedCoeff_eq_pow_card_mul_reindexTensor`).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1471 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeAbsorbed_of_perVertex_card
    (A B : Tensor G d) (hbond : A.bondDim = B.bondDim)
    (X : (g : Edge G) → GL (Fin (B.bondDim g)) ℂ) {lam : ℂ}
    (hPV : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ)
    (hlam : lam ^ (Fintype.card V) = 1)
    (e : Edge G) (σ : V → Fin d)
    (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) A e σ N =
      edgeInsertedCoeff (G := G) (applyGauge B X) e σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  have hscale := edgeInsertedCoeff_eq_pow_card_mul_reindexTensor A (applyGauge B X) hbond lam
    hPV e σ N
  rw [hscale, edgeInsertedCoeff_reindexTensor (applyGauge B X) hbond e σ N, hlam, one_mul]
  rfl

open scoped Classical in
/-- **Uniqueness clause of the Fundamental Theorem for normal PEPS**
(arXiv:1804.04964, Section 3, theorem labelled `normal`: the gauges are unique
up to a multiplicative constant).

Two gauge families `X`, `X'` each realizing the scalar-free gauge relation of
`fundamentalTheorem_normalPEPS` — `B_v = (gauge action of A at v)` at every
vertex — are proportional at every edge: `X' e = c · X e` for a nonzero
scalar `c`.  Each relation yields the bare-edge absorbed equality with the
roles of the two tensors exchanged (`edgeAbsorbed_of_perVertex_card` with
scalar `1`), and the equalities determine the gauge at `e` up to a scalar on
the red block of `e`'s frame (`absorbedGauge_unique_scalar_of_region`), whose
block and host injectivity for the first tensor come from the blocking
hypotheses and union closure.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalPEPS_gauge_unique
    (A B : Tensor G d)
    (h : NormalPEPSBlockingHypotheses
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G)
    (hbond : A.bondDim = B.bondDim)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g)
    (X X' : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (hX : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ =
        gaugeVertex A X v η σ)
    (hX' : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ =
        gaugeVertex A X' v η σ)
    (e : Edge G) :
    ∃ c : ℂˣ, (X' e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
      (c : ℂ) • (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
  classical
  -- The scalar-free relation in the exchanged-roles per-vertex form.
  have hswap : ∀ (Y : (g : Edge G) → GL (Fin (A.bondDim g)) ℂ),
      (∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ =
          gaugeVertex A Y v η σ) →
      ∀ (v : V) (ζ : (ie : IncidentEdge G v) → Fin (B.bondDim ie.1)) (σp : Fin d),
        B.component v ζ σp =
          (1 : ℂ) * gaugeVertex A Y v
            (fun ie => Fin.cast (congr_fun hbond.symm ie.1) (ζ ie)) σp := by
    intro Y hY v ζ σp
    rw [one_mul]
    have hζ : (fun ie : IncidentEdge G v => Fin.cast (congr_fun hbond ie.1)
        (Fin.cast (congr_fun hbond.symm ie.1) (ζ ie))) = ζ := by
      funext ie
      exact Fin.ext (by simp)
    have hcomp := hY v (fun ie => Fin.cast (congr_fun hbond.symm ie.1) (ζ ie)) σp
    rwa [hζ] at hcomp
  -- The exchanged-roles bare-edge absorbed equality at `e` for both families.
  have hone : (1 : ℂ) ^ (Fintype.card V) = 1 := one_pow _
  have hedgeX := fun (σ : V → Fin d)
      (N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =>
    edgeAbsorbed_of_perVertex_card B A hbond.symm X (hswap X hX) hone e σ N
  have hedgeX' := fun (σ : V → Fin d)
      (N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =>
    edgeAbsorbed_of_perVertex_card B A hbond.symm X' (hswap X' hX') hone e σ N
  -- The comparison region: the red block of `e`'s frame, injective for `A`.
  have hUA : RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G) A) :=
    regionInjectivityUnionClosure_of_overlap A hposA
  set D := h.edgeBlocking.blockingData e with hD
  have hRA : RegionBlockedTensorInjective (G := G) A D.pairLeft.red :=
    regionBlockedTensorInjective_red D.pairLeft
  have hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.pairLeft.red) :=
    regionBlockedTensorInjective_host D.pairLeft hUA
  have hbdry : IsRegionBoundaryEdge (G := G) D.pairLeft.red e :=
    Or.inl ⟨D.left_mem_red,
      Finset.disjoint_right.mp D.red_disjoint_blue D.right_mem_blue⟩
  exact absorbedGauge_unique_scalar_of_region B A hbond.symm D.pairLeft.red
    ⟨e, hbdry⟩ hRA hCA hposA X X' hedgeX hedgeX'

end PEPS
end TNLean
