import TNLean.PEPS.RegionBlock.UnionInjectivityGeneralBlue

/-!
# The general union-of-injective-regions lemma: the two-step inverse application

This file completes `TNLean.PEPS.RegionBlock.UnionInjectivityGeneral`: from the blue
and complement fiber-collapse factorizations over a bare `ThreeBlockGeometry`, it
re-derives the source's two-step inverse application of Lemma `injective_union`
(arXiv:1804.04964, Section 3, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`) and specializes it to the disjoint two-region
union lemma `regionBlockedTensorInjective_union_disjoint`, the source-faithful
statement assuming injectivity of the two unioned regions only.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}
variable (g : ThreeBlockGeometry V)

/-! ### The two-step inverse application: the general union theorem

The source's `injective_union`, re-derived over the bare geometry. -/

/-- A boundary edge of the host `univ \ red` whose host-side endpoint lies in the blue
block is a boundary edge of the blue block: the host-side endpoint is in blue, and the
red-side endpoint lies outside blue (the blocks are disjoint). -/
theorem ThreeBlockGeometry.isBlueBoundaryEdge_of_hostBoundary_blue
    {f : Edge G} (hf : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) f)
    (hb : (f.1.1 ∈ Finset.univ \ g.red ∧ f.1.1 ∈ g.blue) ∨
      (f.1.2 ∈ Finset.univ \ g.red ∧ f.1.2 ∈ g.blue)) :
    IsRegionBoundaryEdge (G := G) g.blue f := by
  rcases hf with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
  · -- `f.1.1 ∈ univ \ red`, `f.1.2 ∈ red`.
    have h2red : f.1.2 ∈ g.red := by
      rw [Finset.mem_sdiff] at h2nothost; push_neg at h2nothost
      exact h2nothost (Finset.mem_univ _)
    have h2notblue : f.1.2 ∉ g.blue := fun hbl =>
      (Finset.disjoint_left.mp g.red_disjoint_blue) h2red hbl
    rcases hb with ⟨_, hb1⟩ | ⟨h2host', _⟩
    · exact Or.inl ⟨hb1, h2notblue⟩
    · exact absurd h2host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h2red)
  · have h1red : f.1.1 ∈ g.red := by
      rw [Finset.mem_sdiff] at h1nothost; push_neg at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h1notblue : f.1.1 ∉ g.blue := fun hbl =>
      (Finset.disjoint_left.mp g.red_disjoint_blue) h1red hbl
    rcases hb with ⟨h1host', _⟩ | ⟨_, hb2⟩
    · exact absurd h1host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1red)
    · exact Or.inr ⟨h1notblue, hb2⟩

/-- A boundary edge of the host `univ \ red` whose host-side endpoint lies in the
complement block is a boundary edge of the complement block. -/
theorem ThreeBlockGeometry.isComplBoundaryEdge_of_hostBoundary_compl
    {f : Edge G} (hf : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) f)
    (hc : (f.1.1 ∈ Finset.univ \ g.red ∧ f.1.1 ∈ g.complement) ∨
      (f.1.2 ∈ Finset.univ \ g.red ∧ f.1.2 ∈ g.complement)) :
    IsRegionBoundaryEdge (G := G) g.complement f := by
  rcases hf with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
  · have h2red : f.1.2 ∈ g.red := by
      rw [Finset.mem_sdiff] at h2nothost; push_neg at h2nothost
      exact h2nothost (Finset.mem_univ _)
    have h2notcompl : f.1.2 ∉ g.complement := fun hcl =>
      (Finset.disjoint_left.mp g.red_disjoint_complement) h2red hcl
    rcases hc with ⟨_, hc1⟩ | ⟨h2host', _⟩
    · exact Or.inl ⟨hc1, h2notcompl⟩
    · exact absurd h2host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h2red)
  · have h1red : f.1.1 ∈ g.red := by
      rw [Finset.mem_sdiff] at h1nothost; push_neg at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h1notcompl : f.1.1 ∉ g.complement := fun hcl =>
      (Finset.disjoint_left.mp g.red_disjoint_complement) h1red hcl
    rcases hc with ⟨h1host', _⟩ | ⟨_, hc2⟩
    · exact absurd h1host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1red)
    · exact Or.inr ⟨h1notcompl, hc2⟩

/-- The host-side endpoint of a host boundary edge lies in the blue block or in the
complement block, by the disjoint cover `univ \ red = blue ⊔ complement`. -/
theorem ThreeBlockGeometry.hostBoundary_hostVertex_mem_blue_or_compl
    {f : Edge G} (hf : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) f) :
    (f.1.1 ∈ Finset.univ \ g.red ∧ (f.1.1 ∈ g.blue ∨ f.1.1 ∈ g.complement)) ∨
      (f.1.2 ∈ Finset.univ \ g.red ∧ (f.1.2 ∈ g.blue ∨ f.1.2 ∈ g.complement)) := by
  have hsplit : ∀ w : V, w ∈ Finset.univ \ g.red → w ∈ g.blue ∨ w ∈ g.complement := by
    intro w hw
    rw [g.sdiff_red_eq_blue_union_complement] at hw
    exact Finset.mem_union.mp hw
  rcases hf with ⟨h1host, _⟩ | ⟨_, h2host⟩
  · exact Or.inl ⟨h1host, hsplit _ h1host⟩
  · exact Or.inr ⟨h2host, hsplit _ h2host⟩

/-- The host boundary configuration reconstructed from a blue boundary configuration
`bβ` and a complement boundary configuration `bc'`: on a host boundary edge whose
host-side endpoint lies in the blue block, read the blue value `bβ` (the edge is a
blue boundary edge); otherwise the host-side endpoint lies in the complement block,
and read the complement value `bc'` (the edge is a complement boundary edge).

The blue and complement values agree where both apply only through the consistency on
shared blue/complement crossing edges; here the two pieces never overlap, since a host
boundary edge's host-side endpoint lies in exactly one block. -/
noncomputable def ThreeBlockGeometry.hostLabelFrom
    (bβ : RegionBoundaryConfig (G := G) A g.blue)
    (bc' : RegionBoundaryConfig (G := G) A g.complement) :
    RegionBoundaryConfig (G := G) A (Finset.univ \ g.red) :=
  fun f =>
    if hb : (f.1.1.1 ∈ Finset.univ \ g.red ∧ f.1.1.1 ∈ g.blue) ∨
        (f.1.1.2 ∈ Finset.univ \ g.red ∧ f.1.1.2 ∈ g.blue) then
      bβ ⟨f.1, g.isBlueBoundaryEdge_of_hostBoundary_blue f.2 hb⟩
    else
      bc' ⟨f.1, g.isComplBoundaryEdge_of_hostBoundary_compl f.2 (by
        rcases g.hostBoundary_hostVertex_mem_blue_or_compl f.2 with
          ⟨h1host, hbc⟩ | ⟨h2host, hbc⟩
        · rcases hbc with hbl | hcl
          · exact absurd (Or.inl ⟨h1host, hbl⟩) hb
          · exact Or.inl ⟨h1host, hcl⟩
        · rcases hbc with hbl | hcl
          · exact absurd (Or.inr ⟨h2host, hbl⟩) hb
          · exact Or.inr ⟨h2host, hcl⟩)⟩

/-- The host boundary label of a global virtual configuration `q` is reconstructed
from its blue and complement boundary labels by `hostLabelFrom`. On a host boundary
edge the reconstruction reads either the blue label or the complement label of `q` at
that edge, both of which equal the global value of `q` there, as does the host label.

This is the structural identity isolating the host residual configuration from the
blue and complement coupling data: a global configuration's host residual is determined
by its blue and complement residuals.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.regionBoundaryLabel_host_eq_hostLabelFrom
    (q : VirtualConfig A) :
    regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q =
      g.hostLabelFrom
        (regionBoundaryLabel (G := G) A g.blue q)
        (regionBoundaryLabel (G := G) A g.complement q) := by
  funext f
  rw [regionBoundaryLabel_apply, hostLabelFrom]
  by_cases hb : (f.1.1.1 ∈ Finset.univ \ g.red ∧ f.1.1.1 ∈ g.blue) ∨
      (f.1.1.2 ∈ Finset.univ \ g.red ∧ f.1.1.2 ∈ g.blue)
  · rw [dif_pos hb, regionBoundaryLabel_apply]
  · rw [dif_neg hb, regionBoundaryLabel_apply]

/-! ### The blue inversion of the host annihilation

A coefficient family `c` annihilating the blocked-region weight family of the host
`univ \ red` annihilates, at every fused blue/complement physical leg, the host
weight. Reading the resulting identity as a function of the blue physical leg and
applying the blue block's chosen left inverse strips the blue block, leaving the
`c`-weighted complement coupling coefficients vanishing for every complement physical
leg and blue boundary configuration. -/

open scoped Classical in
/-- The blue block strips out of the host annihilation. If the coefficient family `c`
annihilates the blocked-region weight family of the host `univ \ red`, then for every
complement physical leg `σcompl` and blue boundary configuration `bβ`, the
`c`-weighted sum of complement coupling coefficients
`threeBlockComplCoeff g bdry σcompl bβ` vanishes.

The annihilation, evaluated at the fused leg `threeBlockComplPhysical g σblue σcompl`,
holds for every blue leg `σblue`. Scaling by the nonzero blue interior bond product
and applying the blue smul-factorization
(`regionInteriorBondProd_smul_geometryBlueWeight_eq`) rewrites the host weights as
the complement-coupling combination of the blue blocked-region weights; the blue
block's chosen left inverse then reads off the complement coupling row.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.complCoeff_combination_eq_zero
    (hblue : RegionBlockedTensorInjective (G := G) A g.blue)
    (c : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        c bdry • regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry = 0)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (bβ : RegionBoundaryConfig (G := G) A g.blue) :
    ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        c bdry • g.threeBlockComplCoeff bdry σcompl bβ = 0 := by
  classical
  -- The σblue-function obtained by `c`-combining the fused host weights.
  set F : RegionPhysicalConfig (V := V) (d := d) g.blue → ℂ :=
    fun σblue => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
      c bdry • regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
        (g.complPhysical σblue σcompl) with hF
  -- The host annihilation makes `F` vanish identically.
  have hFzero : F = 0 := by
    funext σblue
    rw [hF]
    have := congrFun hc (g.complPhysical σblue σcompl)
    simpa [Finset.sum_apply, Pi.smul_apply] using this
  -- Scaling `F` by the blue interior bond product is the complement-coupling
  -- combination of the blue blocked-region weights.
  have hbluefac :
      (regionInteriorBondProd (G := G) A g.blue : ℂ) • F =
        regionBlockedTensorMap (G := G) A g.blue
          (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            c bdry • g.threeBlockComplCoeff bdry σcompl bβ') := by
    rw [hF]
    funext σblue
    rw [Pi.smul_apply, regionBlockedTensorMap_apply]
    -- Distribute the bond multiple through the `c`-combination and apply the blue
    -- smul-factorization to each fused host weight.
    rw [Finset.smul_sum]
    rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          (regionInteriorBondProd (G := G) A g.blue : ℂ) •
            c bdry • regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
              (g.complPhysical σblue σcompl)) =
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry • ((regionInteriorBondProd (G := G) A g.blue : ℂ) •
            regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
              (g.complPhysical σblue σcompl)) from
        Finset.sum_congr rfl (fun bdry _ => by rw [smul_comm])]
    rw [show (∑ μ : RegionBoundaryConfig (G := G) A g.blue,
          (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            c bdry • g.threeBlockComplCoeff bdry σcompl bβ') μ •
              regionBlockedWeight (G := G) A g.blue μ σblue) =
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry • ∑ bβ' : RegionBoundaryConfig (G := G) A g.blue,
            g.threeBlockComplCoeff bdry σcompl bβ' •
              regionBlockedWeight (G := G) A g.blue bβ' σblue from ?_]
    · refine Finset.sum_congr rfl (fun bdry _ => ?_)
      congr 1
      rw [g.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
        bdry σblue σcompl]
    · -- Beta-reduce, distribute the `bβ'`-sum out of each `c bdry` scalar, and swap
      -- the `bdry`/`bβ'` summation order.
      simp only []
      rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            c bdry • ∑ bβ' : RegionBoundaryConfig (G := G) A g.blue,
              g.threeBlockComplCoeff bdry σcompl bβ' •
                regionBlockedWeight (G := G) A g.blue bβ' σblue) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            ∑ bβ' : RegionBoundaryConfig (G := G) A g.blue,
              (c bdry * g.threeBlockComplCoeff bdry σcompl bβ') •
                regionBlockedWeight (G := G) A g.blue bβ' σblue from
        Finset.sum_congr rfl (fun bdry _ => by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun bβ' _ => by rw [smul_smul]))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun bβ' _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun bdry _ => ?_)
      simp only [smul_eq_mul, mul_assoc]
  -- The left side is zero, so the blue blocked map kills the complement coupling row;
  -- injectivity of the blue block forces that row to vanish.
  rw [hFzero, smul_zero] at hbluefac
  have hrow := regionBlockedTensorMap_injective_of_injective (G := G) A g.blue
    (hblue)
    (a₁ := fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
      c bdry • g.threeBlockComplCoeff bdry σcompl bβ')
    (a₂ := 0) (by rw [← hbluefac, map_zero])
  have := congrFun hrow bβ
  simpa using this

/-! ### The blue/red crossing multiplicity collapse of the complement coupling

The complement coupling coefficient `threeBlockComplCoeff g bdry σcompl bβ`, read as a
function of the complement physical leg `σcompl`, lies in the range of the complement
block's blocked-region tensor map, with the coefficient row supported on the single
host residual `bdry` reconstructed from `bβ` and the complement boundary configuration.

The route mirrors `stateCoeff_eq_regionComplement` at the level of the constrained
coupling sum. Grouping the global configurations of `threeBlockComplCoeff` by the
complement boundary configuration `bc'` they induce, each inner sum runs over the
configurations carrying the three prescribed boundary labels (host `bdry`, blue `bβ`,
complement `bc'`). The complement blocked-region weight at `bc'` runs over the larger
family of configurations carrying only the complement label `bc'`; the difference is
the free virtual indices on the red/blue crossing edges, which the complement vertex
product ignores. Projecting away those crossing indices collapses the larger sum onto
the constrained sum with the red/blue crossing bond product as the constant fiber
multiplicity. When no configuration carries the three labels (the host residual is not
the one reconstructed from `bβ` and `bc'`, or `bβ` and `bc'` clash on a blue/complement
crossing edge) the constrained sum is empty and the collapse is the zero identity. -/

/-- The red/blue crossing edges: the boundary edges of the red block that are also
boundary edges of the blue block. These are the free virtual indices distinguishing the
complement blocked-region weight from the constrained complement coupling sum. -/
def ThreeBlockGeometry.IsBlueRedCrossingEdge (_A : Tensor G d) (eg : Edge G) :
    Prop :=
  IsRegionBoundaryEdge (G := G) g.red eg ∧ IsRegionBoundaryEdge (G := G) g.blue eg

instance ThreeBlockGeometry.instDecidableIsBlueRedCrossingEdge (eg : Edge G) :
    Decidable (g.IsBlueRedCrossingEdge A eg) := by
  unfold ThreeBlockGeometry.IsBlueRedCrossingEdge; infer_instance

/-- The bond-dimension product over the red/blue crossing edges: the constant fiber
multiplicity of the complement coupling collapse. -/
noncomputable def ThreeBlockGeometry.blueRedCrossingBondProd (A : Tensor G d) : ℕ :=
  ∏ eg ∈ Finset.univ.filter (fun eg : Edge G => g.IsBlueRedCrossingEdge A eg),
    A.bondDim eg

/-- A red/blue crossing edge is not incident to the complement block: each of its
endpoints lies in the red or blue block, both disjoint from the complement. -/
theorem ThreeBlockGeometry.not_isRegionIncidentEdge_complement_of_blueRedCrossing
    {eg : Edge G} (hg : g.IsBlueRedCrossingEdge A eg) :
    ¬ IsRegionIncidentEdge (G := G) g.complement eg := by
  -- If an endpoint were in the complement it would be outside both red and blue, so
  -- both red and blue boundary edges would put their in-block endpoint on the other
  -- vertex, forcing that vertex into both red and blue — impossible.
  have key : ∀ w : V, w ∈ g.complement →
      (eg.1.1 ∈ g.red ∧ eg.1.2 ∉ g.red ∨ eg.1.1 ∉ g.red ∧ eg.1.2 ∈ g.red) →
      (eg.1.1 ∈ g.blue ∧ eg.1.2 ∉ g.blue ∨ eg.1.1 ∉ g.blue ∧ eg.1.2 ∈ g.blue) →
      (w = eg.1.1 ∨ w = eg.1.2) → False := by
    intro w hw hr hb hwg
    have hwnotred : w ∉ g.red := fun h =>
      (Finset.disjoint_left.mp g.red_disjoint_complement) h hw
    have hwnotblue : w ∉ g.blue := fun h =>
      (Finset.disjoint_left.mp g.blue_disjoint_complement) h hw
    -- The other endpoint lies in both red and blue.
    rcases hwg with hwg | hwg
    · -- `w = eg.1.1`, so `eg.1.1 ∉ red, ∉ blue`; the edges put `eg.1.2 ∈ red ∩ blue`.
      have h1notred : eg.1.1 ∉ g.red := hwg ▸ hwnotred
      have h1notblue : eg.1.1 ∉ g.blue := hwg ▸ hwnotblue
      have h2red : eg.1.2 ∈ g.red := (hr.resolve_left (fun h => h1notred h.1)).2
      have h2blue : eg.1.2 ∈ g.blue := (hb.resolve_left (fun h => h1notblue h.1)).2
      exact (Finset.disjoint_left.mp g.red_disjoint_blue) h2red h2blue
    · have h2notred : eg.1.2 ∉ g.red := hwg ▸ hwnotred
      have h2notblue : eg.1.2 ∉ g.blue := hwg ▸ hwnotblue
      have h1red : eg.1.1 ∈ g.red := (hr.resolve_right (fun h => h2notred h.2)).1
      have h1blue : eg.1.1 ∈ g.blue := (hb.resolve_right (fun h => h2notblue h.2)).1
      exact (Finset.disjoint_left.mp g.red_disjoint_blue) h1red h1blue
  rintro (hc | hc)
  · exact key _ hc hg.1 hg.2 (Or.inl rfl)
  · exact key _ hc hg.1 hg.2 (Or.inr rfl)

/-- The complement vertex product reads a global virtual configuration only through the
complement-incident edges, which never include a red/blue crossing edge. Overwriting a
configuration on the red/blue crossing edges therefore does not change the complement
vertex product. -/
theorem ThreeBlockGeometry.complProd_overwrite_blueRedCrossing_eq
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (ζ ζ' : VirtualConfig A)
    (h : ∀ eg : Edge G, ¬ g.IsBlueRedCrossingEdge A eg → ζ eg = ζ' eg) :
    (∏ w : {w : V // w ∈ g.complement}, A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
      ∏ w : {w : V // w ∈ g.complement}, A.component w.1 (fun ie => ζ' ie.1) (σcompl w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  by_cases hcross : g.IsBlueRedCrossingEdge A ie.1
  · have hinc : IsRegionIncidentEdge (G := G) g.complement ie.1 := by
      have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
      rcases hwinc with hw | hw
      · exact Or.inl (by rw [hw]; exact w.2)
      · exact Or.inr (by rw [hw]; exact w.2)
    exact absurd hinc
      (g.not_isRegionIncidentEdge_complement_of_blueRedCrossing hcross)
  · exact h ie.1 hcross

open scoped Classical in
/-- **The red/blue crossing fiber count.** Among the global configurations carrying the
complement boundary label `bc'`, those projecting (by overwriting the red/blue crossing
edges with a fixed witness `q₀`) onto a fixed configuration `q` are the configurations
agreeing with `q` off the red/blue crossing edges. They biject with the free virtual
indices on the red/blue crossing edges, so the fiber has cardinality
`blueRedCrossingBondProd`. -/
theorem ThreeBlockGeometry.blueRedCrossing_fiber_card
    (bc' : RegionBoundaryConfig (G := G) A g.complement)
    (q₀ q : VirtualConfig A)
    (hq : regionBoundaryLabel (G := G) A g.complement q = bc')
    (hq0cross : ∀ eg : Edge G, g.IsBlueRedCrossingEdge A eg → q eg = q₀ eg) :
    (Finset.univ.filter (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A g.complement ζ = bc' ∧
          (fun eg => if g.IsBlueRedCrossingEdge A eg then q₀ eg else ζ eg) =
            q)).card =
      g.blueRedCrossingBondProd A := by
  classical
  rw [show g.blueRedCrossingBondProd A =
      (Finset.univ : Finset ((eg : {eg : Edge G //
          g.IsBlueRedCrossingEdge A eg}) → Fin (A.bondDim eg.1))).card from ?_]
  · refine Finset.card_nbij'
      (fun ζ eg => ζ eg.1)
      (fun h eg => if hg : g.IsBlueRedCrossingEdge A eg then h ⟨eg, hg⟩ else q eg)
      ?_ ?_ ?_ ?_
    · -- The crossing legs land in the full assignment set.
      intro ζ _; exact Finset.mem_univ _
    · -- The reconstruction lands in the fiber.
      intro h _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · -- Same complement boundary label as `q`: crossing edges are not complement
        -- boundary edges, so the reconstruction agrees with `q` there.
        funext f
        simp only [regionBoundaryLabel_apply]
        by_cases hcross : g.IsBlueRedCrossingEdge A f.1
        · exact absurd (incident_of_boundary (G := G) g.complement f.2)
            (g.not_isRegionIncidentEdge_complement_of_blueRedCrossing hcross)
        · rw [dif_neg hcross]
          have := congrFun hq f
          rwa [regionBoundaryLabel_apply] at this
      · -- Projecting the reconstruction recovers `q`: off the crossing it is `q`, and on
        -- the crossing the projection reads `q₀`, which `q` matches.
        funext eg
        by_cases hcross : g.IsBlueRedCrossingEdge A eg
        · rw [if_pos hcross]; exact (hq0cross eg hcross).symm
        · rw [if_neg hcross, dif_neg hcross]
    · -- Reconstructing from the crossing legs of a fiber element recovers it.
      intro ζ hζ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      obtain ⟨_, hproj⟩ := hζ
      funext eg
      by_cases hcross : g.IsBlueRedCrossingEdge A eg
      · simp only [hcross, dif_pos]
      · simp only [hcross, dif_neg, not_false_iff]
        have := congrFun hproj eg; rw [if_neg hcross] at this; exact this.symm
    · -- Reading the crossing legs of a reconstruction recovers them.
      intro h _
      funext eg
      simp only [eg.2, dif_pos]
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [blueRedCrossingBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun eg : Edge G => g.IsBlueRedCrossingEdge A eg))
        (fun eg => by simp [Finset.mem_filter]) (fun eg => A.bondDim eg)]

/-- A host boundary edge is a red boundary edge: having one endpoint in `univ \ red`
and one in `red` is the same as having one endpoint in `red` and one outside. -/
theorem ThreeBlockGeometry.isRegionBoundaryEdge_red_of_host
    {eg : Edge G} (hg : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) eg) :
    IsRegionBoundaryEdge (G := G) g.red eg := by
  rcases hg with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
  · have h1notred : eg.1.1 ∉ g.red := (Finset.mem_sdiff.mp h1host).2
    have h2red : eg.1.2 ∈ g.red := by
      rw [Finset.mem_sdiff] at h2nothost; push_neg at h2nothost
      exact h2nothost (Finset.mem_univ _)
    exact Or.inr ⟨h1notred, h2red⟩
  · have h1red : eg.1.1 ∈ g.red := by
      rw [Finset.mem_sdiff] at h1nothost; push_neg at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h2notred : eg.1.2 ∉ g.red := (Finset.mem_sdiff.mp h2host).2
    exact Or.inl ⟨h1red, h2notred⟩

/-- A host boundary edge that is not a red/blue crossing edge is a complement boundary
edge: its host-side endpoint lies in the complement (otherwise it would lie in the blue
block and the edge would be a crossing edge). -/
theorem ThreeBlockGeometry.isComplBoundary_of_hostBoundary_not_crossing
    {eg : Edge G} (hg : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) eg)
    (hncross : ¬ g.IsBlueRedCrossingEdge A eg) :
    IsRegionBoundaryEdge (G := G) g.complement eg := by
  -- The host-side endpoint is in `blue ∪ complement`. If it were in blue, with the red
  -- endpoint outside blue, the edge would be a blue boundary edge, making it a crossing
  -- edge. So the host-side endpoint is in the complement.
  rcases g.hostBoundary_hostVertex_mem_blue_or_compl hg with
    ⟨h1host, hbc⟩ | ⟨h2host, hbc⟩
  · rcases hbc with hbl | hcl
    · exact absurd ⟨g.isRegionBoundaryEdge_red_of_host hg,
        g.isBlueBoundaryEdge_of_hostBoundary_blue hg
          (Or.inl ⟨h1host, hbl⟩)⟩ hncross
    · exact g.isComplBoundaryEdge_of_hostBoundary_compl hg
        (Or.inl ⟨h1host, hcl⟩)
  · rcases hbc with hbl | hcl
    · exact absurd ⟨g.isRegionBoundaryEdge_red_of_host hg,
        g.isBlueBoundaryEdge_of_hostBoundary_blue hg
          (Or.inr ⟨h2host, hbl⟩)⟩ hncross
    · exact g.isComplBoundaryEdge_of_hostBoundary_compl hg
        (Or.inr ⟨h2host, hcl⟩)

open scoped Classical in
/-- **The per-fiber complement weight collapse.** When some global configuration `q₀`
carries the three boundary labels (host `bdry`, blue `bβ`, complement `bc'`), the
complement blocked-region weight at `bc'` is the red/blue crossing bond product times
the constrained complement coupling sum over the configurations carrying the three
labels. Grouping the complement-labelled configurations by overwriting their red/blue
crossing indices with those of `q₀`, the complement vertex product is constant on each
fiber and each fiber has cardinality the red/blue crossing bond product. -/
theorem ThreeBlockGeometry.regionBlockedWeight_complement_eq_smul_constrained
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (bβ : RegionBoundaryConfig (G := G) A g.blue)
    (bc' : RegionBoundaryConfig (G := G) A g.complement)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (q₀ : VirtualConfig A)
    (hq0host : regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q₀ = bdry)
    (hq0blue : regionBoundaryLabel (G := G) A g.blue q₀ = bβ)
    (hq0compl : regionBoundaryLabel (G := G) A g.complement q₀ = bc') :
    regionBlockedWeight (G := G) A g.complement bc' σcompl =
      g.blueRedCrossingBondProd A •
        ∑ q ∈ Finset.univ.filter
            (fun q : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A g.complement q = bc'),
          ∏ w : {w : V // w ∈ g.complement},
            A.component w.1 (fun ie => q ie.1) (σcompl w) := by
  classical
  -- `ζ` agrees with `q₀` on every red boundary edge whose far endpoint avoids the blue
  -- block: those are complement boundary edges (`isComplBoundary`), pinned by `bc'`.
  have hagree_compl : ∀ ζ : VirtualConfig A,
      regionBoundaryLabel (G := G) A g.complement ζ = bc' →
      ∀ eg : Edge G, IsRegionBoundaryEdge (G := G) g.complement eg → ζ eg = q₀ eg := by
    intro ζ hζ eg hg
    have h1 := congrFun hζ ⟨eg, hg⟩
    have h2 := congrFun hq0compl ⟨eg, hg⟩
    rw [regionBoundaryLabel_apply] at h1 h2
    rw [h1, h2]
  -- Expand the complement weight and group its configurations by the projection.
  rw [regionBlockedWeight]
  set proj : VirtualConfig A → VirtualConfig A :=
    fun ζ eg => if g.IsBlueRedCrossingEdge A eg then q₀ eg else ζ eg with hproj
  set Sζ := Finset.univ.filter
    (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A g.complement ζ = bc') with hSζ
  set Sq := Finset.univ.filter
    (fun q : VirtualConfig A =>
      regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
        regionBoundaryLabel (G := G) A g.blue q = bβ ∧
          regionBoundaryLabel (G := G) A g.complement q = bc') with hSq
  -- The projection maps `Sζ` into `Sq`.
  have hmaps : ∀ ζ ∈ Sζ, proj ζ ∈ Sq := by
    intro ζ hζ
    rw [hSζ, Finset.mem_filter] at hζ
    rw [hSq, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · -- Host label.
      funext f
      rw [regionBoundaryLabel_apply, hproj]
      simp only
      by_cases hcross : g.IsBlueRedCrossingEdge A f.1
      · rw [if_pos hcross]; exact congrFun hq0host f
      · rw [if_neg hcross]
        -- `f` is a host boundary edge, not crossing, so a complement boundary edge.
        have hcompl := g.isComplBoundary_of_hostBoundary_not_crossing f.2 hcross
        rw [hagree_compl ζ hζ.2 f.1 hcompl]
        exact congrFun hq0host f
    · -- Blue label.
      funext f
      rw [regionBoundaryLabel_apply, hproj]
      simp only
      by_cases hcross : g.IsBlueRedCrossingEdge A f.1
      · rw [if_pos hcross]; exact congrFun hq0blue f
      · rw [if_neg hcross]
        -- A blue boundary edge that is not a crossing edge is a complement boundary edge:
        -- its blue-side endpoint's neighbour lies in the complement, not red.
        have hred : ¬ IsRegionBoundaryEdge (G := G) g.red f.1 := fun hr => hcross ⟨hr, f.2⟩
        have hcompl : IsRegionBoundaryEdge (G := G) g.complement f.1 := by
          -- `f` is a blue boundary edge: one endpoint in blue, one not. The non-blue
          -- endpoint is not in red (else `f` would be a red boundary edge), so it is in
          -- the complement.
          rcases f.2 with ⟨h1blue, h2notblue⟩ | ⟨h1notblue, h2blue⟩
          · have h2notred : f.1.1.2 ∉ g.red := fun h2red =>
              hred (Or.inr ⟨fun h1red =>
                (Finset.disjoint_left.mp g.red_disjoint_blue) h1red h1blue, h2red⟩)
            have h2compl : f.1.1.2 ∈ g.complement := by
              have hcover : f.1.1.2 ∈ g.red ∪ g.blue ∪ g.complement := by
                rw [g.cover_univ]; exact Finset.mem_univ _
              rcases Finset.mem_union.mp hcover with hrb | hc
              · rcases Finset.mem_union.mp hrb with hr | hb
                · exact absurd hr h2notred
                · exact absurd hb h2notblue
              · exact hc
            exact Or.inr ⟨fun h1compl =>
              (Finset.disjoint_left.mp g.blue_disjoint_complement) h1blue h1compl, h2compl⟩
          · have h1notred : f.1.1.1 ∉ g.red := fun h1red =>
              hred (Or.inl ⟨h1red, fun h2red =>
                (Finset.disjoint_left.mp g.red_disjoint_blue) h2red h2blue⟩)
            have h1compl : f.1.1.1 ∈ g.complement := by
              have hcover : f.1.1.1 ∈ g.red ∪ g.blue ∪ g.complement := by
                rw [g.cover_univ]; exact Finset.mem_univ _
              rcases Finset.mem_union.mp hcover with hrb | hc
              · rcases Finset.mem_union.mp hrb with hr | hb
                · exact absurd hr h1notred
                · exact absurd hb h1notblue
              · exact hc
            exact Or.inl ⟨h1compl, fun h2compl =>
              (Finset.disjoint_left.mp g.blue_disjoint_complement) h2blue h2compl⟩
        rw [hagree_compl ζ hζ.2 f.1 hcompl]
        exact congrFun hq0blue f
    · -- Complement label unchanged.
      funext f
      rw [regionBoundaryLabel_apply, hproj]
      simp only
      by_cases hcross : g.IsBlueRedCrossingEdge A f.1
      · exact absurd (incident_of_boundary (G := G) g.complement f.2)
          (g.not_isRegionIncidentEdge_complement_of_blueRedCrossing hcross)
      · rw [if_neg hcross]
        have := congrFun hζ.2 f; rwa [regionBoundaryLabel_apply] at this
  -- Group the complement-labelled sum fiberwise over the projection.
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun ζ => ∏ w : {w : V // w ∈ g.complement},
      A.component w.1 (fun ie => ζ ie.1) (σcompl w))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [hSq, Finset.mem_filter] at hq
  -- On the fiber over `q`, the complement product is constant `∏compl(q)`.
  rw [Finset.sum_congr rfl (g := fun _ => ∏ w : {w : V // w ∈ g.complement},
        A.component w.1 (fun ie => q ie.1) (σcompl w))
    (fun ζ hζ => by
      rw [Finset.mem_filter] at hζ
      rw [hSζ, Finset.mem_filter] at hζ
      refine g.complProd_overwrite_blueRedCrossing_eq σcompl ζ q
        (fun eg hg => ?_)
      have := congrFun hζ.2 eg
      rw [hproj] at this; simp only at this; rwa [if_neg hg] at this)]
  rw [Finset.sum_const]
  -- `q` and `q₀` agree on the red/blue crossing edges, which are host boundary edges
  -- where both carry the host label `bdry`.
  have hqcross : ∀ eg : Edge G, g.IsBlueRedCrossingEdge A eg → q eg = q₀ eg := by
    intro eg hg
    -- A crossing edge is a red boundary edge, hence a host boundary edge.
    have hhost : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) eg := by
      rcases hg.1 with ⟨h1red, h2notred⟩ | ⟨h1notred, h2red⟩
      · exact Or.inr ⟨by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1red,
          by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h2notred⟩⟩
      · exact Or.inl ⟨by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h1notred⟩,
          by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h2red⟩
    have h1 := congrFun hq.2.1 ⟨eg, hhost⟩
    have h2 := congrFun hq0host ⟨eg, hhost⟩
    rw [regionBoundaryLabel_apply] at h1 h2
    rw [h1, ← h2]
  -- The fiber cardinality is the red/blue crossing bond product.
  rw [show (Finset.filter (fun ζ => proj ζ = q) Sζ) =
        Finset.univ.filter (fun ζ : VirtualConfig A =>
          regionBoundaryLabel (G := G) A g.complement ζ = bc' ∧
            (fun eg => if g.IsBlueRedCrossingEdge A eg then q₀ eg else ζ eg) = q)
      from by rw [hSζ, hproj, Finset.filter_filter],
    g.blueRedCrossing_fiber_card bc' q₀ q hq.2.2.2 hqcross]

open scoped Classical in
/-- **The complement coupling collapse.** The red/blue crossing bond multiple of the
complement coupling coefficient, read as a function of the complement physical leg, is
the complement-blocked combination of the complement blocked-region weights with the
coefficient row supported on the complement boundary configurations `bc'` that, together
with `bβ`, are realized by a global configuration carrying host residual `bdry`.

Grouping the constrained coupling sum by the complement boundary configuration and
collapsing each group through the per-fiber identity
`regionBlockedWeight_complement_eq_smul_constrained`, the coupling coefficient becomes a
combination of complement blocked-region weights with the prescribed indicator
coefficients.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (bβ : RegionBoundaryConfig (G := G) A g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (g.blueRedCrossingBondProd A : ℂ) •
        g.threeBlockComplCoeff bdry σcompl bβ =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
              regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                regionBoundaryLabel (G := G) A g.complement q = bc'
          then (1 : ℂ) else 0) •
          regionBlockedWeight (G := G) A g.complement bc' σcompl := by
  classical
  -- Group the constrained coupling sum by the complement boundary configuration.
  rw [threeBlockComplCoeff, ← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter
      (fun q : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
          regionBoundaryLabel (G := G) A g.blue q = bβ))
    (t := (Finset.univ : Finset (RegionBoundaryConfig (G := G) A g.complement)))
    (g := fun q => regionBoundaryLabel (G := G) A g.complement q)
    (fun q _ => Finset.mem_univ _)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  -- Recognize the `bc'`-group as the three-label constrained set.
  rw [show (Finset.univ.filter
        (fun q : VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
            regionBoundaryLabel (G := G) A g.blue q = bβ)).filter
          (fun q => regionBoundaryLabel (G := G) A g.complement q = bc') =
        Finset.univ.filter
          (fun q : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
              regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                regionBoundaryLabel (G := G) A g.complement q = bc')
      from by
        rw [Finset.filter_filter]
        refine Finset.filter_congr (fun q _ => ?_)
        constructor
        · rintro ⟨⟨hh, hb⟩, hc⟩; exact ⟨hh, hb, hc⟩
        · rintro ⟨hh, hb, hc⟩; exact ⟨⟨hh, hb⟩, hc⟩]
  by_cases hex : ∃ q : VirtualConfig A,
      regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
        regionBoundaryLabel (G := G) A g.blue q = bβ ∧
          regionBoundaryLabel (G := G) A g.complement q = bc'
  · obtain ⟨q₀, hq0host, hq0blue, hq0compl⟩ := hex
    rw [if_pos ⟨q₀, hq0host, hq0blue, hq0compl⟩, one_smul,
      g.regionBlockedWeight_complement_eq_smul_constrained bdry bβ bc'
        σcompl q₀ hq0host hq0blue hq0compl, Nat.cast_smul_eq_nsmul]
  · rw [if_neg hex, zero_smul]
    -- No configuration carries the three labels: the constrained sum is empty.
    rw [Finset.filter_eq_empty_iff.mpr (fun q _ => ?_), Finset.sum_empty, smul_zero]
    rintro ⟨hh, hb, hc⟩
    exact hex ⟨q, hh, hb, hc⟩

/-! ### Surjectivity of the host boundary label

Every host boundary configuration is realized by some global virtual configuration:
extend the boundary values to a total configuration, reading an arbitrary index on
the non-boundary edges, which exist because every bond dimension is positive. -/

open scoped Classical in
/-- **Realizing a host boundary configuration.** With positive bond dimensions, every
host boundary configuration `bdry` is the host boundary label of some global virtual
configuration: read `bdry` on the host boundary edges and an arbitrary index elsewhere.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.exists_regionBoundaryLabel_host_eq
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    ∃ q : VirtualConfig A, regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry := by
  classical
  refine ⟨fun eg => if hg : IsRegionBoundaryEdge (G := G) (Finset.univ \ g.red) eg then
      bdry ⟨eg, hg⟩
    else ⟨0, hpos eg⟩, ?_⟩
  funext f
  rw [regionBoundaryLabel_apply, dif_pos f.2]

/-! ### The union of the blue and complement blocks is injective

Assembling the blue inversion, the complement coupling collapse, and the host boundary
surjectivity into the source's `injective_union` for the load-bearing instance: the
host block `univ \ red`, the union of the blue and complement blocks, is blocked-tensor
injective. -/

open scoped Classical in
/-- **The union lemma of the normal PEPS Fundamental Theorem.** The host block
`univ \ red`, the union of the blue and complement injective blocks of the geometry, is blocked-tensor injective.

A coefficient family `c` annihilating the host blocked-region weight family is stripped
of the blue block (`complCoeff_combination_eq_zero`), leaving the `c`-weighted complement
coupling coefficients vanishing for every complement physical leg and blue boundary
configuration. The complement coupling collapse
(`blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq`) reads each as a complement-blocked
combination; injectivity of the complement block forces, for every blue and complement
boundary configuration realized by a global configuration, the host residual coefficient
reconstructed from them to vanish. Surjectivity of the host boundary label
(`exists_regionBoundaryLabel_host_eq`) makes every host residual realized, so `c = 0`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.regionBlockedTensorInjective_union
    (hblue : RegionBlockedTensorInjective (G := G) A g.blue)
    (hcompl : RegionBlockedTensorInjective (G := G) A g.complement)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ g.red) := by
  classical
  rw [RegionBlockedTensorInjective, Fintype.linearIndependent_iff]
  intro c hc
  -- The annihilation hypothesis as a function identity.
  have hc0 : ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
      c bdry • regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry = 0 := hc
  -- Strip the blue block: the `c`-weighted complement coupling row vanishes.
  have hstrip := g.complCoeff_combination_eq_zero hblue c hc0
  -- For each blue boundary configuration, the complement coupling row lies in the kernel
  -- of the complement block, hence vanishes.
  have hrow : ∀ bβ : RegionBoundaryConfig (G := G) A g.blue,
      (fun bc' : RegionBoundaryConfig (G := G) A g.complement =>
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                  regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                    regionBoundaryLabel (G := G) A g.complement q = bc'
              then (1 : ℂ) else 0)) = 0 := by
    intro bβ
    -- The complement-blocked map of the coupling row is the crossing multiple of the
    -- stripped coupling combination, which vanishes.
    have hmap : regionBlockedTensorMap (G := G) A g.complement
        (fun bc' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                  regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                    regionBoundaryLabel (G := G) A g.complement q = bc'
              then (1 : ℂ) else 0)) = 0 := by
      funext σcompl
      rw [regionBlockedTensorMap_apply, Pi.zero_apply]
      -- Distribute each coefficient sum over the weight, then swap the summation order.
      rw [Finset.sum_congr rfl (g := fun bc' =>
            ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
              (c bdry •
                  (if ∃ q : VirtualConfig A,
                      regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                        regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                          regionBoundaryLabel (G := G) A g.complement q = bc'
                    then (1 : ℂ) else 0)) •
                regionBlockedWeight (G := G) A g.complement bc' σcompl)
          (fun bc' _ => Finset.sum_smul)]
      rw [Finset.sum_comm]
      rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
              (c bdry •
                  (if ∃ q : VirtualConfig A,
                      regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                        regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                          regionBoundaryLabel (G := G) A g.complement q = bc'
                    then (1 : ℂ) else 0)) •
                regionBlockedWeight (G := G) A g.complement bc' σcompl) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            c bdry •
              ((g.blueRedCrossingBondProd A : ℂ) •
                g.threeBlockComplCoeff bdry σcompl bβ) from ?_]
      · -- The `c`-combination of the crossing multiples of the coupling vanishes.
        rw [Finset.sum_congr rfl (g := fun bdry =>
              (g.blueRedCrossingBondProd A : ℂ) •
                (c bdry • g.threeBlockComplCoeff bdry σcompl bβ))
            (fun bdry _ => smul_comm _ _ _),
          ← Finset.smul_sum, hstrip σcompl bβ, smul_zero]
      · refine Finset.sum_congr rfl (fun bdry _ => ?_)
        rw [g.blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq bdry bβ σcompl,
          Finset.smul_sum]
        refine Finset.sum_congr rfl (fun bc' _ => ?_)
        rw [smul_assoc]
    have := regionBlockedTensorMap_injective_of_injective (G := G) A g.complement hcompl
      (a₁ := fun bc' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        c bdry •
          (if ∃ q : VirtualConfig A,
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A g.complement q = bc'
            then (1 : ℂ) else 0))
      (a₂ := 0) (by rw [hmap, map_zero])
    exact this
  -- Extract `c` at every host residual realized by a global configuration.
  intro bdry
  obtain ⟨q, hq⟩ := g.exists_regionBoundaryLabel_host_eq bdry hpos
  -- Apply the vanishing coupling row at the blue and complement labels of `q`.
  have hq0 := congrFun (hrow (regionBoundaryLabel (G := G) A g.blue q))
    (regionBoundaryLabel (G := G) A g.complement q)
  simp only [Pi.zero_apply] at hq0
  -- The indicator selects the single host residual `host q = bdry`.
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q)] at hq0
  · rw [if_pos ⟨q, rfl, rfl, rfl⟩, smul_eq_mul, mul_one] at hq0
    rw [← hq]; exact hq0
  · intro bdry' _ hne
    -- Any global configuration realizing the blue and complement labels of `q` has host
    -- residual `host q`, so the indicator at `bdry' ≠ host q` is zero.
    rw [if_neg ?_, smul_zero]
    rintro ⟨q', hh', hb', hc'⟩
    apply hne
    have e1 := g.regionBoundaryLabel_host_eq_hostLabelFrom q'
    have e2 := g.regionBoundaryLabel_host_eq_hostLabelFrom q
    rw [hh', hb', hc'] at e1
    rw [e2]
    -- `host q' = hostLabelFrom (blue q) (compl q) = host q`, and `host q' = bdry'`.
    rw [← e1] at e2 ⊢ <;> exact e2
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The disjoint two-region union lemma

Specializing the three-block geometry to `blue := S`, `complement := T`, and
`red := univ \ (S ∪ T)` gives the source's union-of-injective-regions lemma for two
disjoint regions, with neither the red block's injectivity nor a distinguished edge.
-/

/-- The three-block geometry of two disjoint regions `S`, `T`: the blue block is `S`,
the complement block is `T`, and the red block is the set complement of their union.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
def twoRegionGeometry (S T : Finset V) (hST : Disjoint S T) : ThreeBlockGeometry V where
  red := Finset.univ \ (S ∪ T)
  blue := S
  complement := T
  red_disjoint_blue := by
    rw [Finset.disjoint_left]
    intro v hv hvS
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hvS)
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hv hvT
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ hvT)
  blue_disjoint_complement := hST
  cover_univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto

@[simp] theorem twoRegionGeometry_blue (S T : Finset V) (hST : Disjoint S T) :
    (twoRegionGeometry (V := V) S T hST).blue = S := rfl

@[simp] theorem twoRegionGeometry_complement (S T : Finset V) (hST : Disjoint S T) :
    (twoRegionGeometry (V := V) S T hST).complement = T := rfl

@[simp] theorem twoRegionGeometry_red (S T : Finset V) (hST : Disjoint S T) :
    (twoRegionGeometry (V := V) S T hST).red = Finset.univ \ (S ∪ T) := rfl

/-- The host block of the two-region geometry is the union `S ∪ T`. -/
theorem twoRegionGeometry_univ_sdiff_red (S T : Finset V) (hST : Disjoint S T) :
    Finset.univ \ (twoRegionGeometry (V := V) S T hST).red = S ∪ T := by
  rw [twoRegionGeometry_red]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not, Finset.mem_union]

/-- **The general union-of-injective-regions lemma.** For two disjoint finite regions
`S`, `T` whose blocked tensors are injective, and with every virtual bond dimension
positive, the blocked tensor of their union `S ∪ T` is injective. This is the
source-faithful statement of Lemma `injective_union`: it assumes injectivity of the
two unioned regions only, with no injectivity hypothesis on the complement and no
distinguished edge.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_union_disjoint
    {S T : Finset V} (hST : Disjoint S T)
    (hS : RegionBlockedTensorInjective (G := G) A S)
    (hT : RegionBlockedTensorInjective (G := G) A T)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    RegionBlockedTensorInjective (G := G) A (S ∪ T) := by
  have h := (twoRegionGeometry (V := V) S T hST).regionBlockedTensorInjective_union
    (A := A) (by rw [twoRegionGeometry_blue]; exact hS)
    (by rw [twoRegionGeometry_complement]; exact hT) hpos
  rwa [twoRegionGeometry_univ_sdiff_red] at h

/-- **The finite disjoint union of injective regions is injective.** For a nonempty
finite family of pairwise-disjoint regions whose blocked tensors are each injective,
and with every virtual bond dimension positive, the blocked tensor of their union is
injective. This is the finite iteration of the disjoint union lemma, the disjoint
analogue used when a region is presented as a union of disjoint injective blocks.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and the examples
following it, lines 1322--1430 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_biUnion_disjoint {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (R : ι → Finset V)
    (hdisj : (s : Set ι).Pairwise (fun i j => Disjoint (R i) (R j)))
    (hR : ∀ i ∈ s, RegionBlockedTensorInjective (G := G) A (R i))
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    RegionBlockedTensorInjective (G := G) A (s.biUnion R) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hR i (by simp)
  | cons i t hi ht ih =>
      rw [Finset.cons_eq_insert, Finset.biUnion_insert]
      have hdisj_it : Disjoint (R i) (t.biUnion R) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj (by simp) (by simp [hj])
          (by rintro rfl; exact hi hj)
      refine regionBlockedTensorInjective_union_disjoint hdisj_it
        (hR i (by simp)) (ih ?_ ?_) hpos
      · exact hdisj.mono (by simp [Finset.coe_cons, Set.subset_insert])
      · exact fun j hj => hR j (by simp [hj])

end PEPS
end TNLean
