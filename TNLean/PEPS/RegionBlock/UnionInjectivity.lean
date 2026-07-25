/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.ThreeBlockResonate2
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2

/-!
# Injectivity of the union of two injective region blocks

This file proves the union lemma of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`): the contraction of injective tensors over the
union of two disjoint injective regions is again injective. The load-bearing
instance is the union of the blue and complement blocks of a
`NormalEdgeBlockingData`, whose union is the set complement of the red block
(`univ \ red`). The three-block gauge chain needs the host block `univ \ red` to be
blocked-tensor injective, which this file supplies from injectivity of the blue and
complement blocks individually.

The proof is the source's two-step inverse application. Suppose a coefficient
family `c` annihilates the blocked-region weight family of `univ \ red`. Reading the
physical leg of `univ \ red` as a fused blue/complement pair
(`threeBlockComplPhysical`, a bijection onto `univ \ red` legs), the core
factorization `regionInteriorBondProd_smul_threeBlockComplWeight_eq` rewrites the
annihilation as a complement-block combination whose coefficients are the
`c`-weighted blue coupling coefficients. Injectivity of the complement block removes
the complement part, leaving `c`-weighted blue coupling coefficients that vanish for
every complement boundary configuration. The blue coupling coefficient, read as a
function of the blue physical leg, factors through the blue block's blocked-region
weights; injectivity of the blue block then removes the remaining part, forcing
`c = 0`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d} {e : Edge G}

/-! ### Viewing edge blocking data as a bare three-block geometry

The union lemma is proved once over a bare `ThreeBlockGeometry` (in
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2`). The
`NormalEdgeBlockingData`-parametrized theorems of this file are thin wrappers
that view the edge-centred red, blue, and complement blocks as that geometry;
the bridge is `NormalEdgeBlockingData.toThreeBlockGeometry`. -/

/-- View the one-edge blocking data as a bare three-block geometry: the same
red, blue, and complement blocks, keeping only their pairwise disjointness and
the cover of the vertex set, and forgetting the injectivity witnesses and the
distinguished edge. -/
def NormalEdgeBlockingData.toThreeBlockGeometry
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    ThreeBlockGeometry V where
  red := D.red
  blue := D.blue
  complement := D.complement
  red_disjoint_blue := D.red_disjoint_blue
  red_disjoint_complement := D.red_disjoint_complement
  blue_disjoint_complement := D.blue_disjoint_complement
  cover_univ := D.cover_univ

/-! ### Reconstructing a host boundary configuration from blue and complement data

A boundary edge of the host `univ \ red` has one endpoint in `univ \ red` and one in
`red`. The host-side endpoint lies in the blue block or in the complement block (the
two cover `univ \ red`). When it lies in blue the edge is a boundary edge of the blue
block (the red endpoint is outside blue); when it lies in complement the edge is a
boundary edge of the complement block (the red endpoint is outside complement). A host
boundary configuration is therefore the data of a blue boundary configuration on the
blue/red crossing edges and a complement boundary configuration on the complement/red
crossing edges, recombined by `hostLabelFrom`. -/

/-- A boundary edge of the host `univ \ red` whose host-side endpoint lies in the blue
block is a boundary edge of the blue block: the host-side endpoint is in blue, and the
red-side endpoint lies outside blue (the blocks are disjoint). -/
theorem isBlueBoundaryEdge_of_hostBoundary_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    {f : Edge G} (hf : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) f)
    (hb : (f.1.1 ∈ Finset.univ \ D.red ∧ f.1.1 ∈ D.blue) ∨
      (f.1.2 ∈ Finset.univ \ D.red ∧ f.1.2 ∈ D.blue)) :
    IsRegionBoundaryEdge (G := G) D.blue f := by
  rcases hf with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
  · -- `f.1.1 ∈ univ \ red`, `f.1.2 ∈ red`.
    have h2red : f.1.2 ∈ D.red := by
      rw [Finset.mem_sdiff] at h2nothost; push Not at h2nothost
      exact h2nothost (Finset.mem_univ _)
    have h2notblue : f.1.2 ∉ D.blue := fun hbl =>
      (Finset.disjoint_left.mp D.red_disjoint_blue) h2red hbl
    rcases hb with ⟨_, hb1⟩ | ⟨h2host', _⟩
    · exact Or.inl ⟨hb1, h2notblue⟩
    · exact absurd h2host' (by rw [Finset.mem_sdiff]; push Not; exact fun _ => h2red)
  · have h1red : f.1.1 ∈ D.red := by
      rw [Finset.mem_sdiff] at h1nothost; push Not at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h1notblue : f.1.1 ∉ D.blue := fun hbl =>
      (Finset.disjoint_left.mp D.red_disjoint_blue) h1red hbl
    rcases hb with ⟨h1host', _⟩ | ⟨_, hb2⟩
    · exact absurd h1host' (by rw [Finset.mem_sdiff]; push Not; exact fun _ => h1red)
    · exact Or.inr ⟨h1notblue, hb2⟩

/-- A boundary edge of the host `univ \ red` whose host-side endpoint lies in the
complement block is a boundary edge of the complement block. -/
theorem isComplBoundaryEdge_of_hostBoundary_compl
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    {f : Edge G} (hf : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) f)
    (hc : (f.1.1 ∈ Finset.univ \ D.red ∧ f.1.1 ∈ D.complement) ∨
      (f.1.2 ∈ Finset.univ \ D.red ∧ f.1.2 ∈ D.complement)) :
    IsRegionBoundaryEdge (G := G) D.complement f := by
  rcases hf with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
  · have h2red : f.1.2 ∈ D.red := by
      rw [Finset.mem_sdiff] at h2nothost; push Not at h2nothost
      exact h2nothost (Finset.mem_univ _)
    have h2notcompl : f.1.2 ∉ D.complement := fun hcl =>
      (Finset.disjoint_left.mp D.red_disjoint_complement) h2red hcl
    rcases hc with ⟨_, hc1⟩ | ⟨h2host', _⟩
    · exact Or.inl ⟨hc1, h2notcompl⟩
    · exact absurd h2host' (by rw [Finset.mem_sdiff]; push Not; exact fun _ => h2red)
  · have h1red : f.1.1 ∈ D.red := by
      rw [Finset.mem_sdiff] at h1nothost; push Not at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h1notcompl : f.1.1 ∉ D.complement := fun hcl =>
      (Finset.disjoint_left.mp D.red_disjoint_complement) h1red hcl
    rcases hc with ⟨h1host', _⟩ | ⟨_, hc2⟩
    · exact absurd h1host' (by rw [Finset.mem_sdiff]; push Not; exact fun _ => h1red)
    · exact Or.inr ⟨h1notcompl, hc2⟩

/-- The host-side endpoint of a host boundary edge lies in the blue block or in the
complement block, by the disjoint cover `univ \ red = blue ⊔ complement`. -/
theorem hostBoundary_hostVertex_mem_blue_or_compl
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    {f : Edge G} (hf : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) f) :
    (f.1.1 ∈ Finset.univ \ D.red ∧ (f.1.1 ∈ D.blue ∨ f.1.1 ∈ D.complement)) ∨
      (f.1.2 ∈ Finset.univ \ D.red ∧ (f.1.2 ∈ D.blue ∨ f.1.2 ∈ D.complement)) := by
  have hsplit : ∀ w : V, w ∈ Finset.univ \ D.red → w ∈ D.blue ∨ w ∈ D.complement := by
    intro w hw
    rw [sdiff_red_eq_blue_union_complement (A := A) (e := e) D] at hw
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
noncomputable def hostLabelFrom
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bβ : RegionBoundaryConfig (G := G) A D.blue)
    (bc' : RegionBoundaryConfig (G := G) A D.complement) :
    RegionBoundaryConfig (G := G) A (Finset.univ \ D.red) :=
  fun f =>
    if hb : (f.1.1.1 ∈ Finset.univ \ D.red ∧ f.1.1.1 ∈ D.blue) ∨
        (f.1.1.2 ∈ Finset.univ \ D.red ∧ f.1.1.2 ∈ D.blue) then
      bβ ⟨f.1, isBlueBoundaryEdge_of_hostBoundary_blue (A := A) (e := e) D f.2 hb⟩
    else
      bc' ⟨f.1, isComplBoundaryEdge_of_hostBoundary_compl (A := A) (e := e) D f.2 (by
        rcases hostBoundary_hostVertex_mem_blue_or_compl (A := A) (e := e) D f.2 with
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
theorem regionBoundaryLabel_host_eq_hostLabelFrom
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (q : VirtualConfig A) :
    regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q =
      hostLabelFrom (A := A) (e := e) D
        (regionBoundaryLabel (G := G) A D.blue q)
        (regionBoundaryLabel (G := G) A D.complement q) := by
  funext f
  rw [regionBoundaryLabel_apply, hostLabelFrom]
  by_cases hb : (f.1.1.1 ∈ Finset.univ \ D.red ∧ f.1.1.1 ∈ D.blue) ∨
      (f.1.1.2 ∈ Finset.univ \ D.red ∧ f.1.1.2 ∈ D.blue)
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
`threeBlockComplCoeff D bdry σcompl bβ` vanishes.

The annihilation, evaluated at the fused leg `threeBlockComplPhysical D σblue σcompl`,
holds for every blue leg `σblue`. Scaling by the nonzero blue interior bond product
and applying the blue smul-factorization
(`regionInteriorBondProd_smul_threeBlockBlueWeight_eq`) rewrites the host weights as
the complement-coupling combination of the blue blocked-region weights; the blue
block's chosen left inverse then reads off the complement coupling row.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem complCoeff_combination_eq_zero
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (c : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry = 0)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (bβ : RegionBoundaryConfig (G := G) A D.blue) :
    ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ = 0 :=
  D.toThreeBlockGeometry.complCoeff_combination_eq_zero
    (regionBlockedTensorInjective_blue (A := A) (e := e) D) c hc σcompl bβ

/-! ### The blue/red crossing multiplicity collapse of the complement coupling

The complement coupling coefficient `threeBlockComplCoeff D bdry σcompl bβ`, read as a
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
def IsBlueRedCrossingEdge
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) (g : Edge G) :
    Prop :=
  IsRegionBoundaryEdge (G := G) D.red g ∧ IsRegionBoundaryEdge (G := G) D.blue g

instance
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) (g : Edge G) :
    Decidable (IsBlueRedCrossingEdge (A := A) (e := e) D g) := by
  unfold IsBlueRedCrossingEdge; infer_instance

/-- The bond-dimension product over the red/blue crossing edges: the constant fiber
multiplicity of the complement coupling collapse. -/
noncomputable def blueRedCrossingBondProd
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) : ℕ :=
  ∏ g ∈ Finset.univ.filter (fun g : Edge G => IsBlueRedCrossingEdge (A := A) (e := e) D g),
    A.bondDim g

/-- A red/blue crossing edge is not incident to the complement block: each of its
endpoints lies in the red or blue block, both disjoint from the complement. -/
theorem not_isRegionIncidentEdge_complement_of_blueRedCrossing
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    {g : Edge G} (hg : IsBlueRedCrossingEdge (A := A) (e := e) D g) :
    ¬ IsRegionIncidentEdge (G := G) D.complement g := by
  -- If an endpoint were in the complement it would be outside both red and blue, so
  -- both red and blue boundary edges would put their in-block endpoint on the other
  -- vertex, forcing that vertex into both red and blue — impossible.
  have key : ∀ w : V, w ∈ D.complement →
      (g.1.1 ∈ D.red ∧ g.1.2 ∉ D.red ∨ g.1.1 ∉ D.red ∧ g.1.2 ∈ D.red) →
      (g.1.1 ∈ D.blue ∧ g.1.2 ∉ D.blue ∨ g.1.1 ∉ D.blue ∧ g.1.2 ∈ D.blue) →
      (w = g.1.1 ∨ w = g.1.2) → False := by
    intro w hw hr hb hwg
    have hwnotred : w ∉ D.red := fun h =>
      (Finset.disjoint_left.mp D.red_disjoint_complement) h hw
    have hwnotblue : w ∉ D.blue := fun h =>
      (Finset.disjoint_left.mp D.blue_disjoint_complement) h hw
    -- The other endpoint lies in both red and blue.
    rcases hwg with hwg | hwg
    · -- `w = g.1.1`, so `g.1.1 ∉ red, ∉ blue`; the edges put `g.1.2 ∈ red ∩ blue`.
      have h1notred : g.1.1 ∉ D.red := hwg ▸ hwnotred
      have h1notblue : g.1.1 ∉ D.blue := hwg ▸ hwnotblue
      have h2red : g.1.2 ∈ D.red := (hr.resolve_left (fun h => h1notred h.1)).2
      have h2blue : g.1.2 ∈ D.blue := (hb.resolve_left (fun h => h1notblue h.1)).2
      exact (Finset.disjoint_left.mp D.red_disjoint_blue) h2red h2blue
    · have h2notred : g.1.2 ∉ D.red := hwg ▸ hwnotred
      have h2notblue : g.1.2 ∉ D.blue := hwg ▸ hwnotblue
      have h1red : g.1.1 ∈ D.red := (hr.resolve_right (fun h => h2notred h.2)).1
      have h1blue : g.1.1 ∈ D.blue := (hb.resolve_right (fun h => h2notblue h.2)).1
      exact (Finset.disjoint_left.mp D.red_disjoint_blue) h1red h1blue
  rintro (hc | hc)
  · exact key _ hc hg.1 hg.2 (Or.inl rfl)
  · exact key _ hc hg.1 hg.2 (Or.inr rfl)

/-- The complement vertex product reads a global virtual configuration only through the
complement-incident edges, which never include a red/blue crossing edge. Overwriting a
configuration on the red/blue crossing edges therefore does not change the complement
vertex product. -/
theorem complProd_overwrite_blueRedCrossing_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (ζ ζ' : VirtualConfig A)
    (h : ∀ g : Edge G, ¬ IsBlueRedCrossingEdge (A := A) (e := e) D g → ζ g = ζ' g) :
    (∏ w : {w : V // w ∈ D.complement}, A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
      ∏ w : {w : V // w ∈ D.complement}, A.component w.1 (fun ie => ζ' ie.1) (σcompl w) := by
  apply regionProd_subtype_congr
  intro ie hie
  by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D ie
  · exact absurd hie
      (not_isRegionIncidentEdge_complement_of_blueRedCrossing (A := A) (e := e) D hcross)
  · exact h ie hcross

open scoped Classical in
/-- **The red/blue crossing fiber count.** Among the global configurations carrying the
complement boundary label `bc'`, those projecting (by overwriting the red/blue crossing
edges with a fixed witness `q₀`) onto a fixed configuration `q` are the configurations
agreeing with `q` off the red/blue crossing edges. They biject with the free virtual
indices on the red/blue crossing edges, so the fiber has cardinality
`blueRedCrossingBondProd`. -/
theorem blueRedCrossing_fiber_card
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bc' : RegionBoundaryConfig (G := G) A D.complement)
    (q₀ q : VirtualConfig A)
    (hq : regionBoundaryLabel (G := G) A D.complement q = bc')
    (hq0cross : ∀ g : Edge G, IsBlueRedCrossingEdge (A := A) (e := e) D g → q g = q₀ g) :
    (Finset.univ.filter (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A D.complement ζ = bc' ∧
          (fun g => if IsBlueRedCrossingEdge (A := A) (e := e) D g then q₀ g else ζ g) =
            q)).card =
      blueRedCrossingBondProd (A := A) (e := e) D := by
  classical
  rw [show blueRedCrossingBondProd (A := A) (e := e) D =
      (Finset.univ : Finset ((g : {g : Edge G //
          IsBlueRedCrossingEdge (A := A) (e := e) D g}) → Fin (A.bondDim g.1))).card from ?_]
  · refine Finset.card_nbij'
      (fun ζ g => ζ g.1)
      (fun h g => if hg : IsBlueRedCrossingEdge (A := A) (e := e) D g then h ⟨g, hg⟩ else q g)
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
        by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D f.1
        · exact absurd (incident_of_boundary (G := G) D.complement f.2)
            (not_isRegionIncidentEdge_complement_of_blueRedCrossing (A := A) (e := e) D hcross)
        · rw [dif_neg hcross]
          have := congrFun hq f
          rwa [regionBoundaryLabel_apply] at this
      · -- Projecting the reconstruction recovers `q`: off the crossing it is `q`, and on
        -- the crossing the projection reads `q₀`, which `q` matches.
        funext g
        by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D g
        · rw [if_pos hcross]; exact (hq0cross g hcross).symm
        · rw [if_neg hcross, dif_neg hcross]
    · -- Reconstructing from the crossing legs of a fiber element recovers it.
      intro ζ hζ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      obtain ⟨_, hproj⟩ := hζ
      funext g
      by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D g
      · simp only [hcross, dif_pos]
      · simp only [hcross, dif_neg, not_false_iff]
        have := congrFun hproj g; rw [if_neg hcross] at this; exact this.symm
    · -- Reading the crossing legs of a reconstruction recovers them.
      intro h _
      funext g
      simp only [g.2, dif_pos]
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [blueRedCrossingBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun g : Edge G => IsBlueRedCrossingEdge (A := A) (e := e) D g))
        (fun g => by simp [Finset.mem_filter]) (fun g => A.bondDim g)]

/-- A host boundary edge is a red boundary edge: having one endpoint in `univ \ red`
and one in `red` is the same as having one endpoint in `red` and one outside. -/
theorem isRegionBoundaryEdge_red_of_host
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) g) :
    IsRegionBoundaryEdge (G := G) D.red g := by
  rcases hg with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
  · have h1notred : g.1.1 ∉ D.red := (Finset.mem_sdiff.mp h1host).2
    have h2red : g.1.2 ∈ D.red := by
      rw [Finset.mem_sdiff] at h2nothost; push Not at h2nothost
      exact h2nothost (Finset.mem_univ _)
    exact Or.inr ⟨h1notred, h2red⟩
  · have h1red : g.1.1 ∈ D.red := by
      rw [Finset.mem_sdiff] at h1nothost; push Not at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h2notred : g.1.2 ∉ D.red := (Finset.mem_sdiff.mp h2host).2
    exact Or.inl ⟨h1red, h2notred⟩

/-- A host boundary edge that is not a red/blue crossing edge is a complement boundary
edge: its host-side endpoint lies in the complement (otherwise it would lie in the blue
block and the edge would be a crossing edge). -/
theorem isComplBoundary_of_hostBoundary_not_crossing
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) g)
    (hncross : ¬ IsBlueRedCrossingEdge (A := A) (e := e) D g) :
    IsRegionBoundaryEdge (G := G) D.complement g := by
  -- The host-side endpoint is in `blue ∪ complement`. If it were in blue, with the red
  -- endpoint outside blue, the edge would be a blue boundary edge, making it a crossing
  -- edge. So the host-side endpoint is in the complement.
  rcases hostBoundary_hostVertex_mem_blue_or_compl (A := A) (e := e) D hg with
    ⟨h1host, hbc⟩ | ⟨h2host, hbc⟩
  · rcases hbc with hbl | hcl
    · exact absurd ⟨isRegionBoundaryEdge_red_of_host (A := A) (e := e) D hg,
        isBlueBoundaryEdge_of_hostBoundary_blue (A := A) (e := e) D hg
          (Or.inl ⟨h1host, hbl⟩)⟩ hncross
    · exact isComplBoundaryEdge_of_hostBoundary_compl (A := A) (e := e) D hg
        (Or.inl ⟨h1host, hcl⟩)
  · rcases hbc with hbl | hcl
    · exact absurd ⟨isRegionBoundaryEdge_red_of_host (A := A) (e := e) D hg,
        isBlueBoundaryEdge_of_hostBoundary_blue (A := A) (e := e) D hg
          (Or.inr ⟨h2host, hbl⟩)⟩ hncross
    · exact isComplBoundaryEdge_of_hostBoundary_compl (A := A) (e := e) D hg
        (Or.inr ⟨h2host, hcl⟩)

open scoped Classical in
/-- **The per-fiber complement weight collapse.** When some global configuration `q₀`
carries the three boundary labels (host `bdry`, blue `bβ`, complement `bc'`), the
complement blocked-region weight at `bc'` is the red/blue crossing bond product times
the constrained complement coupling sum over the configurations carrying the three
labels. Grouping the complement-labelled configurations by overwriting their red/blue
crossing indices with those of `q₀`, the complement vertex product is constant on each
fiber and each fiber has cardinality the red/blue crossing bond product. -/
theorem regionBlockedWeight_complement_eq_smul_constrained
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (bβ : RegionBoundaryConfig (G := G) A D.blue)
    (bc' : RegionBoundaryConfig (G := G) A D.complement)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (q₀ : VirtualConfig A)
    (hq0host : regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q₀ = bdry)
    (hq0blue : regionBoundaryLabel (G := G) A D.blue q₀ = bβ)
    (hq0compl : regionBoundaryLabel (G := G) A D.complement q₀ = bc') :
    regionBlockedWeight (G := G) A D.complement bc' σcompl =
      blueRedCrossingBondProd (A := A) (e := e) D •
        ∑ q ∈ Finset.univ.filter
            (fun q : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A D.complement q = bc'),
          ∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => q ie.1) (σcompl w) :=
  D.toThreeBlockGeometry.regionBlockedWeight_complement_eq_smul_constrained
    bdry bβ bc' σcompl q₀ hq0host hq0blue hq0compl

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
theorem blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (bβ : RegionBoundaryConfig (G := G) A D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (blueRedCrossingBondProd (A := A) (e := e) D : ℂ) •
        threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ =
      ∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
              regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                regionBoundaryLabel (G := G) A D.complement q = bc'
          then (1 : ℂ) else 0) •
          regionBlockedWeight (G := G) A D.complement bc' σcompl := by
  classical
  -- Group the constrained coupling sum by the complement boundary configuration.
  rw [threeBlockComplCoeff, ← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter
      (fun q : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
          regionBoundaryLabel (G := G) A D.blue q = bβ))
    (t := (Finset.univ : Finset (RegionBoundaryConfig (G := G) A D.complement)))
    (g := fun q => regionBoundaryLabel (G := G) A D.complement q)
    (fun q _ => Finset.mem_univ _)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  -- Recognize the `bc'`-group as the three-label constrained set.
  rw [show (Finset.univ.filter
        (fun q : VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
            regionBoundaryLabel (G := G) A D.blue q = bβ)).filter
          (fun q => regionBoundaryLabel (G := G) A D.complement q = bc') =
        Finset.univ.filter
          (fun q : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
              regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                regionBoundaryLabel (G := G) A D.complement q = bc')
      from by
        rw [Finset.filter_filter]
        refine Finset.filter_congr (fun q _ => ?_)
        constructor
        · rintro ⟨⟨hh, hb⟩, hc⟩; exact ⟨hh, hb, hc⟩
        · rintro ⟨hh, hb, hc⟩; exact ⟨⟨hh, hb⟩, hc⟩]
  by_cases hex : ∃ q : VirtualConfig A,
      regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
        regionBoundaryLabel (G := G) A D.blue q = bβ ∧
          regionBoundaryLabel (G := G) A D.complement q = bc'
  · obtain ⟨q₀, hq0host, hq0blue, hq0compl⟩ := hex
    rw [if_pos ⟨q₀, hq0host, hq0blue, hq0compl⟩, one_smul,
      regionBlockedWeight_complement_eq_smul_constrained (A := A) (e := e) D bdry bβ bc'
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
theorem exists_regionBoundaryLabel_host_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    ∃ q : VirtualConfig A, regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry := by
  classical
  refine ⟨fun g => if hg : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) g then
      bdry ⟨g, hg⟩
    else ⟨0, hpos g⟩, ?_⟩
  funext f
  rw [regionBoundaryLabel_apply, dif_pos f.2]

/-! ### The union of the blue and complement blocks is injective

Assembling the blue inversion, the complement coupling collapse, and the host boundary
surjectivity into the source's `injective_union` for the load-bearing instance: the
host block `univ \ red`, the union of the blue and complement blocks, is blocked-tensor
injective. -/

open scoped Classical in
/-- **The union lemma of the normal PEPS Fundamental Theorem.** The host block
`univ \ red`, the union of the blue and complement injective blocks of a
`NormalEdgeBlockingData`, is blocked-tensor injective.

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
theorem regionBlockedTensorInjective_union
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (_hblue : RegionBlockedTensorInjective (G := G) A D.blue)
    (_hcompl : RegionBlockedTensorInjective (G := G) A D.complement)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.red) :=
  D.toThreeBlockGeometry.regionBlockedTensorInjective_union
    (regionBlockedTensorInjective_blue (A := A) (e := e) D)
    (regionBlockedTensorInjective_complement (A := A) (e := e) D) hpos

/-- **The host block is blocked-tensor injective.** The set complement of the red block
of a `NormalEdgeBlockingData`, the union of the blue and complement blocks, is
blocked-tensor injective: the union lemma applied to the injectivity of the blue and
complement blocks individually.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_compl_red
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.red) :=
  regionBlockedTensorInjective_union (A := A) (e := e) D
    (regionBlockedTensorInjective_blue (A := A) (e := e) D)
    (regionBlockedTensorInjective_complement (A := A) (e := e) D) hpos

end PEPS
end TNLean
