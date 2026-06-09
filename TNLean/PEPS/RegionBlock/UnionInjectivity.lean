import TNLean.PEPS.RegionBlock.ThreeBlockResonate2

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
      rw [Finset.mem_sdiff] at h2nothost; push_neg at h2nothost
      exact h2nothost (Finset.mem_univ _)
    have h2notblue : f.1.2 ∉ D.blue := fun hbl =>
      (Finset.disjoint_left.mp D.red_disjoint_blue) h2red hbl
    rcases hb with ⟨_, hb1⟩ | ⟨h2host', _⟩
    · exact Or.inl ⟨hb1, h2notblue⟩
    · exact absurd h2host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h2red)
  · have h1red : f.1.1 ∈ D.red := by
      rw [Finset.mem_sdiff] at h1nothost; push_neg at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h1notblue : f.1.1 ∉ D.blue := fun hbl =>
      (Finset.disjoint_left.mp D.red_disjoint_blue) h1red hbl
    rcases hb with ⟨h1host', _⟩ | ⟨_, hb2⟩
    · exact absurd h1host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1red)
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
      rw [Finset.mem_sdiff] at h2nothost; push_neg at h2nothost
      exact h2nothost (Finset.mem_univ _)
    have h2notcompl : f.1.2 ∉ D.complement := fun hcl =>
      (Finset.disjoint_left.mp D.red_disjoint_complement) h2red hcl
    rcases hc with ⟨_, hc1⟩ | ⟨h2host', _⟩
    · exact Or.inl ⟨hc1, h2notcompl⟩
    · exact absurd h2host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h2red)
  · have h1red : f.1.1 ∈ D.red := by
      rw [Finset.mem_sdiff] at h1nothost; push_neg at h1nothost
      exact h1nothost (Finset.mem_univ _)
    have h1notcompl : f.1.1 ∉ D.complement := fun hcl =>
      (Finset.disjoint_left.mp D.red_disjoint_complement) h1red hcl
    rcases hc with ⟨h1host', _⟩ | ⟨_, hc2⟩
    · exact absurd h1host' (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1red)
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
        c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ = 0 := by
  classical
  -- The σblue-function obtained by `c`-combining the fused host weights.
  set F : RegionPhysicalConfig (V := V) (d := d) D.blue → ℂ :=
    fun σblue => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
      c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) with hF
  -- The host annihilation makes `F` vanish identically.
  have hFzero : F = 0 := by
    funext σblue
    rw [hF]
    have := congrFun hc (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)
    simpa [Finset.sum_apply, Pi.smul_apply] using this
  -- Scaling `F` by the blue interior bond product is the complement-coupling
  -- combination of the blue blocked-region weights.
  have hbluefac :
      (regionInteriorBondProd (G := G) A D.blue : ℂ) • F =
        regionBlockedTensorMap (G := G) A D.blue
          (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ') := by
    rw [hF]
    funext σblue
    rw [Pi.smul_apply, regionBlockedTensorMap_apply]
    -- Distribute the bond multiple through the `c`-combination and apply the blue
    -- smul-factorization to each fused host weight.
    rw [Finset.smul_sum]
    rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          (regionInteriorBondProd (G := G) A D.blue : ℂ) •
            c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
              (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          c bdry • ((regionInteriorBondProd (G := G) A D.blue : ℂ) •
            regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
              (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) from
        Finset.sum_congr rfl (fun bdry _ => by rw [smul_comm])]
    rw [show (∑ μ : RegionBoundaryConfig (G := G) A D.blue,
          (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ') μ •
              regionBlockedWeight (G := G) A D.blue μ σblue) =
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          c bdry • ∑ bβ' : RegionBoundaryConfig (G := G) A D.blue,
            threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ' •
              regionBlockedWeight (G := G) A D.blue bβ' σblue from ?_]
    · refine Finset.sum_congr rfl (fun bdry _ => ?_)
      congr 1
      rw [regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
        (A := A) (e := e) D bdry σblue σcompl]
    · -- Beta-reduce, distribute the `bβ'`-sum out of each `c bdry` scalar, and swap
      -- the `bdry`/`bβ'` summation order.
      simp only []
      rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry • ∑ bβ' : RegionBoundaryConfig (G := G) A D.blue,
              threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ' •
                regionBlockedWeight (G := G) A D.blue bβ' σblue) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            ∑ bβ' : RegionBoundaryConfig (G := G) A D.blue,
              (c bdry * threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ') •
                regionBlockedWeight (G := G) A D.blue bβ' σblue from
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
  have hrow := regionBlockedTensorMap_injective_of_injective (G := G) A D.blue
    (regionBlockedTensorInjective_blue (A := A) (e := e) D)
    (a₁ := fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
      c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ')
    (a₂ := 0) (by rw [← hbluefac, map_zero])
  have := congrFun hrow bβ
  simpa using this

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
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D ie.1
  · have hinc : IsRegionIncidentEdge (G := G) D.complement ie.1 := by
      have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
      rcases hwinc with hw | hw
      · exact Or.inl (by rw [hw]; exact w.2)
      · exact Or.inr (by rw [hw]; exact w.2)
    exact absurd hinc
      (not_isRegionIncidentEdge_complement_of_blueRedCrossing (A := A) (e := e) D hcross)
  · exact h ie.1 hcross

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
      rw [Finset.mem_sdiff] at h2nothost; push_neg at h2nothost
      exact h2nothost (Finset.mem_univ _)
    exact Or.inr ⟨h1notred, h2red⟩
  · have h1red : g.1.1 ∈ D.red := by
      rw [Finset.mem_sdiff] at h1nothost; push_neg at h1nothost
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
            A.component w.1 (fun ie => q ie.1) (σcompl w) := by
  classical
  -- `ζ` agrees with `q₀` on every red boundary edge whose far endpoint avoids the blue
  -- block: those are complement boundary edges (`isComplBoundary`), pinned by `bc'`.
  have hagree_compl : ∀ ζ : VirtualConfig A,
      regionBoundaryLabel (G := G) A D.complement ζ = bc' →
      ∀ g : Edge G, IsRegionBoundaryEdge (G := G) D.complement g → ζ g = q₀ g := by
    intro ζ hζ g hg
    have h1 := congrFun hζ ⟨g, hg⟩
    have h2 := congrFun hq0compl ⟨g, hg⟩
    rw [regionBoundaryLabel_apply] at h1 h2
    rw [h1, h2]
  -- Expand the complement weight and group its configurations by the projection.
  rw [regionBlockedWeight]
  set proj : VirtualConfig A → VirtualConfig A :=
    fun ζ g => if IsBlueRedCrossingEdge (A := A) (e := e) D g then q₀ g else ζ g with hproj
  set Sζ := Finset.univ.filter
    (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A D.complement ζ = bc') with hSζ
  set Sq := Finset.univ.filter
    (fun q : VirtualConfig A =>
      regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
        regionBoundaryLabel (G := G) A D.blue q = bβ ∧
          regionBoundaryLabel (G := G) A D.complement q = bc') with hSq
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
      by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D f.1
      · rw [if_pos hcross]; exact congrFun hq0host f
      · rw [if_neg hcross]
        -- `f` is a host boundary edge, not crossing, so a complement boundary edge.
        have hcompl := isComplBoundary_of_hostBoundary_not_crossing (A := A) (e := e) D f.2 hcross
        rw [hagree_compl ζ hζ.2 f.1 hcompl]
        exact congrFun hq0host f
    · -- Blue label.
      funext f
      rw [regionBoundaryLabel_apply, hproj]
      simp only
      by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D f.1
      · rw [if_pos hcross]; exact congrFun hq0blue f
      · rw [if_neg hcross]
        -- A blue boundary edge that is not a crossing edge is a complement boundary edge:
        -- its blue-side endpoint's neighbour lies in the complement, not red.
        have hred : ¬ IsRegionBoundaryEdge (G := G) D.red f.1 := fun hr => hcross ⟨hr, f.2⟩
        have hcompl : IsRegionBoundaryEdge (G := G) D.complement f.1 := by
          -- `f` is a blue boundary edge: one endpoint in blue, one not. The non-blue
          -- endpoint is not in red (else `f` would be a red boundary edge), so it is in
          -- the complement.
          rcases f.2 with ⟨h1blue, h2notblue⟩ | ⟨h1notblue, h2blue⟩
          · have h2notred : f.1.1.2 ∉ D.red := fun h2red =>
              hred (Or.inr ⟨fun h1red =>
                (Finset.disjoint_left.mp D.red_disjoint_blue) h1red h1blue, h2red⟩)
            have h2compl : f.1.1.2 ∈ D.complement := by
              have hcover : f.1.1.2 ∈ D.red ∪ D.blue ∪ D.complement := by
                rw [D.cover_univ]; exact Finset.mem_univ _
              rcases Finset.mem_union.mp hcover with hrb | hc
              · rcases Finset.mem_union.mp hrb with hr | hb
                · exact absurd hr h2notred
                · exact absurd hb h2notblue
              · exact hc
            exact Or.inr ⟨fun h1compl =>
              (Finset.disjoint_left.mp D.blue_disjoint_complement) h1blue h1compl, h2compl⟩
          · have h1notred : f.1.1.1 ∉ D.red := fun h1red =>
              hred (Or.inl ⟨h1red, fun h2red =>
                (Finset.disjoint_left.mp D.red_disjoint_blue) h2red h2blue⟩)
            have h1compl : f.1.1.1 ∈ D.complement := by
              have hcover : f.1.1.1 ∈ D.red ∪ D.blue ∪ D.complement := by
                rw [D.cover_univ]; exact Finset.mem_univ _
              rcases Finset.mem_union.mp hcover with hrb | hc
              · rcases Finset.mem_union.mp hrb with hr | hb
                · exact absurd hr h1notred
                · exact absurd hb h1notblue
              · exact hc
            exact Or.inl ⟨h1compl, fun h2compl =>
              (Finset.disjoint_left.mp D.blue_disjoint_complement) h2blue h2compl⟩
        rw [hagree_compl ζ hζ.2 f.1 hcompl]
        exact congrFun hq0blue f
    · -- Complement label unchanged.
      funext f
      rw [regionBoundaryLabel_apply, hproj]
      simp only
      by_cases hcross : IsBlueRedCrossingEdge (A := A) (e := e) D f.1
      · exact absurd (incident_of_boundary (G := G) D.complement f.2)
          (not_isRegionIncidentEdge_complement_of_blueRedCrossing (A := A) (e := e) D hcross)
      · rw [if_neg hcross]
        have := congrFun hζ.2 f; rwa [regionBoundaryLabel_apply] at this
  -- Group the complement-labelled sum fiberwise over the projection.
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun ζ => ∏ w : {w : V // w ∈ D.complement},
      A.component w.1 (fun ie => ζ ie.1) (σcompl w))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [hSq, Finset.mem_filter] at hq
  -- On the fiber over `q`, the complement product is constant `∏compl(q)`.
  rw [Finset.sum_congr rfl (g := fun _ => ∏ w : {w : V // w ∈ D.complement},
        A.component w.1 (fun ie => q ie.1) (σcompl w))
    (fun ζ hζ => by
      rw [Finset.mem_filter] at hζ
      rw [hSζ, Finset.mem_filter] at hζ
      refine complProd_overwrite_blueRedCrossing_eq (A := A) (e := e) D σcompl ζ q
        (fun g hg => ?_)
      have := congrFun hζ.2 g
      rw [hproj] at this; simp only at this; rwa [if_neg hg] at this)]
  rw [Finset.sum_const]
  -- `q` and `q₀` agree on the red/blue crossing edges, which are host boundary edges
  -- where both carry the host label `bdry`.
  have hqcross : ∀ g : Edge G, IsBlueRedCrossingEdge (A := A) (e := e) D g → q g = q₀ g := by
    intro g hg
    -- A crossing edge is a red boundary edge, hence a host boundary edge.
    have hhost : IsRegionBoundaryEdge (G := G) (Finset.univ \ D.red) g := by
      rcases hg.1 with ⟨h1red, h2notred⟩ | ⟨h1notred, h2red⟩
      · exact Or.inr ⟨by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1red,
          by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h2notred⟩⟩
      · exact Or.inl ⟨by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h1notred⟩,
          by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h2red⟩
    have h1 := congrFun hq.2.1 ⟨g, hhost⟩
    have h2 := congrFun hq0host ⟨g, hhost⟩
    rw [regionBoundaryLabel_apply] at h1 h2
    rw [h1, ← h2]
  -- The fiber cardinality is the red/blue crossing bond product.
  rw [show (Finset.filter (fun ζ => proj ζ = q) Sζ) =
        Finset.univ.filter (fun ζ : VirtualConfig A =>
          regionBoundaryLabel (G := G) A D.complement ζ = bc' ∧
            (fun g => if IsBlueRedCrossingEdge (A := A) (e := e) D g then q₀ g else ζ g) = q)
      from by rw [hSζ, hproj, Finset.filter_filter],
    blueRedCrossing_fiber_card (A := A) (e := e) D bc' q₀ q hq.2.2.2 hqcross]

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
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.red) := by
  classical
  rw [RegionBlockedTensorInjective, Fintype.linearIndependent_iff]
  intro c hc
  -- The annihilation hypothesis as a function identity.
  have hc0 : ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
      c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry = 0 := hc
  -- Strip the blue block: the `c`-weighted complement coupling row vanishes.
  have hstrip := complCoeff_combination_eq_zero (A := A) (e := e) D c hc0
  -- For each blue boundary configuration, the complement coupling row lies in the kernel
  -- of the complement block, hence vanishes.
  have hrow : ∀ bβ : RegionBoundaryConfig (G := G) A D.blue,
      (fun bc' : RegionBoundaryConfig (G := G) A D.complement =>
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          c bdry •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                  regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                    regionBoundaryLabel (G := G) A D.complement q = bc'
              then (1 : ℂ) else 0)) = 0 := by
    intro bβ
    -- The complement-blocked map of the coupling row is the crossing multiple of the
    -- stripped coupling combination, which vanishes.
    have hmap : regionBlockedTensorMap (G := G) A D.complement
        (fun bc' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          c bdry •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                  regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                    regionBoundaryLabel (G := G) A D.complement q = bc'
              then (1 : ℂ) else 0)) = 0 := by
      funext σcompl
      rw [regionBlockedTensorMap_apply, Pi.zero_apply]
      -- Distribute each coefficient sum over the weight, then swap the summation order.
      rw [Finset.sum_congr rfl (g := fun bc' =>
            ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
              (c bdry •
                  (if ∃ q : VirtualConfig A,
                      regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                        regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                          regionBoundaryLabel (G := G) A D.complement q = bc'
                    then (1 : ℂ) else 0)) •
                regionBlockedWeight (G := G) A D.complement bc' σcompl)
          (fun bc' _ => Finset.sum_smul)]
      rw [Finset.sum_comm]
      rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            ∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
              (c bdry •
                  (if ∃ q : VirtualConfig A,
                      regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                        regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                          regionBoundaryLabel (G := G) A D.complement q = bc'
                    then (1 : ℂ) else 0)) •
                regionBlockedWeight (G := G) A D.complement bc' σcompl) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry •
              ((blueRedCrossingBondProd (A := A) (e := e) D : ℂ) •
                threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ) from ?_]
      · -- The `c`-combination of the crossing multiples of the coupling vanishes.
        rw [Finset.sum_congr rfl (g := fun bdry =>
              (blueRedCrossingBondProd (A := A) (e := e) D : ℂ) •
                (c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ))
            (fun bdry _ => smul_comm _ _ _),
          ← Finset.smul_sum, hstrip σcompl bβ, smul_zero]
      · refine Finset.sum_congr rfl (fun bdry _ => ?_)
        rw [blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq (A := A) (e := e) D bdry bβ σcompl,
          Finset.smul_sum]
        refine Finset.sum_congr rfl (fun bc' _ => ?_)
        rw [smul_assoc]
    have := regionBlockedTensorMap_injective_of_injective (G := G) A D.complement _hcompl
      (a₁ := fun bc' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry •
          (if ∃ q : VirtualConfig A,
              regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A D.complement q = bc'
            then (1 : ℂ) else 0))
      (a₂ := 0) (by rw [hmap, map_zero])
    exact this
  -- Extract `c` at every host residual realized by a global configuration.
  intro bdry
  obtain ⟨q, hq⟩ := exists_regionBoundaryLabel_host_eq (A := A) (e := e) D bdry hpos
  -- Apply the vanishing coupling row at the blue and complement labels of `q`.
  have hq0 := congrFun (hrow (regionBoundaryLabel (G := G) A D.blue q))
    (regionBoundaryLabel (G := G) A D.complement q)
  simp only [Pi.zero_apply] at hq0
  -- The indicator selects the single host residual `host q = bdry`.
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q)] at hq0
  · rw [if_pos ⟨q, rfl, rfl, rfl⟩, smul_eq_mul, mul_one] at hq0
    rw [← hq]; exact hq0
  · intro bdry' _ hne
    -- Any global configuration realizing the blue and complement labels of `q` has host
    -- residual `host q`, so the indicator at `bdry' ≠ host q` is zero.
    rw [if_neg ?_, smul_zero]
    rintro ⟨q', hh', hb', hc'⟩
    apply hne
    have e1 := regionBoundaryLabel_host_eq_hostLabelFrom (A := A) (e := e) D q'
    have e2 := regionBoundaryLabel_host_eq_hostLabelFrom (A := A) (e := e) D q
    rw [hh', hb', hc'] at e1
    rw [e2]
    -- `host q' = hostLabelFrom (blue q) (compl q) = host q`, and `host q' = bdry'`.
    rw [← e1] at e2 ⊢ <;> exact e2
  · intro h; exact absurd (Finset.mem_univ _) h

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
