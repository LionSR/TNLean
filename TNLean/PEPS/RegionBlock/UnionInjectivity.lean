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

end PEPS
end TNLean
