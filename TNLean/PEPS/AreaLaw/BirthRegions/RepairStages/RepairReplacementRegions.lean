/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.FanRuns
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.SimultaneousRepair
import Mathlib.Topology.Algebra.ConstMulAction
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairDepth
import Mathlib.Data.Set.Disjoint

/-!
# Replacement sectors from a current wedge assignment

Let the current old regions have identifiers in a type ι and binary labels ξ.
For each current parent occurrence p, an assignment σₚ associates the eight
elementary wedges with old identifiers. Consecutive wedges of equal exterior
label form one connected run. The closed birth of a replacement is the affine
image of the union of the triangles in that run. Its current open region is
the interior of this entire union, so an inactive radial seam is retained.
In particular a run with angle greater than π is left as its triangle union.

Every old current region first loses the union of all closed removal squares.
Old identifiers, remembered births and labels retain their values. Fresh
identifiers retain the new generation, the parent occurrence and the run.
Only parents whose removal half-side is at least the stopping threshold
contribute replacements and the nine child occurrences. Terminal interiors
are exceptional. For a constant exterior label, the existing constant-fan
result gives one run, hence one opposite-label square and all nine children.

The construction is conditional on an explicit current wedge assignment.
Deriving that assignment from the actual current regions, identifying its
changes with the active rays, and proving the repair induction remain
separate mathematical tasks. The definitions here assert none of these facts.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417;
`geometry:repair-induction`, lines 471–514; open actual regions and closed
birth regions, lines 558–561; and `geometry:birth-separation`, lines 584–591.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Disjoint replacement regions at one parent

Distinct connected runs at a parent give disjoint current replacement
regions. This follows from disjointness of the interiors of the normalized
whole runs, transported by the affine homeomorphism of the removal square.
The argument retains inactive seams and applies to reflex runs.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 404–417;
`geometry:repair-induction`, lines 486–514; and closed births and open
current regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## One repair step preserves disjoint current regions

Suppose the old current regions are pairwise disjoint and distinct parents
have disjoint closed removal squares. If every fresh current region lies in
its parent's removal square, the next current regions are pairwise disjoint.
The old regions lose every closed removal square, including terminal ones.
For distinct runs at one parent, the existing whole-run disjointness theorem
applies without a convexity or color restriction.

This is an auxiliary statement about the existing one-step repair operation.
Its removal-square and containment premises are supplied separately by the
metric estimates and the actual replacement construction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417;
`geometry:repair-induction`, lines 478 and 486–514; and remembered closed
births and current open regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- All four sides are divided at their midpoints, giving the eight elementary
triangles of the normalized removal square [-1, 1]².
Source: area-law Section 11, lines 404–417 and 506–514. -/
def repairFanSplit : Fin 4 → Bool :=
  fun _ ↦ true

/-- An elementary wedge of the normalized eight-triangle replacement fan.
Source: area-law Section 11, lines 404–417 and 506–514. -/
abbrev RepairFanSlot :=
  CellFanSlot repairFanSplit

/-- The exterior label of an elementary wedge is the label of the current
old identifier assigned to that wedge.
Source: area-law Section 11, lines 404–407 and 497–504. -/
def repairExteriorColor {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) :
    RepairFanSlot → Fin 2 :=
  fun s ↦ ξ (σ s)

/-- A replacement sector is a connected run of consecutive wedges whose
exterior labels agree. The fan has origin (-1, -1), scale index 1 and cell
index (0, 0), hence center zero and half-side one. Distinct connected runs
retain distinct identifiers even when their exterior labels agree.
Source: area-law Section 11, lines 404–417 and 506–514. -/
abbrev RepairFanRun {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) :=
  CellFanRun (-1, -1) 1 (0, 0) repairFanSplit (repairExteriorColor ξ σ)

/-- The exterior label descends to a connected run, since it is constant
along every equal-label edge. No wedge representative is chosen.
Source: area-law Section 11, lines 404–407 and 497–504. -/
def repairFanRunExteriorColor {ι : Type*} (ξ : ι → Fin 2)
    (σ : RepairFanSlot → ι) : RepairFanRun ξ σ → Fin 2 :=
  SimpleGraph.ConnectedComponent.lift (repairExteriorColor ξ σ) fun i j p _ ↦
    cellFanRun_color_eq (-1, -1) 1 (0, 0) repairFanSplit
      (repairExteriorColor ξ σ) i j
      (SimpleGraph.ConnectedComponent.sound p.reachable)

/-- A replacement run receives the opposite of its exterior label.
Source: area-law Section 11, lines 404–407 and 497–501. -/
def repairReplacementColor {ι : Type*} (ξ : ι → Fin 2)
    (σ : RepairFanSlot → ι) (C : RepairFanRun ξ σ) : Fin 2 :=
  1 - repairFanRunExteriorColor ξ σ C

/-- Affine transport from the normalized removal square to the square
centered at v with the computed removal half-side d(S).
Source: area-law Section 11, lines 398–409 and 506–514. -/
def repairAffineMap (v : ℝ × ℝ) (S : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun x ↦ v + repairHalfSide S • x

/-- The remembered closed birth of a replacement is the affine image of
its whole connected run of closed triangles. A reflex run is kept as this
union rather than replaced by a convex hull.
Source: area-law Section 11, lines 404–417 and 558–561. -/
def repairReplacementBirthRegion {ι : Type*} (v : ℝ × ℝ) (S : ℝ)
    (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) (C : RepairFanRun ξ σ) :
    Set (ℝ × ℝ) :=
  repairAffineMap v S ''
    cellFanRunRegion (-1, -1) 1 (0, 0) repairFanSplit (repairExteriorColor ξ σ) C

/-- The current replacement region at birth is the interior of the entire
transported closed run. Taking the interior after the triangle union retains
the inactive seams between triangles in that run.
Source: area-law Section 11, lines 404–417 and 558–561. -/
def repairReplacementOpenRegion {ι : Type*} (v : ℝ × ℝ) (S : ℝ)
    (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) (C : RepairFanRun ξ σ) :
    Set (ℝ × ℝ) :=
  interior (repairReplacementBirthRegion v S ξ σ C)

/-- A fresh replacement identifier records generation j + 1, a nonterminal
parent occurrence, and one connected run at that parent. The parent occurrence
is retained even when several parents have the same location or labels.
The equality case d(S) = S_* is nonterminal.
Source: area-law Section 11, lines 393–409 and 471–482. -/
abbrev RepairReplacementIndex {ι κ : Type*} (j : ℕ) (S : κ → ℝ) (Sstar : ℝ)
    (ξ : ι → Fin 2) (σ : κ → RepairFanSlot → ι) :=
  {n : ℕ // n = j + 1} ×
    (Σ p : {p : κ // Sstar ≤ repairHalfSide (S p)}, RepairFanRun ξ (σ p.val))

/-- The next region identifiers are the retained old identifiers and the
fresh generation-parent-run identifiers. The two alternatives are disjoint.
Source: area-law Section 11, lines 398–407 and 584–591. -/
abbrev RepairRegionIndex {ι κ : Type*} (j : ℕ) (S : κ → ℝ) (Sstar : ℝ)
    (ξ : ι → Fin 2) (σ : κ → RepairFanSlot → ι) :=
  ι ⊕ RepairReplacementIndex j S Sstar ξ σ

/-- The next remembered birth family leaves every old birth unchanged and
adjoins the transported closed run of each fresh replacement identifier.
Ancestor births may contain later births; the separation comparison concerns
current remnants after removal.
Source: area-law Section 11, lines 404–417, 558–561 and 584–591. -/
def repairNextBirthRegion {ι κ : Type*} (j : ℕ) (B : ι → Set (ℝ × ℝ))
    (v : κ → ℝ × ℝ) (S : κ → ℝ) (Sstar : ℝ) (ξ : ι → Fin 2)
    (σ : κ → RepairFanSlot → ι) :
    RepairRegionIndex j S Sstar ξ σ → Set (ℝ × ℝ)
  | .inl i => B i
  | .inr q => repairReplacementBirthRegion (v q.2.1.val) (S q.2.1.val)
      ξ (σ q.2.1.val) q.2.2

/-- The next current family first removes every parent's closed square from
each old current region and then adjoins the open replacement sectors. A
terminal parent's square is removed but it has no fresh replacement index.
Source: area-law Section 11, lines 393–409, 558–561 and 584–591. -/
def repairNextCurrentRegion {ι κ : Type*} (j : ℕ) (R : ι → Set (ℝ × ℝ))
    (v : κ → ℝ × ℝ) (S : κ → ℝ) (Sstar : ℝ) (ξ : ι → Fin 2)
    (σ : κ → RepairFanSlot → ι) :
    RepairRegionIndex j S Sstar ξ σ → Set (ℝ × ℝ)
  | .inl i => simultaneousRepairRemnants R v S i
  | .inr q => repairReplacementOpenRegion (v q.2.1.val) (S q.2.1.val)
      ξ (σ q.2.1.val) q.2.2

/-- Old identifiers keep their labels; each fresh identifier has the label
opposite to the corresponding current exterior run.
Source: area-law Section 11, lines 398–407 and 497–504. -/
def repairNextRegionColor {ι κ : Type*} (j : ℕ) (S : κ → ℝ) (Sstar : ℝ)
    (ξ : ι → Fin 2) (σ : κ → RepairFanSlot → ι) :
    RepairRegionIndex j S Sstar ξ σ → Fin 2
  | .inl i => ξ i
  | .inr q => repairReplacementColor ξ (σ q.2.1.val) q.2.2

/-- The terminal-interior contribution is the union of the interiors of all
terminal removal squares. These parents appear in the removal union, but have
neither replacement identifiers nor children. The full unassigned remainder
is a separate set. A lattice partition also requires the separate exclusion
of boundary points on the supporting lines from the lattice.
Source: area-law Section 11, lines 398–409 and 558–561. -/
def repairTerminalInteriorSet {κ : Type*} (v : κ → ℝ × ℝ) (S : κ → ℝ)
    (Sstar : ℝ) : Set (ℝ × ℝ) :=
  ⋃ p : {p : κ // repairHalfSide (S p) < Sstar}, interior (repairSquare (v p.val) (S p.val))

/-- A next-generation mark records generation j + 1 and an existing child
occurrence, hence its nonterminal parent and one of the nine centered offsets.
Ray count does not enter this index: a zero-ray nonterminal parent still
contributes all nine offsets, and a terminal parent contributes none.
Source: area-law Section 11, lines 401–409 and 506–514. -/
abbrev RepairNextMarkIndex {κ : Type*} (j : ℕ) (S : κ → ℝ) (Sstar : ℝ) :=
  {n : ℕ // n = j + 1} × RepairChildIndex S Sstar

/-- The next mark location is the existing child location, at the center,
a corner, or a side midpoint of the parent's removal square.
Source: area-law Section 11, lines 404–409 and 506–514. -/
def repairNextMarkLocation {κ : Type*} (j : ℕ) (v : κ → ℝ × ℝ) (S : κ → ℝ)
    (Sstar : ℝ) (q : RepairNextMarkIndex j S Sstar) : ℝ × ℝ :=
  repairChildLocation v S Sstar q.2

/-- The next mark scale is the existing child scale, equal to the computed
removal half-side of its parent.
Source: area-law Section 11, lines 404–409 and 506–514. -/
def repairNextMarkScale {κ : Type*} (j : ℕ) (S : κ → ℝ) (Sstar : ℝ)
    (q : RepairNextMarkIndex j S Sstar) : ℝ :=
  repairChildScale S Sstar q.2

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Distinct runs at one parent have disjoint current replacement regions.
No convexity or difference of colors is required.
Source: area-law Section 11, lines 404–417, 486–514 and 558–561. -/
theorem repairReplacementOpenRegion_pairwise_disjoint {ι : Type*}
    (v : ℝ × ℝ) (S : ℝ) (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) :
    Pairwise (fun R T : RepairFanRun ξ σ ↦
      Disjoint (repairReplacementOpenRegion v S ξ σ R)
        (repairReplacementOpenRegion v S ξ σ T)) := by
  exact fun R T hRT ↦
    let e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
      (Homeomorph.smulOfNeZero (repairHalfSide S) (repairHalfSide_pos S).ne').trans
        (Homeomorph.addLeft v)
    Eq.mp
      (congrArg₂ Disjoint
        (e.image_interior (cellFanRunRegion (-1, -1) 1 (0, 0)
          repairFanSplit (repairExteriorColor ξ σ) R))
        (e.image_interior (cellFanRunRegion (-1, -1) 1 (0, 0)
          repairFanSplit (repairExteriorColor ξ σ) T)))
      (Set.disjoint_image_of_injective e.injective
        (cellFanRunRegions_disjoint_interiors (-1, -1) 1 (0, 0)
          repairFanSplit (repairExteriorColor ξ σ) R T hRT))

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Pairwise disjoint old current regions remain pairwise disjoint after one
simultaneous repair, provided distinct parent removal squares are disjoint
and each fresh current region lies in its parent removal square.
Source: area-law Section 11, lines 393–417, 478, 486–514 and 558–561. -/
theorem repairNextCurrentRegion_pairwise_disjoint {ι κ : Type*}
    (j : ℕ) (R : ι → Set (ℝ × ℝ)) (v : κ → ℝ × ℝ) (S : κ → ℝ)
    (Sstar : ℝ) (ξ : ι → Fin 2) (σ : κ → RepairFanSlot → ι)
    (hOld : Pairwise (fun i k ↦ Disjoint (R i) (R k)))
    (hSquares : Pairwise (fun p q ↦ Disjoint (repairSquare (v p) (S p))
      (repairSquare (v q) (S q))))
    (hFresh : ∀ (p : {p : κ // Sstar ≤ repairHalfSide (S p)})
      (H : RepairFanRun ξ (σ p.val)),
      repairReplacementOpenRegion (v p.val) (S p.val) ξ (σ p.val) H ⊆
        repairSquare (v p.val) (S p.val)) :
    Pairwise (fun x y : RepairRegionIndex j S Sstar ξ σ ↦
      Disjoint (repairNextCurrentRegion j R v S Sstar ξ σ x)
        (repairNextCurrentRegion j R v S Sstar ξ σ y)) := by
  exact fun x y ↦
    match x, y with
    | .inl i, .inl k => fun hne ↦
      Set.disjoint_left.mpr fun _ hzi hzk ↦
        Set.disjoint_left.mp
          (@hOld i k (fun hik ↦ hne (congrArg Sum.inl hik))) hzi.1 hzk.1
    | .inl i, .inr q => fun _ ↦
      Set.disjoint_left.mpr fun _ hzi hzq ↦
        hzi.2 (Set.mem_iUnion.mpr
          ⟨q.2.1.val, hFresh q.2.1 q.2.2 hzq⟩)
    | .inr q, .inl i => fun _ ↦
      Set.disjoint_left.mpr fun _ hzq hzi ↦
        hzi.2 (Set.mem_iUnion.mpr
          ⟨q.2.1.val, hFresh q.2.1 q.2.2 hzq⟩)
    | .inr ⟨a, p, H⟩, .inr ⟨b, q, K⟩ => fun hne ↦
      (Classical.em (p = q)).elim
        (fun hpq ↦ by
          subst q
          apply repairReplacementOpenRegion_pairwise_disjoint
          intro hHK
          apply hne
          exact congrArg Sum.inr
            (Prod.ext (Subtype.ext (a.property.trans b.property.symm))
              (congrArg (Sigma.mk p) hHK)))
        (fun hpq ↦
          Set.disjoint_left.mpr fun _ hzH hzK ↦
            Set.disjoint_left.mp
              (@hSquares p.val q.val (fun hpqval ↦ hpq (Subtype.ext hpqval)))
              (hFresh p H hzH) (hFresh q K hzK))

end TNLean.PEPS.AreaLaw.Geometry
end

end
