/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionRealization
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Planar closed-cell domains supplied by torus covering lifts

A continuous lift of the actual torus cell union is an embedding. On every cell
it is the translation of the original unit square by the lifted integer site.
Thus its image is exactly a finite union of integer-centered closed unit squares.

**Scope restriction (auxiliary planar realization):** This identifies the genuine
geometric domain used in the block diagrams of SCP10, §6.3, local source lines
1935–1957. It neither defines a disk nor proves the complement collar-routing
statement required by the controlled disentangling argument in lines 1957–1990.
In particular, no boundary-word or group-valued flatness hypothesis is introduced.
The exterior lattice walk with prescribed torus winding remains a separate theorem.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

noncomputable section

open Set

namespace TNLean.PEPS

variable {width height : ℕ}

private abbrev CellOffsets := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)

private def regionPoint (R : Finset (TorusVertex width height)) (v : {v // v ∈ R}) :
    torusRegionRealization R :=
  ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩

private def cellPoint (R : Finset (TorusVertex width height)) (v : {v // v ∈ R})
    (d : ℝ × ℝ) (hd : d ∈ CellOffsets) : torusRegionRealization R :=
  ⟨torusVertexPoint v.1 + torusRealProjection width height d,
    mem_iUnion_of_mem v.1 (mem_iUnion_of_mem v.2 ⟨d, hd, rfl⟩)⟩

/-- A genuine covering lift translates every native closed cell to the unit
square centered at the lifted site. Source: SCP10, the realized block domains
in §6.3, lines 1935–1957; auxiliary geometric statement. -/
theorem continuousLift_torusClosedUnitCell
    (R : Finset (TorusVertex width height)) (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (v : {v // v ∈ R}) (d : ℝ × ℝ)
    (hd : d ∈ Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) :
    F ⟨torusVertexPoint v.1 + torusRealProjection width height d,
        mem_iUnion_of_mem v.1 (mem_iUnion_of_mem v.2 ⟨d, hd, rfl⟩)⟩ =
      F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩ + d := by
  have hc : Convex ℝ CellOffsets := (convex_Icc _ _).prod (convex_Icc _ _)
  have hz : (0 : ℝ × ℝ) ∈ CellOffsets := by constructor <;> constructor <;> norm_num
  let γ : unitInterval → torusRegionRealization R := fun t =>
    cellPoint R v ((t : ℝ) • d) (hc.smul_mem_of_zero_mem hz hd t.2)
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_torusRealProjection.comp
      (continuous_subtype_val.smul continuous_const))
  have h0 : torusRealProjection width height (F (γ 0)) = torusVertexPoint v.1 := by
    refine (hF (γ 0)).trans ?_
    simp [γ, cellPoint]
  have hx := eq_affine_of_addCircle_eq (width : ℝ) (fun t => (F (γ t)).1)
    (continuous_fst.comp (F.continuous.comp hγ)) d.1 (by
      intro t
      have ht := congrArg Prod.fst (hF (γ t))
      have hz := congrArg Prod.fst h0
      simp only [torusRealProjection_apply, γ, cellPoint, Prod.fst_add,
        Prod.smul_fst, smul_eq_mul] at ht hz
      exact ht.trans (congrArg (fun a => a + (((t : ℝ) * d.1 : ℝ) :
        AddCircle (width : ℝ))) hz).symm)
  have hy := eq_affine_of_addCircle_eq (height : ℝ) (fun t => (F (γ t)).2)
    (continuous_snd.comp (F.continuous.comp hγ)) d.2 (by
      intro t
      have ht := congrArg Prod.snd (hF (γ t))
      have hz := congrArg Prod.snd h0
      simp only [torusRealProjection_apply, γ, cellPoint, Prod.snd_add,
        Prod.smul_snd, smul_eq_mul] at ht hz
      exact ht.trans (congrArg (fun a => a + (((t : ℝ) * d.2 : ℝ) :
        AddCircle (height : ℝ))) hz).symm)
  have hγ0 : γ 0 = regionPoint R v := by apply Subtype.ext; simp [γ, cellPoint, regionPoint]
  have hγ1 : γ 1 = cellPoint R v d hd := by apply Subtype.ext; simp [γ, cellPoint]
  have h : F (γ 1) = F (γ 0) + d :=
    Prod.ext (by simpa using hx 1) (by simpa using hy 1)
  simpa only [hγ0, hγ1, cellPoint, regionPoint] using h

/-- The plane lift is a closed embedding of the original compact cell union. -/
theorem continuousLift_torusRegionRealization_isClosedEmbedding
    (R : Finset (TorusVertex width height)) (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1) :
    Topology.IsClosedEmbedding F := by
  let : CompactSpace (torusRegionRealization R) :=
    isCompact_iff_compactSpace.mp (isCompact_torusRegionRealization R)
  apply F.continuous.isClosedEmbedding
  intro p q hpq
  apply Subtype.ext
  rw [← hF p, ← hF q, hpq]

/-- The actual planar union of closed unit squares centered at integer region
coordinates. It introduces no graph or notion of a disk. -/
def torusRegionPlanarRealization (R : Finset (TorusVertex width height))
    (L : {v // v ∈ R} → ℤ × ℤ) : Set (ℝ × ℝ) :=
  ⋃ v : {v // v ∈ R},
    (fun d : ℝ × ℝ => (((L v).1 : ℝ), ((L v).2 : ℝ)) + d) '' CellOffsets

/-- The image of the genuine covering lift is exactly the original cells
translated to their lifted integer centers. -/
theorem range_continuousLift_torusRegionRealization
    (R : Finset (TorusVertex width height)) (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (L : {v // v ∈ R} → ℤ × ℤ)
    (hL : ∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
      F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩) :
    Set.range F = torusRegionPlanarRealization R L := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨v, hq⟩ := mem_iUnion.mp q.2
    obtain ⟨hv, hq⟩ := mem_iUnion.mp hq
    obtain ⟨d, hd, hq⟩ := hq
    have heq : cellPoint R ⟨v, hv⟩ d hd = q := Subtype.ext hq
    apply mem_iUnion_of_mem ⟨v, hv⟩
    refine ⟨d, hd, ?_⟩
    dsimp only
    rw [hL, ← heq]
    exact (continuousLift_torusClosedUnitCell R F hF ⟨v, hv⟩ d hd).symm
  · intro hp
    obtain ⟨v, d, hd, hp⟩ := mem_iUnion.mp hp
    refine ⟨cellPoint R v d hd, ?_⟩
    rw [show F (cellPoint R v d hd) = F (regionPoint R v) + d from
      continuousLift_torusClosedUnitCell R F hF v d hd,
      show F (regionPoint R v) = (((L v).1 : ℝ), ((L v).2 : ℝ)) from (hL v).symm]
    exact hp

/-- The actual torus cell union is homeomorphic to its planar lifted cell union.
The homeomorphism is induced by the genuine covering lift. -/
noncomputable def torusRegionLiftHomeomorph
    (R : Finset (TorusVertex width height)) (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (L : {v // v ∈ R} → ℤ × ℤ)
    (hL : ∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
      F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩) :
    torusRegionRealization R ≃ₜ torusRegionPlanarRealization R L :=
  (continuousLift_torusRegionRealization_isClosedEmbedding R F hF).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_continuousLift_torusRegionRealization R F hF L hL))

private theorem continuousLift_unitStep
    (R : Finset (TorusVertex width height)) (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (v w : {v // v ∈ R}) (d : ℝ × ℝ)
    (hw : torusVertexPoint w.1 = torusVertexPoint v.1 + torusRealProjection width height d)
    (hp : (1 / 2 : ℝ) • d ∈ CellOffsets) (hn : (-1 / 2 : ℝ) • d ∈ CellOffsets) :
    F (regionPoint R w) = F (regionPoint R v) + d := by
  have hd : d + (-1 / 2 : ℝ) • d = (1 / 2 : ℝ) • d := by module
  have hm : cellPoint R w ((-1 / 2 : ℝ) • d) hn =
      cellPoint R v ((1 / 2 : ℝ) • d) hp := by
    apply Subtype.ext
    change torusVertexPoint w.1 + torusRealProjection width height ((-1 / 2 : ℝ) • d) = _
    rw [hw, add_assoc, ← map_add, hd]
    rfl
  have hminus := continuousLift_torusClosedUnitCell R F hF w ((-1 / 2 : ℝ) • d) hn
  have hplus := continuousLift_torusClosedUnitCell R F hF v ((1 / 2 : ℝ) • d) hp
  change F (cellPoint R w _ hn) = F (regionPoint R w) + _ at hminus
  change F (cellPoint R v _ hp) = F (regionPoint R v) + _ at hplus
  have h : F (regionPoint R w) + (-1 / 2 : ℝ) • d =
      F (regionPoint R v) + (1 / 2 : ℝ) • d := (hminus.symm.trans (congrArg F hm)).trans hplus
  have hn' : (-1 / 2 : ℝ) • d = -((1 / 2 : ℝ) • d) := by module
  calc
    F (regionPoint R w) = (F (regionPoint R v) + (1 / 2 : ℝ) • d) + (1 / 2 : ℝ) • d :=
      sub_eq_iff_eq_add.mp (by simpa only [sub_eq_add_neg, hn'] using h)
    _ = _ := by module

private theorem integerPairStep (a b d : ℤ × ℤ)
    (h : ((a.1 : ℝ), (a.2 : ℝ)) = ((b.1 : ℝ), (b.2 : ℝ)) + ((d.1 : ℝ), (d.2 : ℝ))) :
    a = b + d :=
  Prod.ext ((Int.cast_injective (α := ℝ)) (by simpa using congrArg Prod.fst h))
    ((Int.cast_injective (α := ℝ)) (by simpa using congrArg Prod.snd h))

/-- A genuine plane lift supplies integer unit-step coordinates whose centered
closed squares are exactly its image. No exterior collar path is assumed. -/
theorem exists_integerLift_torusRegionPlanarRealization [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height)) (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L ∧
      (∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
        F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩) ∧
      Set.range F = torusRegionPlanarRealization R L := by
  classical
  have hj (v : {v // v ∈ R}) : ∃ j : ℤ × ℤ,
      ((j.1 : ℝ), (j.2 : ℝ)) = F (regionPoint R v) ∧
        ((j.1 : ZMod width), (j.2 : ZMod height)) = v.1 := by
    have hc := (hF (regionPoint R v)).trans (torusVertexPoint_eq_projection v.1)
    obtain ⟨x, hx, hxv⟩ := exists_intCast_eq_of_addCircle_eq_zmod_val width
      (F (regionPoint R v)).1 v.1.1 (congrArg Prod.fst hc)
    obtain ⟨y, hy, hyv⟩ := exists_intCast_eq_of_addCircle_eq_zmod_val height
      (F (regionPoint R v)).2 v.1.2 (congrArg Prod.snd hc)
    exact ⟨(x, y), Prod.ext hx hy, Prod.ext hxv hyv⟩
  choose L hreal hproj using hj
  refine ⟨L, ?_, hreal, range_continuousLift_torusRegionRealization R F hF L hreal⟩
  refine ⟨hproj, ?_, ?_⟩
  · intro v he
    let w : {v // v ∈ R} := ⟨(v.1.1 + 1, v.1.2), he⟩
    have hstep := continuousLift_unitStep R F hF v w (1, 0) (torusVertexPoint_right v.1)
      (by constructor <;> constructor <;> norm_num)
      (by constructor <;> constructor <;> norm_num)
    have h := (hreal w).trans
      (hstep.trans (congrArg (fun a : ℝ × ℝ => a + (1, 0)) (hreal v).symm))
    have hs := integerPairStep (L w) (L v) (1, 0) (by simpa using h)
    apply Prod.ext
    · simpa [w] using congrArg Prod.fst hs
    · simpa [w] using congrArg Prod.snd hs
  · intro v hn
    let w : {v // v ∈ R} := ⟨(v.1.1, v.1.2 + 1), hn⟩
    have hstep := continuousLift_unitStep R F hF v w (0, 1) (torusVertexPoint_up v.1)
      (by constructor <;> constructor <;> norm_num)
      (by constructor <;> constructor <;> norm_num)
    have h := (hreal w).trans
      (hstep.trans (congrArg (fun a : ℝ × ℝ => a + (0, 1)) (hreal v).symm))
    have hs := integerPairStep (L w) (L v) (0, 1) (by simpa using h)
    apply Prod.ext
    · simpa [w] using congrArg Prod.fst hs
    · simpa [w] using congrArg Prod.snd hs

end TNLean.PEPS
