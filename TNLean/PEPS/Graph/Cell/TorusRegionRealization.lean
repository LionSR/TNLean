/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff
import TNLean.PEPS.Graph.Holonomy.TorusRegionLiftGauge
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import TNLean.PEPS.Graph.Torus.TorusRectangleConnectivity
import Mathlib.Analysis.Convex.Contractible

/-!
# Local path connectedness of finite compact cell images

A finite union of continuous images of a compact locally path connected space
in a Hausdorff space is locally path connected. The finite disjoint union maps
onto the union by a closed quotient map. This supplies local path connectedness
for the closed-cell domains in SCP10, §6.3, lines 1935–1957.

It also contains the following results.

* `TNLean.PEPS.isSimplyConnected_torusRegionRealization_rectangle`: simply connected rectangular
  cell regions.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*

## Closed-cell realizations of native torus regions

A native region is realized as the finite union of closed unit squares centered
at its sites in the real torus. The unit path between two internal neighboring
sites is contained in the two corresponding cells, including at a periodic seam.
This supplies an actual geometric domain for subsequent covering-space arguments.

**Scope restriction (auxiliary geometric realization):** The closed-cell convention
makes precise the block domains drawn in SCP10, §6.3, local source lines 1935–1957.
It is an auxiliary realization, not a printed definition of a disk and not a
formalization of Theorem 6.9. Local path connectedness follows from the finite
closed-cell construction. Simply connected realizations admit continuous lifts
to the plane, and these give integer lifts preserving all internal unit steps.
Simple connectedness remains a genuine topological hypothesis; no disk predicate
or entropy assertion is introduced. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

### References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

section TorusRegionRealization

section

namespace TNLean.PEPS

/-- A finite union of compact locally path connected cell images is locally
path connected. This is the quotient argument used for the geometric block
domains of SCP10, §6.3, lines 1935–1957. -/
theorem locallyPathConnectedSpace_iUnion_range
    {ι K X : Type*} [Finite ι] [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] [TopologicalSpace X] [T2Space X]
    (f : ι → C(K, X)) : LocallyPathConnectedSpace (⋃ i, Set.range (f i)) := by
  let q : ((i : ι) × K) → (⋃ i, Set.range (f i)) := fun p =>
    ⟨f p.1 p.2, Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩⟩
  have hq : Continuous q := by
    apply continuous_sigma
    intro i
    exact (f i).continuous.subtype_mk _
  have hsurj : Function.Surjective q := by
    rintro ⟨x, hx⟩
    obtain ⟨i, k, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i, k⟩, rfl⟩
  exact (hq.isClosedMap.isQuotientMap hq hsurj).locallyPathConnectedSpace

end TNLean.PEPS

end

section

noncomputable section

open Set

namespace TNLean.PEPS

variable {width height : ℕ}

/-- The actual quotient of the real plane by the two torus periods. -/
def torusRealProjection (width height : ℕ) :
    (ℝ × ℝ) →+ (AddCircle (width : ℝ) × AddCircle (height : ℝ)) where
  toFun p := (p.1, p.2)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Coordinates of the real quotient map. -/
@[simp]
theorem torusRealProjection_apply (p : ℝ × ℝ) :
    torusRealProjection width height p =
      ((p.1 : AddCircle (width : ℝ)), (p.2 : AddCircle (height : ℝ))) := rfl

/-- The real torus projection is continuous. -/
@[continuity]
theorem continuous_torusRealProjection : Continuous (torusRealProjection width height) :=
  ((AddCircle.continuous_mk' (width : ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (height : ℝ)).comp continuous_snd)

private def coordinatePoint (n : ℕ) : ZMod n →+ AddCircle (n : ℝ) :=
  ZMod.lift n ⟨AddMonoidHom.mk' (fun j : ℤ => ((j : ℝ) : AddCircle (n : ℝ)))
    (by intro a b; simp), by simp⟩

private theorem coordinatePoint_intCast (n : ℕ) (j : ℤ) :
    coordinatePoint n (j : ZMod n) = ((j : ℝ) : AddCircle (n : ℝ)) := by
  simp [coordinatePoint]

private theorem coordinatePoint_val (n : ℕ) [NeZero n] (z : ZMod n) :
    coordinatePoint n z = ((z.val : ℝ) : AddCircle (n : ℝ)) := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    coordinatePoint_intCast n (z.val : ℤ)

/-- A native torus vertex as a point of the real torus. -/
def torusVertexPoint (v : TorusVertex width height) :
    AddCircle (width : ℝ) × AddCircle (height : ℝ) :=
  (coordinatePoint width v.1, coordinatePoint height v.2)

/-- Integer lattice centers project to their native torus site points.
This is the covering projection for the cell domains of SCP10, §6.3. -/
theorem torusVertexPoint_intCast (a : ℤ × ℤ) :
    torusVertexPoint ((a.1 : ZMod width), (a.2 : ZMod height)) =
      torusRealProjection width height ((a.1 : ℝ), (a.2 : ℝ)) :=
  Prod.ext (coordinatePoint_intCast width a.1) (coordinatePoint_intCast height a.2)

/-- Native residue coordinates give the original site center in the real torus. -/
theorem torusVertexPoint_eq_projection [NeZero width] [NeZero height]
    (v : TorusVertex width height) :
    torusVertexPoint v = torusRealProjection width height ((v.1.val : ℝ), (v.2.val : ℝ)) :=
  Prod.ext (coordinatePoint_val width v.1) (coordinatePoint_val height v.2)

/-- Rightward addition by one projects to the native neighboring vertex. -/
theorem torusVertexPoint_right (v : TorusVertex width height) :
    torusVertexPoint (v.1 + 1, v.2) =
      torusVertexPoint v + torusRealProjection width height (1, 0) := by
  apply Prod.ext
  · change coordinatePoint width (v.1 + 1) = coordinatePoint width v.1 + (1 : ℝ)
    rw [map_add]
    congr 1
    simpa using coordinatePoint_intCast width 1
  · simp [torusVertexPoint]

/-- Upward addition by one projects to the native neighboring vertex. -/
theorem torusVertexPoint_up (v : TorusVertex width height) :
    torusVertexPoint (v.1, v.2 + 1) =
      torusVertexPoint v + torusRealProjection width height (0, 1) := by
  apply Prod.ext
  · simp [torusVertexPoint]
  · change coordinatePoint height (v.2 + 1) = coordinatePoint height v.2 + (1 : ℝ)
    rw [map_add]
    congr 1
    simpa using coordinatePoint_intCast height 1

/-- The closed unit square centered at a native site, projected to the real torus. -/
def torusClosedUnitCell (v : TorusVertex width height) :
    Set (AddCircle (width : ℝ) × AddCircle (height : ℝ)) :=
  (fun d => torusVertexPoint v + torusRealProjection width height d) ''
    (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))

/-- The actual finite union of closed cells belonging to a native region. -/
def torusRegionRealization (R : Finset (TorusVertex width height)) :
    Set (AddCircle (width : ℝ) × AddCircle (height : ℝ)) :=
  ⋃ v ∈ R, torusClosedUnitCell v

/-- Every native region site lies in its closed-cell realization. -/
theorem torusVertexPoint_mem_torusRegionRealization (R : Finset (TorusVertex width height))
    (v : TorusVertex width height) (hv : v ∈ R) :
    torusVertexPoint v ∈ torusRegionRealization R := by
  apply mem_iUnion_of_mem v
  apply mem_iUnion_of_mem hv
  refine ⟨(0, 0), ?_, ?_⟩
  · norm_num
  · simp

/-- The actual native rightward unit path in the real torus. -/
def torusRightUnitPath (v : TorusVertex width height) :
    Path (torusVertexPoint v) (torusVertexPoint (v.1 + 1, v.2)) where
  toFun t := torusVertexPoint v + torusRealProjection width height ((t : ℝ), 0)
  continuous_toFun := continuous_const.add
    (continuous_torusRealProjection.comp (continuous_subtype_val.prodMk continuous_const))
  source' := by simp
  target' := by simpa using (torusVertexPoint_right v).symm

/-- The actual native upward unit path in the real torus. -/
def torusUpUnitPath (v : TorusVertex width height) :
    Path (torusVertexPoint v) (torusVertexPoint (v.1, v.2 + 1)) where
  toFun t := torusVertexPoint v + torusRealProjection width height (0, (t : ℝ))
  continuous_toFun := continuous_const.add
    (continuous_torusRealProjection.comp (continuous_const.prodMk continuous_subtype_val))
  source' := by simp
  target' := by simpa using (torusVertexPoint_up v).symm

/-- Coordinates of the native rightward path at its real parameter. -/
@[simp]
theorem torusRightUnitPath_apply (v : TorusVertex width height) (t : unitInterval) :
    torusRightUnitPath v t =
      torusVertexPoint v + torusRealProjection width height ((t : ℝ), 0) := rfl

/-- Coordinates of the native upward path at its real parameter. -/
@[simp]
theorem torusUpUnitPath_apply (v : TorusVertex width height) (t : unitInterval) :
    torusUpUnitPath v t =
      torusVertexPoint v + torusRealProjection width height (0, (t : ℝ)) := rfl

/-- Every closed native cell is compact. -/
theorem isCompact_torusClosedUnitCell (v : TorusVertex width height) :
    IsCompact (torusClosedUnitCell v) :=
  (isCompact_Icc.prod isCompact_Icc).image
    (continuous_const.add continuous_torusRealProjection)

/-- The finite union realizing a native region is compact. -/
theorem isCompact_torusRegionRealization (R : Finset (TorusVertex width height)) :
    IsCompact (torusRegionRealization R) :=
  R.isCompact_biUnion (fun v _ => isCompact_torusClosedUnitCell v)

/-- The actual closed-cell region is locally path connected. The finite
coproduct of its compact convex squares maps onto it by a closed quotient map. -/
instance torusRegionRealization_locallyPathConnectedSpace
    (R : Finset (TorusVertex width height)) :
    LocallyPathConnectedSpace (torusRegionRealization R) := by
  let S := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (isCompact_Icc.prod isCompact_Icc)
  let : LocallyPathConnectedSpace S :=
    ((convex_Icc (-1 / 2 : ℝ) (1 / 2)).prod
      (convex_Icc (-1 / 2 : ℝ) (1 / 2))).locallyPathConnectedSpace
  let f (v : {v : TorusVertex width height // v ∈ R}) :
      C(S, AddCircle (width : ℝ) × AddCircle (height : ℝ)) :=
    ⟨fun d => torusVertexPoint v.1 + torusRealProjection width height d.1,
      continuous_const.add (continuous_torusRealProjection.comp continuous_subtype_val)⟩
  have hset : (⋃ v, Set.range (f v)) = torusRegionRealization R := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, d, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_iUnion_of_mem v.1 (mem_iUnion_of_mem v.2 ⟨d.1, d.2, rfl⟩)
    · intro hx
      obtain ⟨v, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hv, d, hd, rfl⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, ⟨d, hd⟩, rfl⟩
  rw [← hset]
  exact locallyPathConnectedSpace_iUnion_range f

private theorem offsetPath_mem_cells (v w : TorusVertex width height) (d : ℝ × ℝ)
    (hdx : d.1 ∈ Icc (0 : ℝ) 1) (hdy : d.2 ∈ Icc (0 : ℝ) 1)
    (hw : torusVertexPoint w = torusVertexPoint v + torusRealProjection width height d)
    (t : unitInterval) :
    torusVertexPoint v + torusRealProjection width height ((t : ℝ) * d.1, (t : ℝ) * d.2) ∈
      torusClosedUnitCell v ∪ torusClosedUnitCell w := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · left
    refine ⟨((t : ℝ) * d.1, (t : ℝ) * d.2), ?_, rfl⟩
    constructor <;> constructor <;> nlinarith [hdx.1, hdx.2, hdy.1, hdy.2]
  · right
    refine ⟨(((t : ℝ) - 1) * d.1, ((t : ℝ) - 1) * d.2), ?_, ?_⟩
    · constructor <;> constructor <;> nlinarith [hdx.1, hdx.2, hdy.1, hdy.2]
    · have hd : d + (((t : ℝ) - 1) * d.1, ((t : ℝ) - 1) * d.2) =
          ((t : ℝ) * d.1, (t : ℝ) * d.2) := Prod.ext (by dsimp; ring) (by dsimp; ring)
      dsimp only
      rw [hw, add_assoc, ← map_add, hd]

/-- Every internal rightward unit path lies in the actual region realization,
also when its native bond crosses the horizontal seam. -/
theorem torusRightUnitPath_mem_torusRegionRealization
    (R : Finset (TorusVertex width height)) (v : TorusVertex width height)
    (hv : v ∈ R) (he : (v.1 + 1, v.2) ∈ R) (t : unitInterval) :
    torusRightUnitPath v t ∈ torusRegionRealization R := by
  have hc := offsetPath_mem_cells v (v.1 + 1, v.2) (1, 0)
    (by norm_num) (by norm_num) (torusVertexPoint_right v) t
  simp only [mul_one, mul_zero] at hc
  rcases hc with hc | hc
  · exact mem_iUnion_of_mem v (mem_iUnion_of_mem hv hc)
  · exact mem_iUnion_of_mem (v.1 + 1, v.2) (mem_iUnion_of_mem he hc)

/-- Every internal upward unit path lies in the actual region realization,
also when its native bond crosses the vertical seam. -/
theorem torusUpUnitPath_mem_torusRegionRealization
    (R : Finset (TorusVertex width height)) (v : TorusVertex width height)
    (hv : v ∈ R) (hn : (v.1, v.2 + 1) ∈ R) (t : unitInterval) :
    torusUpUnitPath v t ∈ torusRegionRealization R := by
  have hc := offsetPath_mem_cells v (v.1, v.2 + 1) (0, 1)
    (by norm_num) (by norm_num) (torusVertexPoint_up v) t
  simp only [mul_zero, mul_one] at hc
  rcases hc with hc | hc
  · exact mem_iUnion_of_mem v (mem_iUnion_of_mem hv hc)
  · exact mem_iUnion_of_mem (v.1, v.2 + 1) (mem_iUnion_of_mem hn hc)

/-- A real point above a native residue in the additive circle is an integer
with that residue. This is the arithmetic fiber identity used in the geometric
lifts of SCP10, §6.3, lines 1935–1957. -/
theorem exists_intCast_eq_of_addCircle_eq_zmod_val (n : ℕ) [NeZero n]
    (x : ℝ) (z : ZMod n)
    (hx : (x : AddCircle (n : ℝ)) = ((z.val : ℝ) : AddCircle (n : ℝ))) :
    ∃ j : ℤ, (j : ℝ) = x ∧ (j : ZMod n) = z := by
  have hz : ((x - z.val : ℝ) : AddCircle (n : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, hx]
    exact sub_self _
  obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff (n : ℝ)).mp hz
  refine ⟨a * (n : ℤ) + (z.val : ℤ), ?_, ?_⟩
  · simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, zsmul_eq_mul] at ha ⊢
    linarith
  · simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, zero_add, ZMod.natCast_zmod_val]

/-- A continuous real lift of an affine interval path in an additive circle
is the affine path with its prescribed initial point. This is covering-lift
uniqueness for the native cell and edge paths in SCP10, §6.3, lines 1935–1957. -/
theorem eq_affine_of_addCircle_eq (period : ℝ) (f : unitInterval → ℝ)
    (hf : Continuous f) (d : ℝ)
    (hproj : ∀ t, (f t : AddCircle period) =
      (f 0 : AddCircle period) + (((t : ℝ) * d : ℝ) : AddCircle period)) :
    ∀ t, f t = f 0 + (t : ℝ) * d := by
  have he : ((↑) : ℝ → AddCircle period) ∘ f =
      ((↑) : ℝ → AddCircle period) ∘ (fun t : unitInterval => f 0 + (t : ℝ) * d) := by
    funext t
    exact (hproj t).trans (AddCircle.coe_add _ _ _).symm
  have h := (AddCircle.isCoveringMap_coe period).eq_of_comp_eq hf
    (continuous_const.add (continuous_subtype_val.mul continuous_const)) he 0 (by simp)
  exact congrFun h

private theorem continuousLift_offsetPath
    (R : Finset (TorusVertex width height))
    (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (v w : TorusVertex width height) (hv : v ∈ R) (hwR : w ∈ R) (d : ℝ × ℝ)
    (hw : torusVertexPoint w = torusVertexPoint v + torusRealProjection width height d)
    (hp : ∀ t : unitInterval, torusVertexPoint v +
      torusRealProjection width height ((t : ℝ) * d.1, (t : ℝ) * d.2) ∈
        torusRegionRealization R) :
    F ⟨torusVertexPoint w, torusVertexPoint_mem_torusRegionRealization R w hwR⟩ =
      F ⟨torusVertexPoint v, torusVertexPoint_mem_torusRegionRealization R v hv⟩ + d := by
  let γ : unitInterval → torusRegionRealization R := fun t =>
    ⟨torusVertexPoint v + torusRealProjection width height
      ((t : ℝ) * d.1, (t : ℝ) * d.2), hp t⟩
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_torusRealProjection.comp
      ((continuous_subtype_val.mul continuous_const).prodMk
        (continuous_subtype_val.mul continuous_const)))
  have h0 : torusRealProjection width height (F (γ 0)) = torusVertexPoint v := by
    refine (hF (γ 0)).trans ?_
    simp only [γ, Set.Icc.coe_zero, zero_mul]
    change torusVertexPoint v + torusRealProjection width height 0 = torusVertexPoint v
    rw [map_zero, add_zero]
  have hx := eq_affine_of_addCircle_eq (width : ℝ) (fun t => (F (γ t)).1)
    (continuous_fst.comp (F.continuous.comp hγ)) d.1 (by
      intro t
      have ht := congrArg Prod.fst (hF (γ t))
      have hz := congrArg Prod.fst h0
      simp only [torusRealProjection_apply, γ, Prod.fst_add] at ht hz
      exact ht.trans (congrArg (fun a => a + (((t : ℝ) * d.1 : ℝ) :
        AddCircle (width : ℝ))) hz).symm)
  have hy := eq_affine_of_addCircle_eq (height : ℝ) (fun t => (F (γ t)).2)
    (continuous_snd.comp (F.continuous.comp hγ)) d.2 (by
      intro t
      have ht := congrArg Prod.snd (hF (γ t))
      have hz := congrArg Prod.snd h0
      simp only [torusRealProjection_apply, γ, Prod.snd_add] at ht hz
      exact ht.trans (congrArg (fun a => a + (((t : ℝ) * d.2 : ℝ) :
        AddCircle (height : ℝ))) hz).symm)
  have hv0 : γ 0 = ⟨torusVertexPoint v,
      torusVertexPoint_mem_torusRegionRealization R v hv⟩ := by
    apply Subtype.ext
    simp [γ]
  have hw1 : γ 1 = ⟨torusVertexPoint w,
      torusVertexPoint_mem_torusRegionRealization R w hwR⟩ := by
    apply Subtype.ext
    simpa [γ] using hw.symm
  have h : F (γ 1) = F (γ 0) + d :=
    Prod.ext (by simpa using hx 1) (by simpa using hy 1)
  simpa only [hv0, hw1] using h

/-- A supplied continuous lift of the actual closed-cell region gives an
integer lift of its native vertices preserving every internal unit step.
The hypotheses concern the geometric covering map, not group-valued flatness. -/
theorem exists_isTorusRegionIntegerLift_of_continuousLift [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height))
    (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L := by
  classical
  let p (v : {v // v ∈ R}) : torusRegionRealization R :=
    ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩
  have hj (v : {v // v ∈ R}) : ∃ j : ℤ × ℤ,
      ((j.1 : ℝ), (j.2 : ℝ)) = F (p v) ∧
        ((j.1 : ZMod width), (j.2 : ZMod height)) = v.1 := by
    have hc := (hF (p v)).trans (torusVertexPoint_eq_projection v.1)
    obtain ⟨x, hx, hxv⟩ := exists_intCast_eq_of_addCircle_eq_zmod_val width (F (p v)).1 v.1.1
      (congrArg Prod.fst hc)
    obtain ⟨y, hy, hyv⟩ := exists_intCast_eq_of_addCircle_eq_zmod_val height (F (p v)).2 v.1.2
      (congrArg Prod.snd hc)
    exact ⟨(x, y), Prod.ext hx hy, Prod.ext hxv hyv⟩
  choose L hreal hproj using hj
  refine ⟨L, hproj, ?_, ?_⟩
  · intro v he
    have hstep := continuousLift_offsetPath R F hF v.1 (v.1.1 + 1, v.1.2)
      v.2 he (1, 0) (torusVertexPoint_right v.1) (by
        intro t
        simpa only [mul_one, mul_zero, torusRightUnitPath_apply] using
          torusRightUnitPath_mem_torusRegionRealization R v.1 v.2 he t)
    have h : (((L ⟨(v.1.1 + 1, v.1.2), he⟩).1 : ℝ),
        ((L ⟨(v.1.1 + 1, v.1.2), he⟩).2 : ℝ)) =
          (((L v).1 : ℝ), ((L v).2 : ℝ)) + (1, 0) :=
      (hreal ⟨(v.1.1 + 1, v.1.2), he⟩).trans
        (hstep.trans (congrArg (fun a : ℝ × ℝ => a + (1, 0)) (hreal v).symm))
    apply Prod.ext
    · exact (Int.cast_injective (α := ℝ)) (by simpa using congrArg Prod.fst h)
    · exact (Int.cast_injective (α := ℝ)) (by simpa using congrArg Prod.snd h)
  · intro v hn
    have hstep := continuousLift_offsetPath R F hF v.1 (v.1.1, v.1.2 + 1)
      v.2 hn (0, 1) (torusVertexPoint_up v.1) (by
        intro t
        simpa only [mul_zero, mul_one, torusUpUnitPath_apply] using
          torusUpUnitPath_mem_torusRegionRealization R v.1 v.2 hn t)
    have h : (((L ⟨(v.1.1, v.1.2 + 1), hn⟩).1 : ℝ),
        ((L ⟨(v.1.1, v.1.2 + 1), hn⟩).2 : ℝ)) =
          (((L v).1 : ℝ), ((L v).2 : ℝ)) + (0, 1) :=
      (hreal ⟨(v.1.1, v.1.2 + 1), hn⟩).trans
        (hstep.trans (congrArg (fun a : ℝ × ℝ => a + (0, 1)) (hreal v).symm))
    apply Prod.ext
    · exact (Int.cast_injective (α := ℝ)) (by simpa using congrArg Prod.fst h)
    · exact (Int.cast_injective (α := ℝ)) (by simpa using congrArg Prod.snd h)

/-- Simple connectedness of the actual closed-cell region gives a continuous
lift to the real plane. Local path connectedness is derived from the cells,
and the two coordinates use Mathlib's additive-circle covering theorem. -/
theorem exists_continuousLift_torusRegionRealization [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height))
    (hR : IsSimplyConnected (torusRegionRealization R)) (o : {v // v ∈ R}) :
    ∃ F : C(torusRegionRealization R, ℝ × ℝ),
      ∀ p, torusRealProjection width height (F p) = p.1 := by
  let : SimplyConnectedSpace (torusRegionRealization R) := hR.simplyConnectedSpace
  let p₀ : torusRegionRealization R :=
    ⟨torusVertexPoint o.1, torusVertexPoint_mem_torusRegionRealization R o.1 o.2⟩
  let fx : C(torusRegionRealization R, AddCircle (width : ℝ)) :=
    ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩
  let fy : C(torusRegionRealization R, AddCircle (height : ℝ)) :=
    ⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩
  obtain ⟨Fx, hFx, _⟩ := (AddCircle.isCoveringMap_coe (width : ℝ)).existsUnique_continuousMap_lifts
    fx p₀ (o.1.1.val : ℝ) (coordinatePoint_val width o.1.1).symm
  obtain ⟨Fy, hFy, _⟩ := (AddCircle.isCoveringMap_coe (height : ℝ)).existsUnique_continuousMap_lifts
    fy p₀ (o.1.2.val : ℝ) (coordinatePoint_val height o.1.2).symm
  refine ⟨⟨fun p => (Fx p, Fy p), Fx.continuous.prodMk Fy.continuous⟩, ?_⟩
  intro p
  exact Prod.ext (congrFun hFx.2 p) (congrFun hFy.2 p)

/-- The actual simply connected closed-cell realization supplies the integer
coordinate lift used by the native closure gauge. This is a topological
auxiliary theorem, not a definition of a disk or an entropy assertion. -/
theorem exists_isTorusRegionIntegerLift_of_isSimplyConnected [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height))
    (hR : IsSimplyConnected (torusRegionRealization R)) (o : {v // v ∈ R}) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L := by
  obtain ⟨F, hF⟩ := exists_continuousLift_torusRegionRealization R hR o
  exact exists_isTorusRegionIntegerLift_of_continuousLift R F hF

end TNLean.PEPS
end

end

end TorusRegionRealization

section TorusRectangleRealization

/-!
## Simply connected rectangular cell regions

A nonwrapping rectangle of native torus sites has a closed-cell realization
homeomorphic to the corresponding closed planar rectangle, provided that each
side length is strictly smaller than its torus period. Convexity then gives
simple connectedness of the actual realization.

This is locally proved auxiliary geometry, motivated by the reduction to
horizontal and vertical stripes in SCP10, Theorem 6.7 (arXiv:1001.3807, local
source lines 1995–2011); the source states no rectangle realization. It asserts
neither a physical disentangling identity nor a parent-Hamiltonian statement.

### References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Set
noncomputable section
namespace TNLean.PEPS

private theorem exists_integer_center_in_interval (a b : ℤ) (hab : a ≤ b) (x : ℝ)
    (hx : (a : ℝ) - 1 / 2 ≤ x ∧ x ≤ (b : ℝ) + 1 / 2) :
    ∃ i : ℤ, a ≤ i ∧ i ≤ b ∧ |x - (i : ℝ)| ≤ 1 / 2 := by
  let i : ℤ := min ⌊x + 1 / 2⌋ b
  have haf : a ≤ ⌊x + 1 / 2⌋ := Int.le_floor.mpr (by linarith [hx.1])
  have hai : a ≤ i := le_min haf hab
  have hib : i ≤ b := min_le_right _ _
  have hf : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hf' : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨i, hai, hib, ?_⟩
  dsimp [i]
  rw [Int.cast_min, abs_le]
  constructor
  · have hm : min (⌊x + 1 / 2⌋ : ℝ) (b : ℝ) ≤ (⌊x + 1 / 2⌋ : ℝ) := min_le_left _ _
    linarith
  · rcases le_total ⌊x + 1 / 2⌋ b with h | h
    · rw [min_eq_left (by exact_mod_cast h)]
      linarith
    · rw [min_eq_right (by exact_mod_cast h)]
      linarith [hx.2]

private def planarRectangle (xStart yStart xLen yLen : ℕ) : Set (ℝ × ℝ) :=
  Icc ((xStart : ℝ) - 1 / 2) ((xStart + xLen : ℕ) - 1 / 2 : ℝ) ×ˢ
    Icc ((yStart : ℝ) - 1 / 2) ((yStart + yLen : ℕ) - 1 / 2 : ℝ)

private theorem projection_planarRectangle_eq
    {width height : ℕ} [NeZero width] [NeZero height]
    (xStart yStart xLen yLen : ℕ) (hx : 0 < xLen) (hy : 0 < yLen)
    (hxb : xStart + xLen ≤ width) (hyb : yStart + yLen ≤ height) :
    torusRealProjection width height '' planarRectangle xStart yStart xLen yLen =
      torusRegionRealization
        (torusContiguousRectangle (width := width) (height := height)
          xStart yStart xLen yLen) := by
  ext z
  unfold torusRegionRealization
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hxInt : (xStart : ℤ) ≤ (xStart + xLen : ℕ) - 1 := by omega
    have hyInt : (yStart : ℤ) ≤ (yStart + yLen : ℕ) - 1 := by omega
    obtain ⟨i, hi₁, hi₂, hip⟩ := exists_integer_center_in_interval
      (xStart : ℤ) ((xStart + xLen : ℕ) - 1) hxInt p.1 (by
        have hlo := hp.1.1
        have hhi := hp.1.2
        push_cast at hlo hhi ⊢
        constructor <;> linarith)
    obtain ⟨j, hj₁, hj₂, hjp⟩ := exists_integer_center_in_interval
      (yStart : ℤ) ((yStart + yLen : ℕ) - 1) hyInt p.2 (by
        have hlo := hp.2.1
        have hhi := hp.2.2
        push_cast at hlo hhi ⊢
        constructor <;> linarith)
    have hi₀ : 0 ≤ i := le_trans (by omega) hi₁
    have hj₀ : 0 ≤ j := le_trans (by omega) hj₁
    have hiw : i < (width : ℤ) := by omega
    have hjh : j < (height : ℤ) := by omega
    have hiv : (((i : ZMod width).val : ℕ) : ℤ) = i := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hi₀ hiw]
    have hjv : (((j : ZMod height).val : ℕ) : ℤ) = j := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hj₀ hjh]
    let v : TorusVertex width height := ((i : ZMod width), (j : ZMod height))
    have hv : v ∈ torusContiguousRectangle xStart yStart xLen yLen := by
      rw [mem_torusContiguousRectangle]
      change xStart ≤ (i : ZMod width).val ∧ (i : ZMod width).val < xStart + xLen ∧
        yStart ≤ (j : ZMod height).val ∧ (j : ZMod height).val < yStart + yLen
      omega
    apply mem_iUnion_of_mem v
    apply mem_iUnion_of_mem hv
    refine ⟨p - ((i : ℝ), (j : ℝ)), ?_, ?_⟩
    · simpa only [Prod.fst_sub, Prod.snd_sub, mem_prod, mem_Icc, ← abs_le, neg_div]
        using And.intro hip hjp
    · change torusVertexPoint v + torusRealProjection width height
        (p - ((i : ℝ), (j : ℝ))) = torusRealProjection width height p
      rw [show torusVertexPoint v = torusRealProjection width height ((i : ℝ), (j : ℝ))
        from torusVertexPoint_intCast (i, j), ← map_add, add_sub_cancel]
  · intro hz
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨v, hv, d, hd, rfl⟩ := hz
    have hv' := (mem_torusContiguousRectangle xStart yStart xLen yLen v).mp hv
    have hx₁ : (xStart : ℝ) ≤ (v.1.val : ℝ) := by exact_mod_cast hv'.1
    have hx₂ : (v.1.val : ℝ) + 1 ≤ (xStart + xLen : ℕ) := by
      exact_mod_cast hv'.2.1
    have hy₁ : (yStart : ℝ) ≤ (v.2.val : ℝ) := by exact_mod_cast hv'.2.2.1
    have hy₂ : (v.2.val : ℝ) + 1 ≤ (yStart + yLen : ℕ) := by
      exact_mod_cast hv'.2.2.2
    refine ⟨((v.1.val : ℝ), (v.2.val : ℝ)) + d, ?_, ?_⟩
    · dsimp [planarRectangle]
      obtain ⟨⟨hd₁, hd₂⟩, ⟨hd₃, hd₄⟩⟩ := hd
      constructor <;> constructor <;> dsimp <;> linarith
    · rw [map_add, ← torusVertexPoint_eq_projection]

private theorem addCircle_injOn_short_interval (P a b : ℝ) (hP : 0 < P)
    (hb : b < a + P) : Set.InjOn (fun x : ℝ => (x : AddCircle P)) (Icc a b) := by
  let : Fact (0 < P) := ⟨hP⟩
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico a (a + P) from ⟨hx.1, hx.2.trans_lt hb⟩)
    (show y ∈ Ico a (a + P) from ⟨hy.1, hy.2.trans_lt hb⟩)).mp hxy

private theorem projection_planarRectangle_injOn
    {width height : ℕ} [NeZero width] [NeZero height]
    (xStart yStart xLen yLen : ℕ) (hx : xLen < width) (hy : yLen < height) :
    Set.InjOn (torusRealProjection width height) (planarRectangle xStart yStart xLen yLen) := by
  have hxp : (0 : ℝ) < width := Nat.cast_pos.mpr (NeZero.pos width)
  have hyp : (0 : ℝ) < height := Nat.cast_pos.mpr (NeZero.pos height)
  have hxl : (xLen : ℝ) < width := by exact_mod_cast hx
  have hyl : (yLen : ℝ) < height := by exact_mod_cast hy
  intro p hp q hq he
  apply Prod.ext
  · exact addCircle_injOn_short_interval (width : ℝ) ((xStart : ℝ) - 1 / 2)
      ((xStart + xLen : ℕ) - 1 / 2 : ℝ) hxp (by push_cast; linarith)
      hp.1 hq.1 (congrArg Prod.fst he)
  · exact addCircle_injOn_short_interval (height : ℝ) ((yStart : ℝ) - 1 / 2)
      ((yStart + yLen : ℕ) - 1 / 2 : ℝ) hyp (by push_cast; linarith)
      hp.2 hq.2 (congrArg Prod.snd he)

/-- The actual closed-cell realization of a positive nonwrapping rectangle
with both side lengths shorter than the torus periods is simply connected.
This is locally proved auxiliary geometry: SCP10, Theorem 6.7, lines 1995–2011,
uses two wrapping stripes and states no rectangle realization. -/
theorem isSimplyConnected_torusRegionRealization_rectangle
    {width height : ℕ} [NeZero width] [NeZero height]
    (xStart yStart xLen yLen : ℕ) (hx : 0 < xLen) (hy : 0 < yLen)
    (hxl : xLen < width) (hyl : yLen < height)
    (hxb : xStart + xLen ≤ width) (hyb : yStart + yLen ≤ height) :
    IsSimplyConnected (torusRegionRealization
      (torusContiguousRectangle (width := width) (height := height)
        xStart yStart xLen yLen)) := by
  let S := planarRectangle xStart yStart xLen yLen
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Convex ℝ S := (convex_Icc _ _).prod (convex_Icc _ _)
  have hn : S.Nonempty := by
    have hxr : (1 : ℝ) ≤ xLen := by exact_mod_cast hx
    have hyr : (1 : ℝ) ≤ yLen := by exact_mod_cast hy
    refine ⟨((xStart : ℝ), (yStart : ℝ)), ?_⟩
    dsimp [S, planarRectangle]
    push_cast
    constructor <;> constructor <;> linarith
  let : ContractibleSpace S := hc.contractibleSpace hn
  let f : S → AddCircle (width : ℝ) × AddCircle (height : ℝ) :=
    fun p => torusRealProjection width height p.1
  have hcont : Continuous f := continuous_torusRealProjection.comp continuous_subtype_val
  have hinj : Function.Injective f := by
    intro p q he
    exact Subtype.ext (projection_planarRectangle_injOn
      xStart yStart xLen yLen hxl hyl p.2 q.2 he)
  have hemb := hcont.isClosedEmbedding hinj
  have hSC : IsSimplyConnected (Set.range f) :=
    hemb.isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  have hrange : Set.range f = torusRegionRealization
      (torusContiguousRectangle (width := width) (height := height)
        xStart yStart xLen yLen) := by
    rw [← projection_planarRectangle_eq xStart yStart xLen yLen hx hy hxb hyb]
    exact Set.range_domRestrict _ _
  rwa [hrange] at hSC

end TNLean.PEPS

end

end TorusRectangleRealization
