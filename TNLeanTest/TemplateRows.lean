import TNLean.PEPS.AreaLaw.Geometry.TemplateRows
import Mathlib.Data.Rat.Floor

/-!
# Template row regression checks

These examples check signed rounding, empty dilation, thin diagonal samples,
disconnected rows, overlapping unions, and the actual template interface.
The guarded audit records the permitted dependencies of every new export.
-/

open scoped BigOperators

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

-- Negative coordinates and diagonal integer shifts must not use natural rounding.
example : ⌈(-3 / 2 : ℝ) + ((-1 : ℤ) : ℝ) * (-4 : ℤ)⌉ = 3 := by
  rw [ceil_affine_row (-3 / 2) (-1) (-4)]
  norm_num

example : ⌊(-3 / 2 : ℝ) + ((1 : ℤ) : ℝ) * (-4 : ℤ)⌋ = -6 := by
  rw [floor_affine_row (-3 / 2) 1 (-4)]
  norm_num

-- Empty pieces remain empty under every ambient dilation.
example (r : ℕ) : ambientDilation ∅ r = ∅ := by
  simp [ambientDilation]

-- Thin diagonals need ambient, rather than induced-domain, dilation.
example : (0, 1) ∈ ambientDilation {(-1, -1), (0, 0), (1, 1)} 1 := by
  decide

-- A disconnected union may have a disconnected horizontal row.
example : latticeRow {(-3, 0), (3, 0)} 0 = {-3, 3} := by decide
example : (0 : ℤ) ∉ latticeRow {(-3, 0), (3, 0)} 0 := by decide

-- The reduction permits repeated, overlapping pieces and empty pieces.
example (S : Finset (ℤ × ℤ)) (r t : ℕ) :
    (ambientDilation (({0, 1, 2} : Finset ℕ).biUnion
      (fun i ↦ if i = 2 then ∅ else S)) r \
      ambientDilation (({0, 1, 2} : Finset ℕ).biUnion
        (fun i ↦ if i = 2 then ∅ else S)) t).card ≤
      ∑ i ∈ ({0, 1, 2} : Finset ℕ),
        (ambientDilation (if i = 2 then ∅ else S) r \
          ambientDilation (if i = 2 then ∅ else S) t).card :=
  card_ambientDilation_biUnion_sdiff_le _ _ _ _

-- These theorems consume the published model without row-regularity fields.
example {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀) (i : Fin T.pieceCount)
    {a b x y : ℤ} (ha : (a, y) ∈ T.sample i) (hb : (b, y) ∈ T.sample i)
    (hax : a ≤ x) (hxb : x ≤ b) : (x, y) ∈ T.sample i :=
  T.mem_sample_of_row_between i ha hb hax hxb

example {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀) (hC : 1 ≤ Ctpl) :
    T.points.card ≤ 9 * n * s₀ := template_card_le T hC

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.mem_ambientDilation_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.mem_ambientDilation_iff

/--
info: 'TNLean.PEPS.AreaLaw.ambientDilation_mono'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientDilation_mono

/--
info: 'TNLean.PEPS.AreaLaw.ambientDilation_mono_radius'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientDilation_mono_radius

/--
info: 'TNLean.PEPS.AreaLaw.ambientDilation_biUnion_sdiff_subset'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientDilation_biUnion_sdiff_subset

/--
info: 'TNLean.PEPS.AreaLaw.card_ambientDilation_biUnion_sdiff_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_ambientDilation_biUnion_sdiff_le

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.latticeRow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.latticeRow

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.mem_latticeRow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.mem_latticeRow

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.convex_region'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.convex_region

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.isCompact_region'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.isCompact_region

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.horizontal_mem_of_mem_of_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.horizontal_mem_of_mem_of_le

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.isCompact_horizontalSection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.isCompact_horizontalSection

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.horizontalSection_eq_Icc'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.horizontalSection_eq_Icc

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_eq_Icc_ceil_floor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_eq_Icc_ceil_floor

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.mem_sample_of_row_between'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.mem_sample_of_row_between

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_eq_Icc'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_eq_Icc

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.sample_subset_box'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.sample_subset_box

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.card_sample_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.card_sample_le

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_card_le

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.ceil_affine_row'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.ceil_affine_row

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.floor_affine_row'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.floor_affine_row

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.mem_latticeRow_ambientDilation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.mem_latticeRow_ambientDilation

/--
info: 'TNLean.PEPS.AreaLaw.ambientDilation_add'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientDilation_add

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.mem_latticeRow_dilation_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.mem_latticeRow_dilation_iff

end AxiomChecks
