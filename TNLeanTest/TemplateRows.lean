import TNLean.PEPS.AreaLaw.Geometry.TemplateLayers
import Mathlib.Data.Rat.Floor

/-!
# Template row regression checks

These examples check signed rounding, empty dilation, thin diagonal samples,
disconnected rows, overlapping unions, and the actual template interface.
The audit records the proof dependencies of every new export.
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

/-- A real thin rectangle with two diagonal side directions. -/
private noncomputable def thinDiagonalPolygon : TemplatePolygon :=
  .rectangle (-1, -1) (2, 2) (1 / 4, -1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [IsAllowedSlope]) (by norm_num [IsAllowedSlope])

/-- The claimed sample is proved exact below, rather than supplied as an assumption. -/
private def thinDiagonalSample : Finset (ℤ × ℤ) := {(-1, -1), (0, 0), (1, 1)}

private theorem thinDiagonal_bounds {p : ℝ × ℝ} (hp : p ∈ thinDiagonalPolygon.region) :
    (-1 ≤ p.1 ∧ p.1 ≤ 5 / 4) ∧ (-5 / 4 ≤ p.2 ∧ p.2 ≤ 1) ∧
      0 ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 1 / 2 := by
  let d : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ
  let B : Set (ℝ × ℝ) := (Set.Icc (-1 : ℝ) (5 / 4) ×ˢ Set.Icc (-5 / 4) 1) ∩
    d ⁻¹' Set.Icc 0 (1 / 2)
  have hB : Convex ℝ B :=
    ((convex_Icc _ _).prod (convex_Icc _ _)).inter
      ((convex_Icc _ _).linear_preimage d)
  have hPB : thinDiagonalPolygon.region ⊆ B := by
    apply convexHull_min _ hB
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      norm_num [B, d, Set.mem_Icc]
  have h := hPB hp
  change ((-1 ≤ p.1 ∧ p.1 ≤ 5 / 4) ∧ (-5 / 4 ≤ p.2 ∧ p.2 ≤ 1)) ∧
    (0 ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 1 / 2) at h
  tauto

private theorem thinDiagonal_sample_iff (p : ℤ × ℤ) :
    p ∈ thinDiagonalSample ↔ integerPoint p ∈ thinDiagonalPolygon.region := by
  have ha : (-1, -1) ∈ thinDiagonalPolygon.region :=
    subset_convexHull ℝ _ (by simp)
  have hb : (1, 1) ∈ thinDiagonalPolygon.region :=
    subset_convexHull ℝ _ (by norm_num)
  have hz : (0, 0) ∈ thinDiagonalPolygon.region := by
    have h := thinDiagonalPolygon.convex_region ha hb
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
    convert h using 1
    ext <;> norm_num
  constructor
  · intro h
    simp only [thinDiagonalSample, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · simpa [integerPoint] using ha
    · simpa [integerPoint] using hz
    · simpa [integerPoint] using hb
  · intro h
    rcases p with ⟨x, y⟩
    obtain ⟨⟨hx₀, hx₁⟩, _, hxy₀, hxy₁⟩ := thinDiagonal_bounds h
    change -1 ≤ (x : ℝ) at hx₀
    change (x : ℝ) ≤ 5 / 4 at hx₁
    change 0 ≤ (x : ℝ) - y at hxy₀
    change (x : ℝ) - y ≤ 1 / 2 at hxy₁
    have hx₀' : -1 ≤ x := by exact_mod_cast hx₀
    have hx₁' : 4 * x ≤ 5 := by
      exact_mod_cast (show 4 * (x : ℝ) ≤ 5 by linarith)
    have hxy₀' : 0 ≤ x - y := by exact_mod_cast hxy₀
    have hxy₁' : 2 * (x - y) ≤ 1 := by
      exact_mod_cast (show 2 * ((x : ℝ) - y) ≤ 1 by linarith)
    have hxy : x = y := by omega
    subst y
    have hx : x = -1 ∨ x = 0 ∨ x = 1 := by omega
    rcases hx with rfl | rfl | rfl <;> simp [thinDiagonalSample]

/-- A complete instance of the published model, with a thin real polygon and
its exact three-site diagonal sample. -/
private noncomputable def thinDiagonalTemplate : Template 24 96 3 where
  n_pos := by decide
  s₀_pos := by decide
  pieceCount := 1
  pieceCount_pos := by decide
  polygon _ := thinDiagonalPolygon
  sample _ := thinDiagonalSample
  mem_sample _ := thinDiagonal_sample_iff
  piece_diameter _ x hx y hy := by
    obtain ⟨⟨hx₀, hx₁⟩, ⟨hx₂, hx₃⟩, _⟩ := thinDiagonal_bounds hx
    obtain ⟨⟨hy₀, hy₁⟩, ⟨hy₂, hy₃⟩, _⟩ := thinDiagonal_bounds hy
    change max |x.1 - y.1| |x.2 - y.2| ≤ (3 : ℝ)
    simp only [max_le_iff, abs_le]
    constructor <;> constructor <;> linarith
  points := thinDiagonalSample
  nonempty := ⟨(0, 0), by simp [thinDiagonalSample]⟩
  cover := by simp
  scale := by norm_num
  diameter x hx y hy := by
    simp only [thinDiagonalSample, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> norm_num

-- Thin diagonals need ambient, rather than induced-domain, dilation.
example : (0, 1) ∈ ambientDilation thinDiagonalTemplate.points 1 := by
  change (0, 1) ∈ ambientDilation thinDiagonalSample 1
  decide

example : latticeRow
    (thinDiagonalTemplate.sample ⟨0, thinDiagonalTemplate.pieceCount_pos⟩) 0 = {0} := by
  change latticeRow thinDiagonalSample 0 = {0}
  decide

example : thinDiagonalTemplate.points.card ≤ 9 * 96 * 3 :=
  template_card_le thinDiagonalTemplate (by norm_num)

example (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ 3) :
    (ambientDilation thinDiagonalTemplate.points j \
      ambientDilation thinDiagonalTemplate.points (j - 1)).card ≤ 96 :=
  template_layer_card_le thinDiagonalTemplate (by norm_num) j hj hjs

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

-- Record the new constructor and endpoint proofs before guarding their exact output.
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.vertices
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.region_eq_convexHull_vertices
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.mem_region_iff_normal_bounds
#print axioms TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.exists_four_strip_bounds
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.exists_sample_four_strip_bounds
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.exists_latticeRow_profile
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_nonempty_between
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_min_step
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_max_step

#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.exists_sample_in_window_between
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.exists_nearby_sample_in_row

#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.mem_latticeRow_dilation_of_between
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_dilation_eq_Icc
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_dilation_succ_bounds
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.card_latticeRow_layer_le_four
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.card_latticeRow_dilation_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.exists_dilation_row_domain
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.card_dilation_layer_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_layer_card_le

end AxiomChecks
