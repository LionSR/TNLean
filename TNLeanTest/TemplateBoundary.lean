import TNLean.PEPS.AreaLaw.Geometry.TemplateBoundary
import Mathlib.Data.Rat.Floor

/-!
# Ambient template boundary regressions

Checks unordered crossing edges, exclusion of diagonal and internal edges,
and the zero and maximal permitted radii of a complete actual Template.
The private thin-real-polygon fixture is preserved from the original regression
at TNLean commit 06cfc12e5ce3bc1c7e16553af44ded6da1e71223.
-/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

example : ambientBoundary ∅ = ∅ := ambientBoundary_empty

example : s((0, 0), (1, 0)) ∈ ambientBoundary {(0, 0)} := by
  exact mem_ambientBoundary_iff.mpr
    ⟨(0, 0), by simp, (1, 0), by simp, by decide, rfl⟩

example : s((1, 0), (0, 0)) ∈ ambientBoundary {(0, 0)} := by
  exact mem_ambientBoundary_iff.mpr
    ⟨(0, 0), by simp, (1, 0), by simp, by decide, Sym2.eq_swap⟩

example : s((-2, -3), (-2, -4)) ∈ ambientBoundary {(-2, -3)} := by
  exact mem_ambientBoundary_iff.mpr
    ⟨(-2, -3), by simp, (-2, -4), by simp, by decide, rfl⟩

-- Sup-norm dilation contains diagonal sites, but boundary edges are nearest-neighbor edges.
example : s((0, 0), (1, 1)) ∉ ambientBoundary {(0, 0)} := by
  intro he
  obtain ⟨p, _, q, _, hpq, he⟩ := mem_ambientBoundary_iff.mp he
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [latticeNeighbors] at hpq

example : s((0, 0), (1, 0)) ∉ ambientBoundary {(0, 0), (1, 0)} := by
  intro he
  obtain ⟨p, _, q, hq, _, he⟩ := mem_ambientBoundary_iff.mp he
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at hq

private theorem singleton_boundary : ambientBoundary {(0, 0)} =
    {s((0, 0), (1, 0)), s((0, 0), (-1, 0)),
      s((0, 0), (0, 1)), s((0, 0), (0, -1))} := by
  ext e
  constructor
  · intro he
    obtain ⟨p, hp, q, _, hpq, rfl⟩ := mem_ambientBoundary_iff.mp he
    have hp' : p = (0, 0) := Finset.mem_singleton.mp hp
    subst p
    simp only [latticeNeighbors, Finset.mem_insert, Finset.mem_singleton] at hpq
    rcases hpq with rfl | rfl | rfl | rfl <;> norm_num
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      apply mem_ambientBoundary_iff.mpr
    · exact ⟨(0, 0), by simp, (1, 0), by simp, by decide, rfl⟩
    · exact ⟨(0, 0), by simp, (-1, 0), by simp, by decide, rfl⟩
    · exact ⟨(0, 0), by simp, (0, 1), by simp, by decide, rfl⟩
    · exact ⟨(0, 0), by simp, (0, -1), by simp, by decide, rfl⟩

-- Four unordered edges, rather than eight directed incidences.
example : (ambientBoundary {(0, 0)}).card = 4 := by
  rw [singleton_boundary]
  decide

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


example : (ambientBoundary thinDiagonalTemplate.points).card ≤ 4 * 96 := by
  simpa only [ambientDilation_zero] using
    template_boundary_card_le thinDiagonalTemplate (by norm_num) 0 (by omega)

example : (ambientBoundary (ambientDilation thinDiagonalTemplate.points 3)).card ≤ 4 * 96 :=
  template_boundary_card_le thinDiagonalTemplate (by norm_num) 3 (by omega)

example (j : ℕ) (hj : j ≤ 3) :
    (ambientBoundary (ambientDilation thinDiagonalTemplate.points j \
      thinDiagonalTemplate.points)).card ≤ 8 * 96 :=
  template_shell_boundary_card_le thinDiagonalTemplate (by norm_num) j hj

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.latticeNeighbors'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeNeighbors
/--
info: 'TNLean.PEPS.AreaLaw.mem_latticeNeighbors_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.mem_latticeNeighbors_iff
/--
info: 'TNLean.PEPS.AreaLaw.latticeNeighbors_symm'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeNeighbors_symm
/--
info: 'TNLean.PEPS.AreaLaw.card_latticeNeighbors_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_latticeNeighbors_le
/--
info: 'TNLean.PEPS.AreaLaw.neighbor_mem_ambientDilation_succ'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.neighbor_mem_ambientDilation_succ
/--
info: 'TNLean.PEPS.AreaLaw.ambientBoundaryRegion'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientBoundaryRegion
/--
info: 'TNLean.PEPS.AreaLaw.ambientBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientBoundary
/--
info: 'TNLean.PEPS.AreaLaw.card_ambientBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_ambientBoundary
/--
info: 'TNLean.PEPS.AreaLaw.mem_ambientBoundary_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.mem_ambientBoundary_iff
/--
info: 'TNLean.PEPS.AreaLaw.ambientBoundary_orientation_unique'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientBoundary_orientation_unique
/--
info: 'TNLean.PEPS.AreaLaw.ambientBoundary_empty'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientBoundary_empty
/--
info: 'TNLean.PEPS.AreaLaw.card_ambientBoundary_le_of_endpoint_cover'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_ambientBoundary_le_of_endpoint_cover
/--
info: 'TNLean.PEPS.AreaLaw.card_ambientBoundary_le_outer_layer'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_ambientBoundary_le_outer_layer
/--
info: 'TNLean.PEPS.AreaLaw.card_ambientBoundary_dilation_le_layer'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_ambientBoundary_dilation_le_layer
/--
info: 'TNLean.PEPS.AreaLaw.ambientBoundary_sdiff_subset'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.ambientBoundary_sdiff_subset
/--
info: 'TNLean.PEPS.AreaLaw.card_ambientBoundary_sdiff_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_ambientBoundary_sdiff_le
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_boundary_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_boundary_card_le
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_shell_boundary_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_shell_boundary_card_le

end AxiomChecks
