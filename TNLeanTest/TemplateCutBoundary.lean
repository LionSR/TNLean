import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary
import TNLean.PEPS.AreaLaw.Geometry.TemplateClearance
import TNLean.PEPS.AreaLaw.Geometry.TemplateSafeRectangles
import Mathlib.Data.Rat.Floor

/-!
Physical-cut regressions. The complete thin-polygon fixture is preserved from
TNLean commit acb16ed1bb9b15ca95e3487aa093b29124cd00b9, not upstream OpenAI code.
-/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

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


-- Nonempty endpoint set, maximal permitted dilation, and negative template coordinates.
private theorem separated : thinDiagonalTemplate.IsSeparated 1 {(20, 0), (21, 0)} := by
  intro p hp z hz
  simp only [thinDiagonalTemplate, thinDiagonalSample, Finset.mem_insert,
    Finset.mem_singleton] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hp with rfl | rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num

example : Disjoint (ambientDilation thinDiagonalTemplate.points 3) {(20, 0), (21, 0)} :=
  separated.disjoint_ambientDilation (by norm_num) 3 (by omega)

-- No extra avoidance hypothesis is required in either final physical theorem.
example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (h : thinDiagonalTemplate.IsSeparated 1 (boundaryEndpoints Λ A)) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ thinDiagonalTemplate.points)).card ≤ 384 := by
  exact template_core_boundary_card_le thinDiagonalTemplate (by norm_num) Λ A h (by norm_num)

example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (h : thinDiagonalTemplate.IsSeparated 1 (boundaryEndpoints Λ A)) :
    (edgeBoundary Λ (A.filter fun x ↦
      x.1 ∈ ambientDilation thinDiagonalTemplate.points 3)).card ≤ 384 := by
  exact template_cut_boundary_card_le thinDiagonalTemplate (by norm_num) Λ A h
    (by norm_num) 3 (by omega)

example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (h : thinDiagonalTemplate.IsSeparated 1 (boundaryEndpoints Λ A)) :
    (edgeBoundary Λ (A.filter fun x ↦
      x.1 ∈ ambientDilation thinDiagonalTemplate.points 3 \ thinDiagonalTemplate.points)).card ≤
        768 := by
  exact template_shell_cut_boundary_card_le thinDiagonalTemplate (by norm_num) Λ A h
    (by norm_num) 3 (by omega)

-- Empty cuts, full cuts, and empty ambient restrictions.
example (Λ : Finset (ℤ × ℤ)) : boundaryEndpoints Λ ∅ = ∅ := by
  simp [boundaryEndpoints]

example (Λ : Finset (ℤ × ℤ)) : boundaryEndpoints Λ Finset.univ = ∅ := by
  unfold boundaryEndpoints
  rw [edgeBoundary_univ]
  simp

example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ (∅ : Finset (ℤ × ℤ)))).card = 0 := by
  simp

-- An actual physical edge survives the unordered injection in both orientations.
private def pairDomain : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}
private def leftSite : Site pairDomain := ⟨(0, 0), by simp [pairDomain]⟩
private def rightSite : Site pairDomain := ⟨(1, 0), by simp [pairDomain]⟩

private theorem pair_crossing :
    s(leftSite, rightSite) ∈ edgeBoundary pairDomain {leftSite} := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · apply SimpleGraph.mem_edgeFinset.mpr
    change (domainGraph pairDomain).Adj leftSite rightSite
    decide
  · exact ⟨leftSite, by simp, rightSite, by decide, rfl⟩

example : (0, 0) ∈ boundaryEndpoints pairDomain {leftSite} :=
  mem_boundaryEndpoints_of_mem_edgeBoundary (x := leftSite) pair_crossing (by simp)

example : (1, 0) ∈ boundaryEndpoints pairDomain {leftSite} :=
  mem_boundaryEndpoints_of_mem_edgeBoundary (x := rightSite) pair_crossing (by simp)

example : ¬ Disjoint {(0, 0)} (boundaryEndpoints pairDomain {leftSite}) := by
  intro h
  exact Finset.disjoint_left.mp h (by simp [leftSite])
    (mem_boundaryEndpoints_of_mem_edgeBoundary (x := leftSite) pair_crossing (by simp))

example : s((1, 0), (0, 0)) ∈ ambientBoundary {(0, 0)} := by
  apply mem_ambientBoundary_iff.mpr
  exact ⟨(0, 0), by simp, (1, 0), by simp, by decide, Sym2.eq_swap⟩

-- A missing neighbor is ambient but cannot contribute to the physical cut.
example : (edgeBoundary {(0, 0)} Finset.univ).card = 0 := by
  simp only [edgeBoundary_univ, Finset.card_empty]

-- Disconnected domains and holes are permitted, including a nonempty ambient
-- restriction whose physical cut has no edges.
example : (edgeBoundary {(0, 0), (2, 0)} Finset.univ).card = 0 := by
  simp only [edgeBoundary_univ, Finset.card_empty]

-- A genuine separated cut with a local edge and a remote nonempty cut boundary.
private def disconnectedDomain : Finset (ℤ × ℤ) :=
  {(0, 0), (1, 0), (20, 0), (21, 0)}

private def disconnectedCut : Finset (Site disconnectedDomain) :=
  Finset.univ.filter fun x ↦ x.1 ≠ (21, 0)

private theorem disconnected_endpoints :
    boundaryEndpoints disconnectedDomain disconnectedCut ⊆ {(20, 0), (21, 0)} := by
  classical
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hedge, p, _, q, hq, rfl⟩ := Finset.mem_filter.mp he
  have hqval : q.1 = (21, 0) := by
    simpa only [disconnectedCut, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] using hq
  have hadj : (domainGraph disconnectedDomain).Adj p q := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  have hpdomain := p.property
  simp only [disconnectedDomain, Finset.mem_insert, Finset.mem_singleton] at hpdomain
  have hpval : p.1 = (20, 0) := by
    change (p.1.2 = q.1.2 ∧ (p.1.1 + 1 = q.1.1 ∨ q.1.1 + 1 = p.1.1)) ∨
      (p.1.1 = q.1.1 ∧ (p.1.2 + 1 = q.1.2 ∨ q.1.2 + 1 = p.1.2)) at hadj
    rw [hqval] at hadj
    rcases hpdomain with h | h | h | h
    · rw [h] at hadj
      norm_num at hadj
    · rw [h] at hadj
      norm_num at hadj
    · exact h
    · rw [h] at hadj
      norm_num at hadj
  have hx' : x = p ∨ x = q := Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hx)
  rcases hx' with rfl | rfl <;> simp [hpval, hqval]

private theorem disconnected_separated :
    thinDiagonalTemplate.IsSeparated 1
      (boundaryEndpoints disconnectedDomain disconnectedCut) := by
  intro p hp z hz
  exact separated p hp z (disconnected_endpoints hz)

example : (edgeBoundary disconnectedDomain
    (disconnectedCut.filter fun x ↦ x.1 ∈ thinDiagonalTemplate.points)).card ≤ 384 :=
  template_core_boundary_card_le thinDiagonalTemplate (by norm_num)
    disconnectedDomain disconnectedCut disconnected_separated (by norm_num)

example : (edgeBoundary disconnectedDomain
    (disconnectedCut.filter fun x ↦ x.1 ∈
      ambientDilation thinDiagonalTemplate.points 3 \ thinDiagonalTemplate.points)).card ≤ 768 :=
  template_shell_cut_boundary_card_le thinDiagonalTemplate (by norm_num)
    disconnectedDomain disconnectedCut disconnected_separated (by norm_num) 3 (by omega)

example : (boundaryEndpoints disconnectedDomain disconnectedCut).Nonempty := by
  classical
  let p : Site disconnectedDomain := ⟨(20, 0), by simp [disconnectedDomain]⟩
  let q : Site disconnectedDomain := ⟨(21, 0), by simp [disconnectedDomain]⟩
  have he : s(p, q) ∈ edgeBoundary disconnectedDomain disconnectedCut := by
    apply Finset.mem_filter.mpr
    constructor
    · apply SimpleGraph.mem_edgeFinset.mpr
      change (domainGraph disconnectedDomain).Adj p q
      decide
    · exact ⟨p, by simp [disconnectedCut, p], q, by simp [disconnectedCut, q], rfl⟩
  exact ⟨(20, 0), mem_boundaryEndpoints_of_mem_edgeBoundary (x := p) he (by simp)⟩

example : (edgeBoundary disconnectedDomain
    (disconnectedCut.filter fun x ↦ x.1 ∈ thinDiagonalTemplate.points)).Nonempty := by
  classical
  let p : Site disconnectedDomain := ⟨(0, 0), by simp [disconnectedDomain]⟩
  let q : Site disconnectedDomain := ⟨(1, 0), by simp [disconnectedDomain]⟩
  refine ⟨s(p, q), Finset.mem_filter.mpr ⟨?_, p, ?_, q, ?_, rfl⟩⟩
  · apply SimpleGraph.mem_edgeFinset.mpr
    change (domainGraph disconnectedDomain).Adj p q
    decide
  · simp [disconnectedCut, thinDiagonalTemplate, thinDiagonalSample, p]
  · simp [disconnectedCut, thinDiagonalTemplate, thinDiagonalSample, q]

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.edgeBoundary_filter_image_subset_ambientBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.edgeBoundary_filter_image_subset_ambientBoundary

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_filter_le_ambientBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_filter_le_ambientBoundary

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.disjoint_ambientDilation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.disjoint_ambientDilation

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_cut_boundary_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_cut_boundary_card_le

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_core_boundary_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_core_boundary_card_le

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_shell_cut_boundary_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_shell_cut_boundary_card_le

-- The whole side-two cell lies in the maximal permitted dilation.
private theorem thinDiagonal_cell_subset : latticeDyadicCell 1 (0, 0) ⊆
    ambientDilation thinDiagonalTemplate.points 3 := by
  intro q hq
  have hq' := (mem_latticeDyadicCell_iff_bounds 1 (0, 0) q).mp hq
  norm_num at hq'
  apply mem_ambientDilation_iff.mpr
  refine ⟨(0, 0), by simp [thinDiagonalTemplate, thinDiagonalSample], ?_⟩
  norm_num
  omega

-- Nonvacuous strict clearance for a whole side-two cell in the actual thin template.
example (p : ℤ × ℤ) (hp : p ∈ latticeDyadicCell 1 (0, 0)) :
    (2 : ℝ) < max |(p.1 : ℝ) - 20| |(p.2 : ℝ) - 0| := by
  simpa using separated.side_lt_dist_of_mem_ambientDilation
    (by norm_num) (by omega : 3 ≤ 3) (by omega : 2 ≤ 3) (thinDiagonal_cell_subset hp)
    (by simp : (20, 0) ∈ ({(20, 0), (21, 0)} : Finset (ℤ × ℤ)))

-- Instantiate the full natural clearance theorem at both endpoints of a
-- genuine physical crossing edge in the remote two-site component. Neither
-- separation nor containment is assumed: both were proved for this fixture.
example (p : ℤ × ℤ) (hp : p ∈ latticeDyadicCell 1 (0, 0)) :
    2 < max (p.1 - 20).natAbs p.2.natAbs ∧
      2 < max (p.1 - 21).natAbs p.2.natAbs := by
  classical
  let z : Site disconnectedDomain := ⟨(20, 0), by simp [disconnectedDomain]⟩
  let w : Site disconnectedDomain := ⟨(21, 0), by simp [disconnectedDomain]⟩
  have he : s(z, w) ∈ edgeBoundary disconnectedDomain disconnectedCut := by
    apply Finset.mem_filter.mpr
    constructor
    · apply SimpleGraph.mem_edgeFinset.mpr
      change (domainGraph disconnectedDomain).Adj z w
      decide
    · exact ⟨z, by simp [disconnectedCut, z], w, by simp [disconnectedCut, w], rfl⟩
  have hsep : thinDiagonalTemplate.IsSeparated ((1 : ℕ) : ℝ)
      (boundaryEndpoints disconnectedDomain disconnectedCut) := by
    simpa only [Nat.cast_one] using disconnected_separated
  have h := hsep.dyadicCell_clearance (D₀ := 1)
    (by omega) (by omega : 3 ≤ 3) (by norm_num : 2 ^ 1 ≤ 3)
    thinDiagonal_cell_subset s(z, w) he
  constructor
  · simpa [z] using h z (by simp) p hp
  · simpa [w] using h w (by simp) p hp

-- Native dyadic rectangles retain negative endpoints and use site-count size.
example : (latticeDyadicRect 1 (-2, -1)).toFinset =
    {(-4, -2), (-4, -1), (-3, -2), (-3, -1)} := by decide

example : (latticeDyadicRect 0 (-3, 2)).size = 1 := by simp

-- A genuine selected core cell is safe for the disconnected domain's nonempty cut.
example : IsSafe disconnectedDomain disconnectedCut 1 (latticeDyadicRect 0 (0, 0)) := by
  apply disconnected_separated.isSafe_cappedDyadicPartition_core (by decide) 0 0 (0, 0)
    (by decide)
  decide

-- Maximal permitted dilation, a cap-scale square, and a negative index.
example : IsSafe disconnectedDomain disconnectedCut 1 (latticeDyadicRect 1 (-1, 0)) := by
  apply disconnected_separated.isSafe_cappedDyadicPartition_shell (by decide)
    3 1 1 (-1, 0) (by decide) (by decide)
  decide +kernel

-- A unit shell rectangle has a nonempty physical intersection, despite domain holes.
example : IsSafe disconnectedDomain disconnectedCut 1 (latticeDyadicRect 0 (1, 0)) := by
  apply disconnected_separated.isSafe_cappedDyadicPartition_shell (by decide)
    1 0 0 (1, 0) (by decide) (by decide)
  decide +kernel

example : (rectRegion disconnectedCut (latticeDyadicRect 0 (1, 0))).Nonempty := by
  refine ⟨⟨(1, 0), by simp [disconnectedDomain]⟩, ?_⟩
  simp [mem_rectRegion, disconnectedCut, IntRect.mem_toFinset, latticeDyadicRect]

-- The physical-domain adapter includes no sites absent from the ambient square.
example : rectRegion disconnectedCut (latticeDyadicRect 0 (-3, 2)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hdomain := x.property
  have hrect := (mem_rectRegion.mp hx).2
  simp only [IntRect.mem_toFinset, latticeDyadicRect] at hrect
  simp only [disconnectedDomain, Finset.mem_insert, Finset.mem_singleton] at hdomain
  rcases hdomain with h | h | h | h <;> rw [h] at hrect <;> norm_num at hrect

-- Check the complete export list against the standard kernel axioms.
run_cmd do
  for name in [``latticeDyadicRect, ``toFinset_latticeDyadicRect,
      ``size_latticeDyadicRect, ``rectRegion_latticeDyadicRect,
      ``Template.IsSeparated.isSafe_of_subset_ambientDilation,
      ``Template.IsSeparated.isSafe_cappedDyadicPartition_core,
      ``Template.IsSeparated.isSafe_cappedDyadicPartition_shell] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"
