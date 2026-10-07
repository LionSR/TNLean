import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary
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
  simp [boundaryEndpoints]

example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ (∅ : Finset (ℤ × ℤ)))).card = 0 := by
  simp

set_option linter.hashCommand false

#print axioms TNLean.PEPS.AreaLaw.Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary

#print axioms TNLean.PEPS.AreaLaw.Geometry.edgeBoundary_filter_image_subset_ambientBoundary

#print axioms TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_filter_le_ambientBoundary

#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.disjoint_ambientDilation

#print axioms TNLean.PEPS.AreaLaw.Geometry.template_cut_boundary_card_le

#print axioms TNLean.PEPS.AreaLaw.Geometry.template_core_boundary_card_le

#print axioms TNLean.PEPS.AreaLaw.Geometry.template_shell_cut_boundary_card_le
