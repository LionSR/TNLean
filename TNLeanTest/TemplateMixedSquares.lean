import TNLean.PEPS.AreaLaw.Geometry.TemplateShellCover

/-!
# Actual-template mixed-square regressions

Check integer dilation, signed coordinates, thin samples, empty pieces,
disconnected unions, overlapping pieces, differences and selected scales.
The actual thin-polygon fixture is reused from the template row regressions.
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

-- Side one cannot contain both an inside and an outside site.
example (S : Finset (ℤ × ℤ)) : mixedDyadicIndices S 0 = ∅ := by
  ext z
  simp [mem_mixedDyadicIndices]

-- Signed division locates negative cells without truncating toward zero.
example : (-4, -2) ∈ latticeDyadicCell 1 (-2, -1) := by decide
example : (-1, -1) ∈ latticeDyadicCell 1 (-1, -1) := by decide

-- Empty sampled pieces are allowed even though the whole Template is nonempty.
example {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀)
    (i : Fin T.pieceCount) (hi : T.sample i = ∅) (r k : ℕ) :
    mixedDyadicIndices (ambientDilation (T.sample i) r) k = ∅ := by
  simp [hi, ambientDilation]

example : 2 ^ 1 * (mixedDyadicIndices (ambientDilation thinDiagonalTemplate.points 1) 1).card ≤
    2 * 96 + 24 * thinDiagonalTemplate.pieceCount * 2 ^ 1 :=
  thinDiagonalTemplate.card_mixedDyadicIndices_dilation_le (by norm_num) 1 1 (by decide)

example : mixedDyadicIndices (ambientDilation thinDiagonalSample 1) 1 =
    {(-1, 0), (0, -1), (1, 0), (0, 1), (1, 1)} := by decide +kernel

example (k : ℕ) :
    2 ^ k * (mixedDyadicIndices (ambientDilation thinDiagonalTemplate.points 3 \
      thinDiagonalTemplate.points) k).card ≤
      3 * 96 + 48 * thinDiagonalTemplate.pieceCount * 2 ^ k :=
  thinDiagonalTemplate.card_mixedDyadicIndices_shell_le (by norm_num) 3 k (by decide)

example : 2 ^ 1 * ((cappedDyadicPartition (ambientDilation thinDiagonalTemplate.points 2 \
    thinDiagonalTemplate.points) 2).filter (fun c ↦ c.1 = 1)).card ≤ 14 * 96 :=
  thinDiagonalTemplate.card_cappedDyadicPartition_shell_below_cap_le (by norm_num)
    2 2 1 (by decide) (by decide) (by decide)

-- Dilation is taken in the ambient integer lattice, not in an induced graph.
example : (0, 1) ∈ ambientDilation thinDiagonalTemplate.points 1 := by
  change (0, 1) ∈ ambientDilation thinDiagonalSample 1
  decide

-- Disconnected samples and their holes must survive the union operation.
example : (mixedDyadicIndices (ambientDilation {(-3, 0), (3, 0)} 1) 1).card = 6 := by
  decide +kernel

example : (0, 0) ∉ ambientDilation {(-3, 0), (3, 0)} 1 := by decide

-- Removing one site from a contained square creates a mixed square.
example : mixedDyadicIndices (latticeDyadicCell 1 (-2, -1) \ {(-4, -2)}) 1 =
    {(-2, -1)} := by decide

-- Duplicate and empty constituents need no disjointness premise.
example (S : Finset (ℤ × ℤ)) (k : ℕ) :
    (mixedDyadicIndices (({0, 1, 2} : Finset ℕ).biUnion
      (fun i ↦ if i = 2 then ∅ else S)) k).card ≤
      ∑ i ∈ ({0, 1, 2} : Finset ℕ),
        (mixedDyadicIndices (if i = 2 then ∅ else S) k).card :=
  card_mixedDyadicIndices_biUnion_le _ _ k

-- A zero-radius shell has no selected cells, at every cap and exponent.
example (K : ℕ) (e : ℝ) :
    ∑ c ∈ cappedDyadicPartition (ambientDilation thinDiagonalTemplate.points 0 \
      thinDiagonalTemplate.points) K, ((2 : ℝ) ^ c.1) ^ (1 + e) = 0 := by
  simp

-- The positive-exponent covering theorem also covers e = 1; its constant is 16.
-- This tests the largest admissible radius, a non-power-of-two L, and a thin sample.
example :
    ∑ c ∈ cappedDyadicPartition (ambientDilation thinDiagonalTemplate.points 3 \
      thinDiagonalTemplate.points) 1, ((2 : ℝ) ^ c.1) ^ (2 : ℝ) ≤ 4608 := by
  have h := thinDiagonalTemplate.sum_rpow_cappedDyadicPartition_shell_le
    (by norm_num) 3 3 1 (by decide) (by decide) (by decide) (by decide) 1 (by norm_num)
  norm_num at h ⊢
  exact h

-- L = 1 forces cap zero, so there is no below-cap geometric sum.
example :
    2 ^ 0 * ((cappedDyadicPartition (ambientDilation thinDiagonalTemplate.points 1 \
      thinDiagonalTemplate.points) 0).filter (fun c ↦ c.1 = 0)).card ≤ 2 * 96 :=
  thinDiagonalTemplate.card_cappedDyadicPartition_shell_at_cap_le
    (by norm_num) 1 1 0 (by decide) (by decide) (by decide)

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Geometry.Template.card_shell_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.card_shell_le

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Geometry.Template.card_cappedDyadicPartition_shell_at_cap_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.card_cappedDyadicPartition_shell_at_cap_le

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Geometry.Template.sum_rpow_cappedDyadicPartition_shell_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.sum_rpow_cappedDyadicPartition_shell_le
