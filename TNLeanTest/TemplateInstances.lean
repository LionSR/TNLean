import TNLean.PEPS.AreaLaw.Geometry.TemplateInstances
import TNLean.PEPS.AreaLaw.Geometry.TemplateBoxEntropy
import TNLean.PEPS.AreaLaw.Geometry.TemplateLayers

/-!
# Template instances: a thin rectangle and a disconnected union

A one-row rectangle and a union of two separated one-row pieces are complete
templates of Definition 9.3. The counting and entropy estimates of Lemma 9.4
apply to them with no further geometric hypothesis.
-/

open TNLean.Lattice

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

/-! ### A thin rectangle -/

/-- The one-row rectangle `[0, 5] × {0}`. -/
private def thinRow : IntRect := ⟨0, 5, 0, 0, by decide, le_rfl⟩

private theorem thinRow_size : thinRow.size = 6 := by decide

/-- The thin rectangle as a one-piece template with `s₀ = 6` and `n = 24 · 7`. -/
private noncomputable def thinTemplate : Template 24 168 6 :=
  Template.ofIntRect thinRow thinRow_size.le (by norm_num) (by norm_num)

example : thinTemplate.points = thinRow.toFinset := rfl

example : thinTemplate.pieceCount = 1 := rfl

-- The real rectangle is nondegenerate even though the lattice rectangle is one row.
example : (TemplatePolygon.ofIntRect thinRow).region =
    Set.Icc (0 : ℝ) (5 + 1 / 2) ×ˢ Set.Icc (0 : ℝ) (0 + 1 / 2) := by
  simpa [thinRow] using TemplatePolygon.region_ofIntRect thinRow

-- A rectangle safe with clearance `4 D₀` is separated in the template sense.
example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (D₀ : ℕ)
    (hsafe : IsSafe Λ A (4 * D₀) thinRow) :
    thinTemplate.IsSeparated D₀ (boundaryEndpoints Λ A) :=
  Template.isSeparated_ofIntRect_of_isSafe thinRow _ _ _ hsafe (by rw [thinRow_size])

-- The counting bounds of Lemma 9.4 for the thin rectangle.
example : thinTemplate.points.card ≤ 9 * 168 * 6 := template_card_le _ (by norm_num)

example (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ 6) :
    (ambientDilation thinTemplate.points j \
      ambientDilation thinTemplate.points (j - 1)).card ≤ 168 :=
  template_layer_card_le _ (by norm_num) j hj hjs

/-- The core entropy bound of Lemma 9.4 for a safe thin rectangle, from a safe-box
estimate with one exponent `e`. Here `2 ^ 2 ≤ 6 < 2 ^ 3`. -/
example (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (hD : 1 ≤ D₀) (hsafe : IsSafe Λ A (4 * D₀) thinRow)
    (e C : ℝ) (he : 0 < e) (hC : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ thinRow.toFinset) ≤
      C * (18 + 4 / ((2 : ℝ) ^ e - 1)) * (168 : ℕ) * ((6 : ℕ) : ℝ) ^ e :=
  thinTemplate.regionalEntropy_core_le_of_safe_box Λ q D₀ Ω hΩ A (by norm_num)
    (Template.isSeparated_ofIntRect_of_isSafe thinRow _ _ _ hsafe (by rw [thinRow_size]))
    hD 2 (by norm_num) (by norm_num) e C he hC hbox

/-- The shell entropy bound of Lemma 9.4 for the same thin rectangle, for depth
`j ≤ L = 4`. -/
example (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (hD : 1 ≤ D₀) (hsafe : IsSafe Λ A (4 * D₀) thinRow)
    (e C : ℝ) (he : 0 < e) (hC : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e))
    (j : ℕ) (hj : j ≤ 4) :
    regionalEntropy Λ q Ω
      (A.filter fun x ↦ x.1 ∈ ambientDilation thinRow.toFinset j \ thinRow.toFinset) ≤
      C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * (168 : ℕ) * ((4 : ℕ) : ℝ) ^ e :=
  thinTemplate.regionalEntropy_shell_le_of_safe_box Λ q D₀ Ω hΩ A (by norm_num)
    (Template.isSeparated_ofIntRect_of_isSafe thinRow _ _ _ hsafe (by rw [thinRow_size]))
    hD j 4 2 hj (by norm_num) (by norm_num) (by norm_num) e C he hC hbox

/-! ### A disconnected union of two pieces -/

/-- The left piece `[0, 1] × {0}`. -/
private def leftPiece : IntRect := ⟨0, 1, 0, 0, by decide, le_rfl⟩

/-- The right piece `[4, 5] × {0}`. -/
private def rightPiece : IntRect := ⟨4, 5, 0, 0, by decide, le_rfl⟩

private noncomputable def leftTemplate : Template 24 144 2 :=
  Template.ofIntRect leftPiece (by decide) (by norm_num) (by norm_num)

private noncomputable def rightTemplate : Template 24 144 2 :=
  Template.ofIntRect rightPiece (by decide) (by norm_num) (by norm_num)

/-- The union of the two pieces, a two-piece template with `n = 24 · 2 · 3`. -/
private noncomputable def disconnectedTemplate : Template 24 144 2 :=
  leftTemplate.union rightTemplate (by norm_num [leftTemplate, rightTemplate]) (by
    intro x hx y hy
    simp only [leftTemplate, rightTemplate, Template.points_ofIntRect, Finset.mem_union,
      IntRect.mem_toFinset, leftPiece, rightPiece] at hx hy
    have hx₁ : (0 : ℝ) ≤ x.1 ∧ (x.1 : ℝ) ≤ 5 := by
      constructor <;> norm_cast <;> omega
    have hy₁ : (0 : ℝ) ≤ y.1 ∧ (y.1 : ℝ) ≤ 5 := by
      constructor <;> norm_cast <;> omega
    have hx₂ : x.2 = 0 := by omega
    have hy₂ : y.2 = 0 := by omega
    rw [hx₂, hy₂, max_le_iff, abs_le, abs_le]
    norm_num
    constructor <;> linarith [hx₁.1, hx₁.2, hy₁.1, hy₁.2])

example : disconnectedTemplate.points = leftPiece.toFinset ∪ rightPiece.toFinset := rfl

example : disconnectedTemplate.pieceCount = 2 := rfl

-- No two sites of different pieces are lattice neighbours, even diagonally.
example : ∀ x ∈ leftPiece.toFinset, ∀ y ∈ rightPiece.toFinset, 1 < supDist x y := by
  intro x hx y hy
  simp only [IntRect.mem_toFinset, leftPiece, rightPiece] at hx hy
  simp only [supDist]
  omega

-- The counting bounds of Lemma 9.4 for the disconnected union.
example : disconnectedTemplate.points.card ≤ 9 * 144 * 2 := template_card_le _ (by norm_num)

example (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ 2) :
    (ambientDilation disconnectedTemplate.points j \
      ambientDilation disconnectedTemplate.points (j - 1)).card ≤ 144 :=
  template_layer_card_le _ (by norm_num) j hj hjs

/-- The core entropy bound of Lemma 9.4 for the separated disconnected union.
Here `2 ^ 1 ≤ 2 < 2 ^ 2`. -/
example (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (hD : 1 ≤ D₀)
    (hsep : disconnectedTemplate.IsSeparated D₀ (boundaryEndpoints Λ A))
    (e C : ℝ) (he : 0 < e) (hC : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω
      (A.filter fun x ↦ x.1 ∈ leftPiece.toFinset ∪ rightPiece.toFinset) ≤
      C * (18 + 4 / ((2 : ℝ) ^ e - 1)) * (144 : ℕ) * ((2 : ℕ) : ℝ) ^ e :=
  disconnectedTemplate.regionalEntropy_core_le_of_safe_box Λ q D₀ Ω hΩ A (by norm_num)
    hsep hD 1 (by norm_num) (by norm_num) e C he hC hbox

-- Omitting empty pieces keeps the point set.
example : (disconnectedTemplate.omitEmpty (by norm_num)).points =
    leftPiece.toFinset ∪ rightPiece.toFinset := rfl
