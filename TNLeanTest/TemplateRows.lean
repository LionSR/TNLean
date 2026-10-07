import TNLean.PEPS.AreaLaw.Geometry.TemplateRows

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

-- Negative coordinates and diagonal integer shifts must not use natural rounding.
example : ⌈(-3 / 2 : ℝ) + (-1 : ℝ) * (-4 : ℤ)⌉ = 3 := by
  rw [ceil_affine_row]
  norm_num

example : ⌊(-3 / 2 : ℝ) + (1 : ℝ) * (-4 : ℤ)⌋ = -6 := by
  rw [floor_affine_row]
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

#print axioms TNLean.PEPS.AreaLaw.card_ambientDilation_biUnion_sdiff_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_eq_Icc
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_card_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.mem_latticeRow_ambientDilation
