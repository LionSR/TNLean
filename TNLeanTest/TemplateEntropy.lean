import TNLean.PEPS.AreaLaw.Geometry.TemplateEntropy

/-!
# Actual-state partial-row entropy regressions

Normalized basis vectors exercise empty domains, empty increments, the unit local
alphabet, and the final depth. No abstract entropy functional is supplied.
-/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

private noncomputable def basisState (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (a : Site Λ → Fin q) : StateSpace Λ q := PiLp.single 2 a 1

private theorem norm_basisState (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (a : Site Λ → Fin q) : ‖basisState Λ q a‖ = 1 := by
  simp [basisState]

-- An empty domain has one configuration even when the local alphabet is empty.
example : regionalEntropy ∅ 0 (basisState ∅ 0 fun x ↦ False.elim (by simpa using x.property))
    ∅ ≤ 0 := by
  simpa using regionalEntropy_le_card_mul_log ∅ 0
    (basisState ∅ 0 fun x ↦ False.elim (by simpa using x.property))
    (norm_basisState _ _ _) ∅

-- Arbitrary actual templates, actual normalized one-dimensional physical states,
-- and arbitrary subsets of the final row; q = 1 gives exactly zero cost.
example (Λ : Finset (ℤ × ℤ)) {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (A : Finset (Site Λ))
    (Y : Finset (ℤ × ℤ))
    (hY : Y ⊆ ambientDilation T.points s₀ \ ambientDilation T.points (s₀ - 1)) :
    |regionalEntropy Λ 1 (basisState Λ 1 fun _ ↦ 0)
        (A.filter fun x ↦ x.val ∈ (ambientDilation T.points (s₀ - 1) \ T.points) ∪ Y) -
      regionalEntropy Λ 1 (basisState Λ 1 fun _ ↦ 0)
        (A.filter fun x ↦ x.val ∈ ambientDilation T.points (s₀ - 1) \ T.points)| ≤ 0 := by
  simpa using template_partial_row_entropy_le Λ 1 (by decide)
    (basisState Λ 1 fun _ ↦ 0) (norm_basisState _ _ _) T hC A s₀ T.s₀_pos le_rfl Y hY

-- Empty increments must leave any actual state's entropy unchanged.
example (Λ : Finset (ℤ × ℤ)) (R : Finset (Site Λ)) :
    |regionalEntropy Λ 2 (basisState Λ 2 fun _ ↦ 0) (R ∪ ∅) -
      regionalEntropy Λ 2 (basisState Λ 2 fun _ ↦ 0) R| = 0 := by simp

-- Both signs of the increment are bounded for an arbitrary normalized physical
-- vector, including entangled vectors (no product-state premise).
example (Λ : Finset (ℤ × ℤ)) (Ω : StateSpace Λ 2) (hΩ : ‖Ω‖ = 1)
    (R B : Finset (Site Λ)) (h : Disjoint R B) :
    |regionalEntropy Λ 2 Ω (R ∪ B) - regionalEntropy Λ 2 Ω R| ≤
      B.card * Real.log 2 :=
  (abs_regionalEntropy_union_sub_le Λ 2 Ω hΩ R B h).trans
    (regionalEntropy_le_card_mul_log Λ 2 Ω hΩ B)

set_option linter.hashCommand false

#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_le_card_mul_log
#print axioms TNLean.PEPS.AreaLaw.abs_regionalEntropy_union_sub_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_partial_row_entropy_le
