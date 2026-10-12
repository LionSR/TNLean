import TNLean.PEPS.AreaLaw.Geometry.TemplateBoxEntropy
import TNLean.PEPS.AreaLaw.InitialSafeRectangleEntropy

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
example : regionalEntropy ∅ 0
    (basisState ∅ 0 fun x ↦ isEmptyElim x) ∅ ≤ 0 := by
  simpa using regionalEntropy_le_card_mul_log ∅ 0
    (basisState ∅ 0 fun x ↦ isEmptyElim x)
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

/--
info: 'TNLean.PEPS.AreaLaw.regionalEntropy_le_card_mul_log'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_le_card_mul_log
/--
info: 'TNLean.PEPS.AreaLaw.abs_regionalEntropy_union_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.abs_regionalEntropy_union_sub_le
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.template_partial_row_entropy_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.template_partial_row_entropy_le

-- The physical partition drops ambient sites missing from a disconnected domain.
private def holesDomain : Finset (ℤ × ℤ) := {(-1, -1), (0, 0), (7, 2)}

example :
    (cappedDyadicPartition {(-1, -1), (0, 0), (1, 0)} 1).biUnion
      (fun c ↦ rectRegion (Finset.univ : Finset (Site holesDomain))
        (latticeDyadicRect c.1 c.2)) =
      (Finset.univ : Finset (Site holesDomain)).filter
        (fun x ↦ x.1 = (-1, -1) ∨ x.1 = (0, 0)) := by
  rw [biUnion_rectRegion_cappedDyadicPartition]
  ext x
  have hne : x.1 ≠ (1, 0) := by
    intro h
    have hp := x.property
    rw [h] at hp
    norm_num [holesDomain] at hp
  simp [hne]

-- One-dimensional local spaces supply a real, normalized-state safe-box bound
-- with C = 0 for every exponent and every native rectangle.
private theorem unit_box_bound (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (e : ℝ) (Q : IntRect) :
    regionalEntropy Λ 1 (basisState Λ 1 fun _ ↦ 0) (rectRegion A Q) ≤
      0 * (Q.size : ℝ) ^ (1 + e) := by
  simpa using regionalEntropy_le_card_mul_log Λ 1
    (basisState Λ 1 fun _ ↦ 0) (norm_basisState _ _ _) (rectRegion A Q)

example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) {Ctpl : ℝ} {n s₀ D₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (K : ℕ) (hlo : 2 ^ K ≤ s₀) (hhi : s₀ < 2 ^ (K + 1))
    (e : ℝ) (he : 0 < e) :
    regionalEntropy Λ 1 (basisState Λ 1 fun _ ↦ 0)
      (A.filter fun x ↦ x.1 ∈ T.points) ≤ 0 := by
  simpa only [zero_mul] using Template.regionalEntropy_core_le_of_safe_box Λ 1 D₀
    (basisState Λ 1 fun _ ↦ 0) (norm_basisState _ _ _) A T hC hsep hD K hlo hhi
    e 0 he (le_refl _) (fun Q _ ↦ unit_box_bound Λ A e Q)

-- The last allowed row, with any subset of that row, retains zero entropy at q=1.
example (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) {Ctpl : ℝ} {n s₀ D₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (K : ℕ) (hlo : 2 ^ K ≤ s₀) (hhi : s₀ < 2 ^ (K + 1))
    (Y : Finset (ℤ × ℤ))
    (hY : Y ⊆ ambientDilation T.points s₀ \ ambientDilation T.points (s₀ - 1))
    (e : ℝ) (he : 0 < e) :
    regionalEntropy Λ 1 (basisState Λ 1 fun _ ↦ 0)
      (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (s₀ - 1) \ T.points) ∪ Y) ≤ 0 := by
  simpa only [zero_mul, Nat.cast_one, Real.log_one, mul_zero, add_zero] using
    Template.regionalEntropy_prefix_le_of_safe_box Λ 1 D₀ (by decide)
      (basisState Λ 1 fun _ ↦ 0) (norm_basisState _ _ _) A T hC hsep hD
      s₀ s₀ K T.s₀_pos le_rfl le_rfl hlo hhi Y hY e 0 he (le_refl _)
      (fun Q _ ↦ unit_box_bound Λ A e Q)

-- Empty shells remain admissible for an arbitrary normalized, possibly entangled state.
example (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (K : ℕ) :
    regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ (∅ : Finset (ℤ × ℤ))) ≤ 0 := by
  simpa using regionalEntropy_filter_le_sum_rectRegion Λ q Ω hΩ A ∅ K

run_cmd do
  for name in [``biUnion_rectRegion_cappedDyadicPartition,
      ``pairwiseDisjoint_rectRegion_cappedDyadicPartition,
      ``regionalEntropy_filter_le_sum_rectRegion,
      ``Template.regionalEntropy_core_le_of_safe_box,
      ``Template.regionalEntropy_shell_le_of_safe_box,
      ``Template.regionalEntropy_prefix_le_of_safe_box,
      ``exists_template_entropy_bounds_of_arbitrary_safe_box] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

/--
info: 'TNLean.PEPS.AreaLaw.exists_regionalEntropy_safe_rect_le_rpow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_regionalEntropy_safe_rect_le_rpow
