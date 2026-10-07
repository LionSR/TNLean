import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum

/-! Degenerate and repeated-region regressions for the actual regularized minimum. -/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix TNLean.PEPS

section General

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]

example (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1) (b : ℝ)
    (regions : Fin 0 → Finset V)
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
    regularizedPatchObjective regions (fun _ ↦ 0) b Ω x = 1 := by
  classical
  simpa [regularizedPatchObjective, regularizedPatchOutput, regularizedPatchOperator] using hΩ

example (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1) {b : ℝ} (hb : 0 < b) (regions : Fin 0 → Finset V) :
    regularizedPatchMinimum regions (fun _ ↦ 0) b Ω = 1 := by
  have h := regularizedPatchMinimum_bounds regions (fun _ ↦ 0) (by simp) hb Ω hΩ
  simp only [Finset.sum_const_zero, neg_zero, zero_div, Real.rpow_zero] at h
  exact le_antisymm h.2 h.1

open Classical in
example {m : ℕ} (regions : Fin m → Finset V) {b : ℝ} (hb : 0 < b)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m) :
    regularizedPatchFilter regions (fun _ ↦ 0) b x j = 1 := by
  classical
  simp only [regularizedPatchFilter, neg_zero, zero_div,
    CFC.rpow_zero _ ((hx j).1.add_smul_one_posDef hb).posSemidef.nonneg]
  exact dependentRegionOperatorLift_one (Out := Out) _

example {m : ℕ} (regions : Fin m → Finset V) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    regularizedPatchObjective regions (fun _ ↦ 0) b Ω x = 1 := by
  have h := regularizedPatchObjective_bounds regions (fun _ ↦ 0) (by simp) hb Ω hΩ hx
  simp only [Finset.sum_const_zero, neg_zero, zero_div, Real.rpow_zero] at h
  exact le_antisymm h.2 h.1

example : Fintype.card ((v : (∅ : Finset V)) → Out v.1) = 1 := by simp

example : (1 : Matrix ((v : (∅ : Finset V)) → Out v.1)
    ((v : (∅ : Finset V)) → Out v.1) ℂ).PosSemidef ∧
    (1 : Matrix ((v : (∅ : Finset V)) → Out v.1)
      ((v : (∅ : Finset V)) → Out v.1) ℂ).trace = 1 := by
  exact ⟨Matrix.PosSemidef.one, by simp⟩

example (R : Finset V) (a : Fin 2 → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
    ∃ x ∈ regularizedPatchDomain (Out := Out) (fun _ : Fin 2 ↦ R),
      IsMinOn (regularizedPatchObjective (fun _ ↦ R) a b Ω)
        (regularizedPatchDomain (fun _ ↦ R)) x :=
  exists_isMinOn_regularizedPatchObjective _ a hb Ω hΩ

example {m : ℕ} (regions : Fin m → Finset V) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {R : ℝ} (hR : 0 ≤ R)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
    0 < regularizedPatchMinimum regions a (Real.exp (-R)) Ω ∧
      regularizedPatchMinimum regions a (Real.exp (-R)) Ω ≤ Real.exp (R * (∑ j, a j) / 2) :=
  ⟨regularizedPatchMinimum_pos regions a ha (Real.exp_pos _) Ω hΩ,
    (regularizedPatchMinimum_exp_bounds regions a ha hR Ω hΩ).2⟩

end General
