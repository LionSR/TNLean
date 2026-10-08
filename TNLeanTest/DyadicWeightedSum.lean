import TNLean.PEPS.AreaLaw.Geometry.DyadicWeightedSum

open TNLean.PEPS.AreaLaw.Geometry

-- Cap zero: no below-cap hypothesis is consumed, including zero budget.
example (a : ℕ → ℝ) {A e : ℝ} (he : 0 < e) (ha : a 0 ≤ A) :
    (∑ k ∈ Finset.range 1, a k * ((2 : ℝ) ^ k) ^ (1 + e)) ≤ A := by
  simpa using sum_weighted_dyadic_rpow_le a 0 he (le_refl (0 : ℝ))
    (by simpa using ha) (by intro k hk; omega)

-- Two occupied scales, with sharp cap and below-cap side budgets.
example : (∑ k ∈ Finset.range 2, (1 : ℝ) * ((2 : ℝ) ^ k) ^ (1 + (1 : ℝ))) ≤ 6 := by
  have h := sum_weighted_dyadic_rpow_le (fun _ ↦ 1) 1 (e := 1) (A := 2) (B := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro k hk; have : k = 0 := by omega; subst k; norm_num)
  norm_num at h ⊢

-- Empty weights and an arbitrary positive exponent require no occupied scale.
example (K : ℕ) {e : ℝ} (he : 0 < e) :
    (∑ k ∈ Finset.range (K + 1), (0 : ℝ) * ((2 : ℝ) ^ k) ^ (1 + e)) ≤ 0 := by
  simpa using sum_weighted_dyadic_rpow_le (fun _ ↦ 0) K he (le_refl (0 : ℝ))
    (by simp) (by intros; simp)

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.sum_weighted_dyadic_rpow_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.sum_weighted_dyadic_rpow_le
