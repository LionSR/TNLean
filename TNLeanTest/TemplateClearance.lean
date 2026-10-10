import TNLean.PEPS.AreaLaw.Geometry.TemplateClearance

/-! Strict template-clearance and dyadic interval regressions. -/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

-- Negative-coordinate cells use the same closed integer intervals.
example : latticeDyadicCell 2 (-2, -3) = Finset.Icc (-8) (-5) ×ˢ Finset.Icc (-12) (-9) := by
  simpa using latticeDyadicCell_eq_Icc_product 2 (-2, -3)

-- Unit scale is included, even at negative coordinates.
example : latticeDyadicCell 0 (-1, -2) = {(-1, -2)} := by
  simp

-- The literal interval size convention counts sites, not endpoint displacement.
example (k : ℕ) (z : ℤ × ℤ) :
    max (z.1 * 2 ^ k + 2 ^ k - 1 + 1 - z.1 * 2 ^ k).toNat
      (z.2 * 2 ^ k + 2 ^ k - 1 + 1 - z.2 * 2 ^ k).toNat = 2 ^ k := by
  rw [(latticeDyadicCell_interval_length k z.1).2,
    (latticeDyadicCell_interval_length k z.2).2, max_self]

-- Clearance is derived for every actual edge endpoint, not supplied as an assumption.
example {Ctpl : ℝ} {n s₀ D₀ j k : ℕ} {T : Template Ctpl n s₀}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsep : T.IsSeparated (D₀ : ℝ) (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (hj : j ≤ s₀) (hk : 2 ^ k ≤ s₀) {c : ℤ × ℤ}
    (hcell : latticeDyadicCell k c ⊆ ambientDilation T.points j)
    {e : Sym2 (Site Λ)} (he : e ∈ edgeBoundary Λ A) {z : Site Λ} (hz : z ∈ e)
    {p : ℤ × ℤ} (hp : p ∈ latticeDyadicCell k c) :
    D₀ * 2 ^ k < max (p.1 - z.1.1).natAbs (p.2 - z.1.2).natAbs :=
  hsep.dyadicCell_clearance hD hj hk hcell e he z hz p hp

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.latticeDyadicCell_eq_Icc_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms latticeDyadicCell_eq_Icc_product
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.latticeDyadicCell_interval_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms latticeDyadicCell_interval_length
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.lt_dist_of_mem_ambientDilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Template.IsSeparated.lt_dist_of_mem_ambientDilation
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.side_lt_dist_of_mem_ambientDilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Template.IsSeparated.side_lt_dist_of_mem_ambientDilation
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.dyadicCell_clearance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Template.IsSeparated.dyadicCell_clearance
