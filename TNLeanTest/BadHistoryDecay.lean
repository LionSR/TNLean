import TNLean.PEPS.AreaLaw.Scan.PhysicalBadHistoryDecay

/-!
Concrete source exponents and the probability exponent 200, finite polynomial
accounting, and guarded axiom checks for the actual asymptotic history theorem.
-/

open Filter TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

set_option autoImplicit false

-- All source exponent inequalities are simultaneously satisfied.
example : (0 : ℝ) < 1 / 4 ∧ (0 : ℝ) < 1 / 8 ∧
    (1 / 8 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 - 1 / 4 := by norm_num

-- The threshold is chosen before arbitrary finite domains, labels and targets.
open Classical in
example :
    ∀ᶠ n : ℕ in atTop, ∀ (I : Type) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (TNLean.PEPS.AreaLaw.Site Λ) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - (1 / 4 : ℝ))⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ (1 / 8 : ℝ)⌉₊ → S.r₀ = roundedLogRadius 1 n →
      S.M = ⌈(1 : ℝ) * n * S.D⌉₊ → (T.card : ℝ) ≤ 1 * (n : ℝ) ^ 2 →
      S.graph = TNLean.PEPS.AreaLaw.domainGraph Λ →
      S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ TNLean.PEPS.AreaLaw.Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - (1 / 4 : ℝ))⌋₊ + 10 * S.r₀ : ℕ) : ℤ) <
          ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - (1 / 4 : ℝ))⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ 1) →
      (∑ h : History S.K S.m S.M (n * S.m),
        if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (n : ℝ) ^ (-200 : ℝ) := by
  exact eventually_bad_history_probability_le (ell := 1 / 4) (kappa := 1 / 8)
    (mu := 1 / 2) (Cr := 1) (C1 := 1) (Ct := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 1 200

example : ((2 * 2 * (4 + 2 * 2) * (2 * 2 + 1) : ℕ) : ℝ) * (2 * 2 + 1 : ℕ) ≤
    8 * ((1 : ℝ) + 1) * (2 : ℝ) ^ 7 := by
  exact CollarScan.badHistory_prefactor_le (n := 2) (K := 2) (L := 2) (m := 2)
    (t := 4) (Ct := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- A fixed J suffices even for the small lookahead exponent 1/8.
example : (200 : ℝ) + 8 ≤ (1 / 8 / 2) * (3328 : ℕ) := by norm_num
example : ¬ ((200 : ℝ) + 8 ≤ (1 / 8 / 2) * (3327 : ℕ)) := by norm_num

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.geometricBadTail_le_power'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.geometricBadTail_le_power

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.badChargeRatio_le_radius_cube'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.badChargeRatio_le_radius_cube

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.eventually_badHistory_bound_le_rpow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_badHistory_bound_le_rpow

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.eventually_bad_history_probability_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_bad_history_probability_le
