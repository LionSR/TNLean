/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap
import TNLean.PEPS.AreaLaw.Scan.BoxClearanceComparison
import TNLean.PEPS.AreaLaw.Geometry.CellCounting

/-!
# The physical entropy bound for safe rectangles

For a gapped ground state of a finite-range Hamiltonian, the entropy in the
intersection of a cut with a safe rectangle of size r is at most C r^(1+e),
where e = 2/1000000. The constant depends only on the physical parameters and
is uniform over every real clearance greater than 2R+10, every finite domain,
Hamiltonian, ground state, cut, and rectangle.

The physical safe-box estimate at integer clearance 2R+11 gives an estimate at
clearance 2R+10 by subdivision into at most four rectangles. Every rectangle
with an admissible real clearance has this latter integer clearance.
The resulting pointwise estimate is the bound defining the safe-box supremum
in Proposition 9.5.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.5, `08-scanner.tex`, lines 681–689; the safety condition and
safe-box supremum are in `02-initial.tex`, lines 223–228 and 590–594,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The fixed-exponent safe-rectangle bound with an arbitrary real safety
parameter. The constant depends only on the physical parameters and is chosen
before every safety parameter, domain, Hamiltonian, state, cut, and rectangle.
Source: area-law Proposition 9.5, `08-scanner.tex`, lines 681–689; the safety
condition is `02-initial.tex`, lines 223–228, and the supremum over rectangles
is defined in lines 590–594, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This pointwise statement is the bound defining the source's safe-box supremum;
no second safety predicate or entropy supremum is introduced. -/
theorem exists_regionalEntropy_safe_rect_le_boxError
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D₀ : ℝ, 2 * (R : ℝ) + 10 < D₀ →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (A : Finset (Site Λ)) (Q : IntRect),
          (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
            D₀ * (Q.size : ℝ) < (supDist t z : ℝ)) →
          regionalEntropy Λ q Ω (rectRegion A Q) ≤
            C * (Q.size : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  obtain ⟨Cb, hCb, hbox⟩ := Scan.exists_boxEntropy_le_boxError q R hq hJ hΔ
  let d : ℕ := 2 * R + 10
  have hd : 3 ≤ d := by dsimp only [d]; omega
  have hp : 0 ≤ 1 + (Exponents.boxError : ℝ) := by
    norm_num [Exponents.boxError]
  have hweak := boxEntropy_power_le_of_succ_clearance
    (R := R) (D := d) (J := J) (Δ := Δ) (p := 1 + (Exponents.boxError : ℝ))
    hq hd hCb.le hp (hbox (d + 1) (by dsimp only [d]; omega))
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  refine ⟨4 * Cb + 4 * Real.log q + 1, by linarith, ?_⟩
  intro D₀ hD₀ Λ h E₀ Ω hgs A Q hclear
  have hdreal : (d : ℝ) < D₀ := by
    simpa only [d, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hD₀
  have hsafe : IsSafe Λ A d Q := by
    intro e he z hz t ht
    have hz' := Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary he hz
    have hreal := hclear t ht z.val hz'
    have hle : (d : ℝ) * (Q.size : ℝ) ≤ D₀ * (Q.size : ℝ) :=
      mul_le_mul_of_nonneg_right hdreal.le (Nat.cast_nonneg Q.size)
    have hcast : ((d * Q.size : ℕ) : ℝ) < (supDist t z.val : ℝ) := by
      simpa only [Nat.cast_mul] using hle.trans_lt hreal
    exact_mod_cast hcast
  exact regionalEntropy_le_of_boxEntropy_power (e := (Exponents.boxError : ℝ)) hq
    (by norm_num [Exponents.boxError]) hweak h hgs A Q hsafe

end TNLean.PEPS.AreaLaw
