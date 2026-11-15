/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowDensityEntropy
import QICLean.Analysis.LowDensityEntropyParameters

/-!
# The regularized entropy bound for an original low-energy band

Every unit vector in a buffered original low-energy band has regional entropy
at most the logarithm of the full-band dimension, with coefficient one, plus
a regularized cubic logarithmic remainder. One constant is chosen at each
fixed bandwidth before the physical chain, local dimension, interval,
interactions, deficit and vector. All prescribed intervals are included.

This is the entropy conclusion supporting ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105. Substituting `v = mu / log L`
gives the source's low-density scale for `L ≥ 2`. The sharper MPS
approximation rate and a running-time estimate are separate.

**Scope restriction (nontrivial local dimension and fixed bandwidth):** The
statement retains `q ≥ 2` and the fixed-bandwidth quantifiers of Assumption
(LD), lines 281–284. See `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

-- The actual original spectral band and regional entropy remain in physical coordinates.
/-- An original low-energy unit vector satisfies the regularized entropy bound
on every interval. No spectral gap, supplied family, residual, sampling condition
or entropy premise is imposed. ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_entropy_bound
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        Entropy.regionEntropy J ψ ≤ Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          K / v * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / v)) ^ 3 := by
  classical
  obtain ⟨Kb, Cf, hKb, hCf, hphysical⟩ :=
    exists_fixed_bandwidth_interval_low_energy_entropy_bound_capped etaLD hLD
  let B := max 12 etaLD
  let F := 102 + Real.log B
  let P := 14872 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1))
  let K := 108 * Kb + P * B * F ^ 3 + 54 * etaLD
  have hK : 0 < K :=
    (Real.low_density_entropy_cost_le (eta := etaLD) (v := etaLD) (q := 2)
      hLD hLD le_rfl hKb hCf (by decide)).1
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw J G ψ hψG hψ
  let : Nonempty (Fin L → Fin q) := config
  by_cases hveta : v ≤ etaLD
  · have hcap := hphysical L q p r v hq hpr hrL hv h hs h0 h1 ψ hψG hψ
    have hcost := (Real.low_density_entropy_cost_le hLD hv hveta hKb hCf hq).2
    dsimp only at hcap hcost
    linarith only [hcap, hcost]
  · have hzero : G (etaLD - v) = ⊥ := by
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨j, hj, rfl⟩
      change hRaw.eigenvalues j ≤ minEigenvalue hRaw + (etaLD - v) at hj
      have hmin := minEigenvalue_le hRaw j
      have hvgt : etaLD < v := lt_of_not_ge hveta
      exact False.elim (by linarith only [hj, hmin, hvgt])
    have hz : ψ = 0 := by simpa only [hzero, Submodule.mem_bot] using hψG
    rw [hz, norm_zero] at hψ
    norm_num at hψ

end TNLean.MPS.AreaLaw
