/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import QICLean.Entropy.Classical.ProbabilityEntropyRankTails
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.LowDensityAccurateViability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.LowDensityLogDimension
import QICLean.ManyBody.Entropy.ViableSubspaceEntropy
import QICLean.Probability.Sampling.ViableSubspaceMinimum
import QICLean.Analysis.Parameter.LowDensityCountParameters

/-!
# Dyadic entropy estimates for the degenerate gapped area law

Cubic logarithmic bounds on approximation ranks yield one integer dyadic
rank majorant. Combined with the finite-probability tail estimate, this
bounds entropy by the logarithm of the ground-space dimension with
coefficient one, plus an explicit cubic logarithmic remainder. A final
scalar estimate absorbs the finite remainder into one gap-dependent term.

The physical tail estimates are not hypotheses about a Hamiltonian in this
module: the statements are scalar and finite-probability implications.
They support ALVV, arXiv:1602.08828v2, the proof of `thm:al-dg`,
lines 1085–1099.

## Entropy in an original low-energy band

One fixed regional viable space for an outer original spectral band is
refined by the actual accurate interval families. Their image spaces control
tails of one fixed physical reduced state, with no spectral gap or invariance
assumption on the original band. Summing these actual tails gives coefficient
exactly one on the logarithm of the full-band dimension.

The constants are chosen before the physical data at each fixed positive
bandwidth. This is the entropy argument supporting ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105, and Proposition `prop:albootstrap-ld`,
lines 1107–1128. The sharper accuracy-dependent MPS rate is separate.

**Scope restriction (physical intervals and fixed bandwidth):** The statements
retain `q ≥ 2` and one coefficient for each fixed bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

## The regularized entropy bound for an original low-energy band

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

section

open scoped BigOperators

namespace Real

/-- Auxiliary to the entropy estimate in ALVV, arXiv:1602.08828v2,
proof of `thm:al-dg`, lines 1085–1087. Cubic logarithmic bounds at
dyadic numerical count bases admit one integer rank schedule. This is
a scalar statement and assumes no physical change of local dimension. -/
private theorem exists_cubic_dyadic_rank_majorant
    (q r : ℕ) (g K : ℝ) (D : ℕ → ℕ)
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hD : ∀ i, 1 ≤ D i)
    (hlogD : ∀ i, log (D i : ℝ) ≤
      K * (1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g)) ^ 3) :
    let u : ℝ := 1 + log (q : ℝ) + log (1 / g)
    ∃ B : ℕ, 1 ≤ B ∧
      (B : ℝ) ≤ 26 * K * u ^ 3 / log 2 + 2 ∧
      ∀ i : ℕ, r * D 0 ^ 24 * D i ^ 2 ≤
        r * 2 ^ (B * (i + 1) ^ 3) := by
  intro u
  have hlog2pos : 0 < log 2 := log_pos (by norm_num)
  have hlog2le : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogq : 0 ≤ log (q : ℝ) := log_natCast_nonneg q
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogbase (i : ℕ) : log ((q * 2 ^ i : ℕ) : ℝ) =
      log (q : ℝ) + (i : ℝ) * log 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      log_mul hqpos.ne' (by positivity), log_pow]
  have hscale (i : ℕ) :
      1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g) ≤
        u * ((i : ℝ) + 1) := by
    rw [hlogbase]
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    dsimp only [u] at hu ⊢
    nlinarith
  have hlogDi (i : ℕ) : log (D i : ℝ) ≤
      K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by
    calc
      log (D i : ℝ) ≤
          K * (1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g)) ^ 3 := hlogD i
      _ ≤ K * (u * ((i : ℝ) + 1)) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply pow_le_pow_left₀ _ (hscale i) 3
        linarith [log_natCast_nonneg (q * 2 ^ i)]
      _ = K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by ring
  let x : ℝ := 26 * K * u ^ 3 / log 2
  let B : ℕ := ⌈x⌉₊ + 1
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hBupper : (B : ℝ) ≤ x + 2 := by
    have hceil := (Nat.ceil_lt_add_one hx).le
    dsimp only [B]
    push_cast
    linarith
  have hcoef : 26 * K * u ^ 3 ≤ (B : ℝ) * log 2 := by
    have hxB : x ≤ (B : ℝ) := by
      have hceil := Nat.le_ceil x
      dsimp only [B]
      push_cast
      linarith
    exact (div_le_iff₀ hlog2pos).mp hxB
  refine ⟨B, hB, hBupper, ?_⟩
  intro i
  have hi : (1 : ℝ) ≤ ((i : ℝ) + 1) ^ 3 := by
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [hi0] : (1 : ℝ) ≤ (i : ℝ) + 1) 3
    simpa using h
  have hlog0 : log (D 0 : ℝ) ≤ K * u ^ 3 := by simpa using hlogDi 0
  have hbudget : 24 * log (D 0 : ℝ) + 2 * log (D i : ℝ) ≤
      (B : ℝ) * ((i : ℝ) + 1) ^ 3 * log 2 := by
    have hbase : K * u ^ 3 ≤ K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ K * u ^ 3)
    have hfinal := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ ((i : ℝ) + 1) ^ 3)
    nlinarith [hlogDi i]
  have hDpos (j : ℕ) : 0 < (D j : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (hD j))
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hr)
  have hlogs : log ((r * D 0 ^ 24 * D i ^ 2 : ℕ) : ℝ) ≤
      log ((r * 2 ^ (B * (i + 1) ^ 3) : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [log_mul (mul_pos hrpos (pow_pos (hDpos 0) _)).ne'
      (pow_pos (hDpos i) _).ne',
      log_mul hrpos.ne' (pow_pos (hDpos 0) _).ne',
      log_mul hrpos.ne' (by positivity), log_pow, log_pow, log_pow]
    push_cast
    nlinarith
  have hleftpos : 0 < ((r * D 0 ^ 24 * D i ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact mul_pos (mul_pos hrpos (pow_pos (hDpos 0) _)) (pow_pos (hDpos i) _)
  have hrightpos : 0 < ((r * 2 ^ (B * (i + 1) ^ 3) : ℕ) : ℝ) := by
    push_cast
    exact mul_pos hrpos (by positivity)
  have hreal := (log_le_log_iff hleftpos hrightpos).mp hlogs
  exact_mod_cast hreal

end Real

namespace Entropy

/-- Cubic logarithmic bounds on approximation ranks and dyadic probability
tails give an entropy estimate with coefficient one on the logarithm of the
ground-space rank. This is a pure finite-probability auxiliary for ALVV,
arXiv:1602.08828v2, proof of `thm:al-dg`, lines 1085–1087. The probability
tail bounds are inputs here; no physical tail estimate is asserted. -/
theorem probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    {N : ℕ} (q r : ℕ) (g K : ℝ) (D : ℕ → ℕ)
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hD : ∀ i, 1 ≤ D i)
    (hlogD : ∀ i, Real.log (D i : ℝ) ≤
      K * (1 + Real.log ((q * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3)
    (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (htail : ∀ i < N,
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * D 0 ^ 24 * D i ^ 2 ≤ a.val), p a) ≤ 1 / (2 : ℝ) ^ (i + 1)) :
    let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    probabilityEntropy p ≤ Real.log (r : ℝ) + 676 * K * u ^ 3 + 54 * Real.log 2 := by
  intro u
  obtain ⟨B, hB, hBupper, hmajor⟩ :=
    Real.exists_cubic_dyadic_rank_majorant q r g K D hq hr hg hg1 hK hD hlogD
  have htailB (i : ℕ) (hi : i < N) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val), p a) ≤ 1 / (2 : ℝ) ^ (i + 1) := by
    have hsubset :
        Finset.univ.filter (fun a : Fin N ↦ r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val) ⊆
        Finset.univ.filter (fun a : Fin N ↦ r * D 0 ^ 24 * D i ^ 2 ≤ a.val) := by
      intro a ha
      obtain ⟨hauniv, hlarge⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hauniv, (hmajor i).trans hlarge⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun a _ _ ↦ hp a)).trans (htail i hi)
  have hraw := probabilityEntropy_le_of_cubic_dyadic_rank_tail_bounds
    r B hr hB p hp hsum htailB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoefficient : (B : ℝ) * Real.log 2 ≤ 26 * K * u ^ 3 + 2 * Real.log 2 := by
    calc
      (B : ℝ) * Real.log 2 ≤
          (26 * K * u ^ 3 / Real.log 2 + 2) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hBupper hlog2.le
      _ = 26 * K * u ^ 3 + 2 * Real.log 2 := by
        rw [add_mul, div_mul_cancel₀ _ hlog2.ne']
  nlinarith only [hraw, hcoefficient]

end Entropy

namespace Real

/-- Absorb the finite dyadic entropy remainder into a uniform gap-dependent
coefficient. Auxiliary to ALVV, arXiv:1602.08828v2, entropy conclusion of
`thm:al-dg`, lines 1085–1087. -/
theorem dg_entropy_coefficient_bound
    (A g u S : ℝ) (r : ℕ) (hg : 0 < g) (hg1 : g ≤ 1) (hu : 1 ≤ u)
    (hS : S ≤ log (r : ℝ) +
      676 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g) * u ^ 3 +
        54 * log 2) :
    S ≤ log (r : ℝ) +
      ((14872 * (A + 1) * (6 + 2 * log (A + 1)) + 54) / g) * u ^ 3 := by
  have hlog2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hu3 : 1 ≤ u ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hu 3
  have hscale : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by linarith)
  have hsmall : 54 * log 2 ≤ (54 : ℝ) / g * u ^ 3 := by
    calc
      54 * log 2 ≤ 54 * 1 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ ≤ 54 * (u ^ 3 / g) := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = 54 / g * u ^ 3 := by ring
  calc
    S ≤ log (r : ℝ) +
        676 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g) * u ^ 3 +
          54 * log 2 := hS
    _ ≤ log (r : ℝ) +
        676 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g) * u ^ 3 +
          54 / g * u ^ 3 := add_le_add_right hsmall _
    _ = log (r : ℝ) +
        ((14872 * (A + 1) * (6 + 2 * log (A + 1)) + 54) / g) * u ^ 3 := by ring

end Real

end

section

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix

-- The original physical marginal is retained in its actual interval coordinates.
/-- Entropy of every unit vector in an original low-energy band, with explicit
capped-width costs and coefficient one on the full-band logarithmic dimension.
The constant-viable initial space is fixed before the accuracy choices. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_entropy_bound_capped
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Kb Cf : ℝ, 0 < Kb ∧ 100 ≤ Cf ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let b := min v (etaLD / 2)
      let g := min (b / 6) 1
      let m := q * ⌈Real.exp 100⌉₊
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        ManyBody.regionEntropy ψ J ≤ Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          Kb / (b / 2) * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 +
          14872 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1)) / g * u ^ 3 +
          54 * Real.log 2 := by
  classical
  obtain ⟨Kb, hKb, hinitial⟩ :=
    exists_fixed_bandwidth_interval_low_energy_viable_subspace_log_bound etaLD hLD
  obtain ⟨Cf, hCf, _hCfeta, hrefine⟩ :=
    exists_fixed_bandwidth_interval_low_energy_dyadic_refinement etaLD hLD
  refine ⟨Kb, Cf, hKb, hCf, ?_⟩
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  intro J G b g m u ψ hψG hψ
  let beta := fun _ : Fin L ↦ Fin q
  let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
    (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
  let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
    (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
    (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
  let EM := EuclideanSpace ℂ (J → Fin q)
  let EE := EuclideanSpace ℂ ({x // x ∉ J} → Fin q)
  have hb : 0 < b := lt_min hv (by positivity)
  have hbv : b ≤ v := min_le_left _ _
  have hbcap : b ≤ etaLD / 2 := min_le_right _ _
  have hw : 0 < b / 6 := by positivity
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hG {a c : ℝ} (hac : a ≤ c) : G a ≤ G c :=
    Submodule.spectralSpanLE_mono_cutoff hRaw.eigenvectorBasis hRaw.eigenvalues
      (by linarith only [hac])
  obtain ⟨W0, hWdim, hW0⟩ :=
    hinitial L q p r (b / 2) hq hpr hrL (by positivity) Φ h0 h1
  have hψupper : ψ ∈ G (etaLD - b / 2) :=
    hG (by linarith only [hbv, hb]) hψG
  have hupperne : (G (etaLD - b / 2)).map Tm.toLinearEquiv.toLinearMap ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨Tm ψ, ⟨ψ, hψupper, rfl⟩, ?_⟩
    intro hz
    have hn : ‖Tm ψ‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hψ
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hWne : W0 ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hW0 (by norm_num) hupperne
  have hr0 : 1 ≤ Module.finrank ℂ W0 := Submodule.one_le_finrank_iff.mpr hWne
  have hGne : G etaLD ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨ψ, hG (by linarith only [hv]) hψG, ?_⟩
    intro hz
    rw [hz, norm_zero] at hψ
    norm_num at hψ
  have hrank : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr hGne
  have hr0R : (0 : ℝ) < Module.finrank ℂ W0 := by
    exact_mod_cast (by omega : 0 < Module.finrank ℂ W0)
  have hrR : (0 : ℝ) < Module.finrank ℂ (G etaLD) := by
    exact_mod_cast (by omega : 0 < Module.finrank ℂ (G etaLD))
  have hlogInitial : Real.log (Module.finrank ℂ W0 : ℝ) ≤
      Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
        Kb / (b / 2) * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 := by
    have h := Real.log_le_log hr0R hWdim
    rwa [Real.log_mul hrR.ne' (Real.exp_ne_zero _), Real.log_exp] at h
  obtain ⟨hqm, hm, _hlogm, _hlogmup⟩ := Real.regularized_filter_count_base_bounds q hq
  let D : ℕ → ℕ := fun i ↦
    let mi := m * 2 ^ i
    let ui := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
    let ell : ℕ := ⌈Cf * ui ^ 2 / g⌉₊
    (mi * ell ^ 2) ^ (22 * ell)
  let Kf := 22 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1)) / g
  have hCf1 : 1 ≤ Cf := (by norm_num : (1 : ℝ) ≤ 100).trans hCf
  have hKf : 0 ≤ Kf := by
    have hlog := Real.log_nonneg (by linarith only [hCf] : 1 ≤ Cf + 1)
    dsimp only [Kf]
    positivity
  have hmi (i : ℕ) : 2 ≤ m * 2 ^ i :=
    hm.trans (Nat.le_mul_of_pos_right m (pow_pos (by decide) i))
  have hD (i : ℕ) : 1 ≤ D i := by
    obtain ⟨_, _, _, hDpos, _, _⟩ :=
      Real.polynomial_filter_count_bounds Cf (m * 2 ^ i) g hCf1 (hmi i) hg hg1
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hDpos.ne')
  have hlogD (i : ℕ) : Real.log (D i : ℝ) ≤
      Kf * (1 + Real.log ((m * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3 :=
    (Real.polynomial_filter_count_bounds Cf (m * 2 ^ i) g hCf1 (hmi i) hg hg1).2.2.2.2.2
  obtain ⟨hp, hsum, hentropy, htailOfViable⟩ :=
    Submodule.unit_cut_spectral_probability Tm (G (etaLD - v)) ψ hψG hψ
  let coord := (Submodule.euclideanTensorEquiv (J → Fin q) ({x // x ∉ J} → Fin q)).symm (Tm ψ)
  let Cψ := Matrix.schmidtCoeffMatrix (WithLp.ofLp coord)
  let hρ := Matrix.posSemidef_self_mul_conjTranspose Cψ
  let probability := hρ.isHermitian.eigenvalues₀
  have htail (i : ℕ) (_hi : i < Fintype.card (J → Fin q)) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin (Fintype.card (J → Fin q)) ↦
        Module.finrank ℂ W0 * D 0 ^ 24 * D i ^ 2 ≤ a.val), probability a) ≤
          1 / (2 : ℝ) ^ (i + 1) := by
    obtain ⟨_hell, _hlog, A, hA⟩ :=
      hrefine L q m p r i (b / 6) hq hqm hpr hrL hw Φ h0 h1
    have hbuffer : 6 * (b / 6) ≤ etaLD - b / 2 := by linarith only [hbcap, hb]
    obtain ⟨hdim, hV⟩ := hA (etaLD - b / 2) hbuffer (by linarith only [hb]) W0 hW0
    have hVraw : Submodule.IsViable (F := EE) (1 / (2 : ℝ) ^ (i + 1))
        (⨆ j : Fin (D i ^ 2), W0.map (A j).toLinearMap)
        ((G (etaLD - b)).map Tm.toLinearEquiv.toLinearMap) := by
      simpa only [show etaLD - b / 2 - 3 * (b / 6) = etaLD - b by ring] using hV
    have hVinner := hVraw.of_target_le
      (Submodule.map_mono (hG (a := etaLD - v) (c := etaLD - b)
        (by linarith only [hbv])))
    have hdim' : Module.finrank ℂ ↥(⨆ j : Fin (D i ^ 2), W0.map (A j).toLinearMap) ≤
        Module.finrank ℂ W0 * D 0 ^ 24 * D i ^ 2 := by
      calc
        _ ≤ D i ^ 2 * Module.finrank ℂ W0 := hdim
        _ = Module.finrank ℂ W0 * D i ^ 2 := Nat.mul_comm _ _
        _ ≤ _ := by
          have hp : 1 ≤ D 0 ^ 24 :=
            Nat.one_le_pow 24 (D 0) (lt_of_lt_of_le Nat.zero_lt_one (hD 0))
          have hmul := Nat.mul_le_mul_left (Module.finrank ℂ W0) hp
          simpa only [mul_one] using Nat.mul_le_mul_right (D i ^ 2) hmul
    have hdelta : (1 : ℝ) / 2 ^ (i + 1) < 1 := by
      apply (div_lt_one (by positivity)).mpr
      have hp : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      nlinarith only [hp]
    exact htailOfViable _ _ _ hdelta hdim' hVinner
  have hraw := Entropy.probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    m (Module.finrank ℂ W0) g Kf D hm hr0 hg hg1 hKf hD hlogD probability hp hsum htail
  have hactual := (Submodule.actualRegionSplit_marginal_and_entropy
    (n := fun _ : Fin L ↦ q) J ψ).2
  have hEntropy : ManyBody.regionEntropy ψ J ≤
      Real.log (Module.finrank ℂ W0 : ℝ) + 676 * Kf * u ^ 3 + 54 * Real.log 2 := by
    rw [← hactual, hentropy]
    exact hraw
  have hcoef : 676 * Kf * u ^ 3 =
      14872 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1)) / g * u ^ 3 := by
    dsimp only [Kf]
    ring
  rw [hcoef] at hEntropy
  linarith only [hEntropy, hlogInitial]

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

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
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        ManyBody.regionEntropy ψ J ≤ Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
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
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw J G ψ hψG hψ
  let : Nonempty (Fin L → Fin q) := config
  by_cases hveta : v ≤ etaLD
  · have hcap := hphysical L q p r v hq hpr hrL hv Φ h0 h1 ψ hψG hψ
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

end
