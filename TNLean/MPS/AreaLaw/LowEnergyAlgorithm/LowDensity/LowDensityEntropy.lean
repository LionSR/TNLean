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
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.LongIntervalLowDensityFamily
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.LowDensityMinimumDimension
import QICLean.ManyBody.Entropy.ViableSubspaceEntropy
import QICLean.Probability.Sampling.ViableSubspaceMinimum
import QICLean.Analysis.Parameter.LowDensityCountParameters
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGViability
import QICLean.ManyBody.Entropy.RegionEntropyInequalities
import QICLean.ManyBody.Entropy.MovementEtaRegional
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_interval_entropy_bound`: regional entropy in the full
  ground space.
* `TNLean.MPS.AreaLaw.exists_fixed_bandwidth_interval_low_energy_entropy_bound_of_pos_dimension`:
  the low-energy entropy bound in every positive local dimension.
-/

section LowDensityEntropy

section

open scoped BigOperators

namespace Real

/-- Absorb the finite dyadic entropy remainder into a uniform gap-dependent
coefficient. Auxiliary to ALVV, arXiv:1602.08828v2, entropy conclusion of
`thm:al-dg`, lines 1085–1087. -/
theorem _root_.TNLean.MPS.AreaLaw.dg_entropy_coefficient_bound
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

end LowDensityEntropy

section PhysicalDGEntropy

/-!
## Regional entropy in the full ground space

For an original positive nearest-neighbour chain with a spectral gap,
every unit vector in its full ground space has bounded regional entropy
on each interval. The bound has coefficient one on the logarithm of the
ground-space dimension and one universal cubic logarithmic remainder.

The accuracy-dependent families and the constant-error bootstrap use the
same universal scalar choice. The actual vector and actual regional state
are retained, including at empty intervals. This establishes the entropy
conclusion only; no efficient construction or matrix product approximation
is asserted here. Supporting ALVV, arXiv:1602.08828v2, `thm:al-dg`,
lines 1048–1099.
-/

open ManyBody (interval)

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every unit vector in the full original ground space has a uniform entropy
bound at every actual interval. One universal constant is chosen before the
chain, Hamiltonian, gap, interval and vector. The entropy is that of the
original physical regional state; the proof uses its Schmidt coefficient
matrix in the fixed actual tensor coordinates.
Supporting the entropy conclusion of ALVV, arXiv:1602.08828v2,
`thm:al-dg`, lines 1048–1099. The accuracy-dependent families and the bootstrap
base use the same universal scale. No algorithmic or efficient matrix product
representation is asserted.

**Local fix (ground-space cutoff):** The original full ground space follows
the proof of `t:ais`; the cutoff and viability boundary are documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf. -/
theorem exists_physical_dg_interval_entropy_bound :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let J := interval L p r
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ManyBody.regionEntropy ψ J ≤ Real.log (Module.finrank ℂ G : ℝ) +
        Cbound / g * (1 + Real.log (q : ℝ) + Real.log (1 / g)) ^ 3 := by
  classical
  obtain ⟨A, hA, _hA21, hphysical⟩ :=
    exists_accuracy_physical_interval_family_and_bootstrap
  let cA : ℝ := 6 + 2 * Real.log (A + 1)
  let Cbound : ℝ := 14872 * (A + 1) * cA + 54
  have hA1 : 1 ≤ A + 1 := by linarith only [hA]
  have hcA : 0 < cA := by
    have hlog := Real.log_nonneg hA1
    dsimp only [cA]
    linarith only [hlog]
  have hAp : 0 < A + 1 := lt_of_lt_of_le zero_lt_one hA1
  have hC : 0 < Cbound := by
    dsimp only [Cbound]
    positivity
  refine ⟨Cbound, hC, ?_⟩
  intro L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma H hH
    hmu hnu hmunu hgap G g J ψ hψG hψ
  let beta := fun _ : Fin L ↦ Fin q
  let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
    (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
  let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
    (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
    (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
  let w := (Submodule.euclideanTensorEquiv (J → Fin q) ({v // v ∉ J} → Fin q)).symm (Tm ψ)
  let Cψ := Matrix.schmidtCoeffMatrix (WithLp.ofLp w)
  let hρ := Matrix.posSemidef_self_mul_conjTranspose Cψ
  let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let ellq : ℕ := ⌈A * u ^ 2 / g⌉₊
  let Dq : ℕ := (q * ellq ^ 2) ^ (22 * ellq)
  obtain ⟨_hDq, _hlogDq, W0, hWdim, hW0, haccuracy⟩ :=
    hphysical L q p r hpr hrL Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hq1 : 1 ≤ q := Nat.le_trans (by decide : 1 ≤ 2) hq
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hu : 1 ≤ u := by
    have hlogq := Real.log_nonneg hqR
    have hlogg := Real.log_nonneg ((one_le_div hg).2 hg1)
    dsimp only [u]
    linarith only [hlogq, hlogg]
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  let D : ℕ → ℕ := fun i ↦
    let m := q * 2 ^ i
    let ui : ℝ := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let elli : ℕ := ⌈A * ui ^ 2 / g⌉₊
    (m * elli ^ 2) ^ (22 * elli)
  have hDzero : D 0 = Dq := by
    simp only [D, pow_zero, mul_one, Dq, ellq, u]
  have hqm (i : ℕ) : q ≤ q * 2 ^ i :=
    Nat.le_mul_of_pos_right q (pow_pos (by decide : 0 < (2 : ℕ)) i)
  have hD (i : ℕ) : 1 ≤ D i := by
    obtain ⟨_hell, _hmD, hDi, _hlog, _hfamily⟩ := haccuracy (q * 2 ^ i) (hqm i)
    exact Nat.le_trans (by decide : 1 ≤ 2) hDi
  let K : ℝ := 22 * (A + 1) * cA / g
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hlogD (i : ℕ) : Real.log (D i : ℝ) ≤
      K * (1 + Real.log ((q * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3 := by
    obtain ⟨_hell, _hmD, _hDi, hlog, _hfamily⟩ := haccuracy (q * 2 ^ i) (hqm i)
    exact hlog
  obtain ⟨hp, hsum, hentropy, htail_of_viable⟩ :=
    Submodule.unit_cut_spectral_probability
      (σ := J → Fin q) (β := {v // v ∉ J} → Fin q) Tm G ψ hψG hψ
  let probability := hρ.isHermitian.eigenvalues₀
  have htail (i : ℕ) (_hi : i < Fintype.card (J → Fin q)) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin (Fintype.card (J → Fin q)) ↦
        Module.finrank ℂ G * D 0 ^ 24 * D i ^ 2 ≤ a.val), probability a) ≤
          1 / (2 : ℝ) ^ (i + 1) := by
    let m := q * 2 ^ i
    obtain ⟨_hell, hmD, _hDi, _hlog, Fops, T, Delta, hTG, hGT,
      _hdimT, _hDelta, hbudget, himprove⟩ := haccuracy m (hqm i)
    have hbase : Module.finrank ℂ W0 ≤ Module.finrank ℂ G * D 0 ^ 24 := by
      rw [hDzero]
      exact hWdim.le
    have hbudget' : (D i : ℝ) ^ 12 * Delta ≤ 0.00001 := by
      simpa only [show (0.00001 : ℝ) = 1 / 100000 by norm_num] using hbudget
    have hspan := Submodule.viable_enlargement_of_close_improving_target
      Tm G T W0 (Module.finrank ℂ G * D 0 ^ 24) m (D i) Delta
      (hq1.trans (hqm i)) hmD hW0 hbase hGT hTG Fops hbudget'
      (fun delta hdelta S hS ↦ himprove S delta hS hdelta)
    obtain ⟨hspanDim, hspanViable⟩ := hspan
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hq1.trans (hqm i))
    have hdelta : (1 / (2 * (m : ℝ)) : ℝ) < 1 := by
      apply (div_lt_one (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
      linarith only [hmR]
    have hmass := htail_of_viable (1 / (2 * (m : ℝ)))
      (⨆ j : Fin (D i ^ 2), W0.map (Fops j).toLinearMap)
      (Module.finrank ℂ G * D 0 ^ 24 * D i ^ 2) hdelta hspanDim hspanViable
    have hdenomNat : 2 ^ (i + 1) ≤ 2 * (q * 2 ^ i) := by
      rw [pow_succ]
      have hmul := Nat.mul_le_mul_right (2 ^ i) hq1
      nlinarith only [hmul]
    have hdenom : (2 : ℝ) ^ (i + 1) ≤ 2 * (m : ℝ) := by
      exact_mod_cast hdenomNat
    exact hmass.trans (div_le_div_of_nonneg_left (by norm_num)
      (pow_pos (by norm_num) (i + 1)) hdenom)
  have hraw := Entropy.probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    q (Module.finrank ℂ G) g K D hq hrG hg hg1 hK hD hlogD probability hp hsum htail
  have hrawEntropy : vonNeumannEntropy (Cψ * Cψᴴ) hρ.isHermitian ≤
      Real.log (Module.finrank ℂ G : ℝ) + 676 * K * u ^ 3 + 54 * Real.log 2 := by
    rw [hentropy]
    exact hraw
  have hcanonical := TNLean.MPS.AreaLaw.dg_entropy_coefficient_bound A g u
    (vonNeumannEntropy (Cψ * Cψᴴ) hρ.isHermitian) (Module.finrank ℂ G)
    hg hg1 hu hrawEntropy
  have hactual : vonNeumannEntropy (Cψ * Cψᴴ) hρ.isHermitian =
      ManyBody.regionEntropy ψ J :=
    (Submodule.actualRegionSplit_marginal_and_entropy (n := fun _ : Fin L ↦ q) J ψ).2
  rw [← hactual]
  exact hcanonical

end TNLean.MPS.AreaLaw

end PhysicalDGEntropy

section PositiveDimensionLowDensityEntropy

/-!
## The low-energy entropy bound in every positive local dimension

The physical construction for local dimension at least two is unchanged.
For a scalar local space, the regional dimension bound gives zero entropy
and hence the same estimate directly. This includes empty chains and all
prescribed intervals. Positive local dimension is the usual convention for
qudit chains, rather than an extra physical assumption.

The bandwidth is fixed before the physical data as in ALVV,
arXiv:1602.08828v2, Assumption (LD), lines 281–284. The conclusion is the
entropy part of Theorem `thm:al-ld`, lines 1096–1105.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The original-band entropy estimate includes the scalar local space.
ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_entropy_bound_of_pos_dimension
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 0 < q), p ≤ r → r ≤ L → 0 < v →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
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
  obtain ⟨K, hK, hactual⟩ := exists_fixed_bandwidth_interval_low_energy_entropy_bound etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv Φ h0 h1 config H hRaw J G ψ hψG hψ
  by_cases hq2 : 2 ≤ q
  · exact hactual L q p r v hq2 hpr hrL hv Φ h0 h1 ψ hψG hψ
  · have hq1 : q = 1 := by omega
    subst q
    have hzero : ManyBody.regionEntropy ψ J ≤ 0 := by
      simpa only [Nat.cast_one, Real.log_one, mul_zero] using
        ManyBody.regionEntropy_le_card_mul_log hψ J
    have hlogv : 0 ≤ Real.log (1 + 1 / v) :=
      Real.log_nonneg (by linarith only [one_div_pos.mpr hv])
    exact hzero.trans (add_nonneg (Real.log_natCast_nonneg _)
      (mul_nonneg (div_nonneg hK.le hv.le) (by
        simp only [Nat.cast_one, Real.log_one, add_zero]
        positivity)))

end TNLean.MPS.AreaLaw

end PositiveDimensionLowDensityEntropy
