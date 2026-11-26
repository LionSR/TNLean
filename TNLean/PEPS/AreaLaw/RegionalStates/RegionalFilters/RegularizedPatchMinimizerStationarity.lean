/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegionalStates.RegionalFilters.RegularizedPatchListCoordinates
import QICLean.Analysis.FunctionalCalculus.ShiftedDensityCommutation
import TNLean.PEPS.AreaLaw.RegionalStates.RegionalFilters.RegularizedPatchRadiusDerivative
import QICLean.Entropy.VonNeumann.SpectralTail
import TNLean.PEPS.AreaLaw.RegionalStates.RegionalFilters.RegularizedPatchMinimum
import QICLean.Analysis.Real.MinimumEnvelope

/-!
# Stationarity of the original indexed patch minimum

At a feasible minimum of the original ordered norm objective, each defining
density commutes with the corresponding marginal of the same normalized final
output. That marginal is bounded above by the density plus the positive scalar
shift. The regularized inverse-power filter therefore also commutes with it.

The result uses the existing stationarity theorem after the canonical
identification with an ordered list. Every region occurrence is retained,
including repeated regions. The input vector is arbitrary and may vanish.
Local coordinates are `Fin (n v)`; transport to other finite coordinate types
is a separate use of the sitewise coordinate isometries.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, Proposition 4.1, `03-patches.tex`, lines 68–99
and 130–205, `eq:patch-stationarity-commutation` and `eq:patch-kkt`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The logarithmic radius derivative at an original patch minimum

For a fixed minimizing density tuple, the original logarithmic objective has
the canonical marginal derivative at the radius where the tuple minimizes.
The commutations used in the ordered trace calculation follow from that minimum.
No choice of a family of minimizers is differentiated.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 453–466; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TNLean.PEPS.trace_regularizedPatchRegulator_le_quarter_of_isMinOn`: the regulator trace at an
  actual regularized patch minimum.
* `TNLean.PEPS.log_regularizedPatchMinimum_exp_neg_le_of_regulator_trace`,
  `TNLean.PEPS.log_regularizedPatchMinimum_exp_neg_le_of_entropy_distance`: growth of the original
  patch minimum from its regulator bound.
-/

section RegularizedPatchMinimizerStationarity

section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- Stationarity of the actual indexed norm minimum gives commutation and
density order for the marginal of the same normalized output.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 130–205. -/
theorem normalizedRegularizedPatchMarginal_stationarity_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    ∀ j : Fin m,
      Commute (x j)
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a b Ω x (regions j)) ∧
        normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
          regions a b Ω x (regions j) ≤ x j + b • 1 := by
  let f : Fin m → Entropy.PatchFactor n := fun j ↦ ⟨regions j, a j, x j⟩
  let l := regularizedPatchFactorList regions a x
  have hindex {g : Entropy.PatchFactor n} (hg : g ∈ l) : ∃ j, f j = g :=
    List.mem_ofFn.mp (List.mem_reverse.mp hg)
  have hmem (j : Fin m) : f j ∈ l :=
    List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hexp : ∀ g ∈ l, 0 < g.exponent := by
    intro g hg
    obtain ⟨j, rfl⟩ := hindex hg
    exact ha j
  have hden : ∀ g ∈ l, g.density.PosSemidef ∧ g.density.trace = 1 := by
    intro g hg
    obtain ⟨j, rfl⟩ := hindex hg
    exact hx j
  have hnest : l.Pairwise (fun g g' ↦ g'.region ⊆ g.region) := by
    change ((List.ofFn f).reverse).Pairwise _
    exact List.pairwise_reverse.mpr
      (List.pairwise_ofFn.mpr fun i j hij ↦ hnested hij.le)
  have hminList := isPatchMinimizer_regularizedPatchFactorList regions a b Ω x hmin
  intro j
  simpa only [f, normalizedRegularizedPatchMarginal_eq_regionState_patchState] using
    Entropy.patch_stationarity hb hexp hden hnest hminList (f j) (hmem j)

/-- Every original inverse-power filter commutes with its marginal at the
same feasible minimum, without a nonvanishing-input assumption.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 130–168. -/
theorem commute_filter_normalizedRegularizedPatchMarginal_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    ∀ j : Fin m,
      Commute ((x j + b • 1) ^ (-(a j) / 2))
        (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
          regions a b Ω x (regions j)) := by
  intro j
  exact ((hx j).1.commute_add_smul_one_rpow_iff hb
    (div_ne_zero (neg_ne_zero.mpr (ha j).ne') (by norm_num))).mpr
    (normalizedRegularizedPatchMarginal_stationarity_of_isMinOn
      regions hnested a ha hb Ω x hx hmin j).1

end TNLean.PEPS

end

section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The fixed minimizing tuple has the stated full radius derivative.
All filter commutations are derived from the same actual norm minimum.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 453–466. -/
theorem hasDerivAt_log_regularizedPatchObjective_exp_neg_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (hΩ : ‖Ω‖ = 1)
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) (R : ℝ)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    HasDerivAt
      (fun r : ℝ ↦ Real.log
        (regularizedPatchObjective (Out := fun v ↦ Fin (n v))
          regions a (Real.exp (-r)) Ω x))
      (∑ j, (a j / 2) *
        (Matrix.trace
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-R)) Ω x (regions j) *
            (Real.exp (-R) • (x j + Real.exp (-R) • 1) ^ (-1 : ℝ)))).re) R := by
  have houter : ∀ j k : Fin m, j < k →
      Commute ((x k + Real.exp (-R) • 1) ^ (-(a k) / 2))
        (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
          regions a (Real.exp (-R)) Ω x (regions k)) := by
    intro _j k _hjk
    exact commute_filter_normalizedRegularizedPatchMarginal_of_isMinOn
      regions hnested a ha (Real.exp_pos (-R)) Ω x hx hmin k
  exact hasDerivAt_log_regularizedPatchObjective_exp_neg_of_outer_commute
    (Out := fun v ↦ Fin (n v))
    regions hnested a (fun j ↦ (ha j).le) Ω hΩ x hx R houter

end TNLean.PEPS

end

end RegularizedPatchMinimizerStationarity

section RegularizedPatchActualRegulatorTrace

/-!
## The regulator trace at an actual regularized patch minimum

The entropy bound concerns the original input marginal, and the distance bound
compares that marginal with the same normalized minimizing output. Stationarity
is derived from the stated original norm minimum. The canonical spectral
projection remains the original marginal's projection; it need not commute with
the minimizing output or its regulator.

This is an auxiliary implication under the explicit entropy and marginal-distance
bounds. A physical application must derive those bounds from the area law and
the original Hamiltonian gap. This statement does not assume or establish a
physical area-law or gap theorem.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 362–418,
`eq:patch-constant-tail` and `eq:patch-regulator-trace`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

/-- The original-state entropy and distance bounds control the regulator for
arbitrary finite matrices, without commutation of the spectral projection.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 362–418. -/
private theorem trace_shiftedRegulator_le_quarter_of_entropy_distance
    {ι : Type*} [Fintype ι] [DecidableEq ι] {x ρ σ : Matrix ι ι ℂ}
    (hx : x.PosSemidef) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (hcomm : Commute ρ x)
    {C u R : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (hR : (16 * C + Real.log 8) * (1 + u) ≤ R)
    (hS : _root_.vonNeumannEntropy σ hσ.isHermitian ≤ C * (1 + u))
    (hd : (CFC.abs (ρ - σ)).trace.re ≤ 1 / 16)
    (hρx : ρ ≤ x + Real.exp (-R) • (1 : Matrix ι ι ℂ)) :
    (Real.exp (-R) •
      (ρ * (x + Real.exp (-R) • (1 : Matrix ι ι ℂ))⁻¹)).trace.re ≤ 1 / 4 := by
  have hspec := hσ.spectralProjectionGE_exp_entropy_bounds hσ1
    (mul_pos hC (by linarith)) (by norm_num : (0 : ℝ) < 16) hS
  let Q := Matrix.spectralProjectionGE σ (Real.exp (-16 * (C * (1 + u))))
  have hQ : IsStarProjection Q :=
    hσ.isHermitian.isStarProjection_spectralProjectionGE _
  have hσtail : ((1 - Q) * σ).trace.re ≤ 1 / 16 := hspec.2
  have hdist : Matrix.traceDistance ρ σ ≤ 1 / 32 := by
    change (CFC.abs (ρ - σ)).trace.re / 2 ≤ 1 / 32
    have hd' : (CFC.abs (ρ - σ)).trace.re ≤ 1 / 16 := hd
    linarith
  have htail : ((1 - Q) * ρ).trace.re ≤ 1 / 8 := by
    have ht := Matrix.re_trace_mul_sub_le_traceDistance hρ.isHermitian hσ.isHermitian
      (hρ1.trans hσ1.symm) hQ.one_sub.nonneg (sub_le_self _ hQ.nonneg)
    linarith
  exact hx.trace_shiftedRegulator_le_quarter hρ hcomm hu hR hρx hQ
    (by simpa only [mul_assoc] using hspec.1) htail

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The canonical regulator of an actual feasible minimum has trace at most
one quarter, provided the original marginal entropy and its full trace-norm
distance to the same normalized output obey the displayed source bounds.
Stationarity and the density order must be derived from the minimum; neither
is a caller hypothesis. Source: polynomial-PEPS `03-patches.tex`, lines 362–418. -/
theorem trace_regularizedPatchRegulator_le_quarter_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (hΩ : ‖Ω‖ = 1) {C u R : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (hR : (16 * C + Real.log 8) * (1 + u) ≤ R)
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x)
    (j : Fin m) :
    let ρ : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ :=
      normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω x (regions j)
    let σ : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ :=
      ManyBody.regionState (Ω) (regions j)
    _root_.vonNeumannEntropy σ
        (ManyBody.regionState_posSemidef (regions j)
          (Ω)).isHermitian ≤ C * (1 + u) →
      (CFC.abs (ρ - σ)).trace.re ≤ 1 / 16 →
      (Real.exp (-R) •
        (ρ *
            (x j + Real.exp (-R) •
            (1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
          (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ))⁻¹)).trace.re ≤ 1 / 4 := by
  intro ρ σ hS hd
  have hρ : ρ.PosSemidef :=
    normalizedRegularizedPatchMarginal_posSemidef (Out := fun v ↦ Fin (n v))
      regions a (Real.exp (-R)) Ω x (regions j)
  have hρ1 : ρ.trace = 1 :=
    trace_normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v)) regions a
      (fun k ↦ (ha k).le) (Real.exp_pos (-R)) Ω hΩ hx (regions j)
  have hσ : σ.PosSemidef :=
    ManyBody.regionState_posSemidef (regions j) (Ω)
  have hσ1 : σ.trace = 1 := by
    dsimp only [σ]
    rw [ManyBody.trace_regionState, hΩ]
    norm_num
  obtain ⟨hcomm, hle⟩ := normalizedRegularizedPatchMarginal_stationarity_of_isMinOn
    regions hnested a ha (Real.exp_pos (-R)) Ω x hx hmin j
  have hcomm' : Commute ρ (x j) := hcomm.symm
  have hle' : ρ ≤ x j + Real.exp (-R) •
      (1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ) := hle
  exact trace_shiftedRegulator_le_quarter_of_entropy_distance
    (ι := (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))) (x := x j) (ρ := ρ) (σ := σ)
    (hx j).1 hρ hσ hρ1 hσ1 hcomm' hC hu hR hS hd hle'

end TNLean.PEPS

end RegularizedPatchActualRegulatorTrace

section RegularizedPatchMinimumGrowth

/-!
## Growth of the original patch minimum from its regulator bound

The logarithm of the original minimum is continuous. At each radius, one
attained minimizing tuple supplies a contacting branch whose derivative is
bounded by the regulator traces. A one-sided comparison then bounds the growth
without choosing a continuous or differentiable family of minimizing tuples.

The regulator trace bound is an explicit premise of this auxiliary theorem.
A physical application must derive it for the same minimizing outputs from the
original-state entropy and the Hamiltonian gap. This theorem alone is not the
physical patch-approximation theorem.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 421–481,
`eq:patch-minimum-growth`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The source growth estimate follows once the quarter-regulator estimate
holds for every original minimizer on the interval. This is an auxiliary
implication with an explicit regulator premise.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 453–481. -/
theorem log_regularizedPatchMinimum_exp_neg_le_of_regulator_trace
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (hΩ : ‖Ω‖ = 1) {Rstart R : ℝ} (hstart : 0 ≤ Rstart) (hR : Rstart ≤ R)
    (hreg : ∀ r ∈ Ico Rstart R,
      ∀ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions,
      IsMinOn (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω)
        (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x →
      ∀ j : Fin m,
        (Real.exp (-r) •
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-r)) Ω x (regions j) *
            (x j + Real.exp (-r) • 1)⁻¹)).trace.re ≤ 1 / 4) :
    Real.log (regularizedPatchMinimum (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω) ≤
      (∑ j, a j) / 2 * (Rstart + R / 4) := by
  let κ : ℝ := ∑ j, a j
  let f := fun r x ↦ Real.log
    (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω x)
  let g := fun r ↦ Real.log
    (regularizedPatchMinimum (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω)
  have ha0 (j : Fin m) : 0 ≤ a j := (ha j).le
  have hg : Continuous g :=
    continuous_log_regularizedPatchMinimum_exp_neg (Out := fun v ↦ Fin (n v)) regions a ha0 Ω hΩ
  have hle : ∀ r ∈ Icc Rstart R,
      ∀ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions, g r ≤ f r x := by
    intro r _hr x hx
    exact (isLeast_log_regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a ha0
      (Real.exp_pos (-r)) Ω hΩ).2 (mem_image_of_mem _ hx)
  have hcontact : ∀ r ∈ Ico Rstart R,
      ∃ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions,
      ∃ d : ℝ, f r x = g r ∧
        HasDerivWithinAt (fun z ↦ f z x) d (Ici r) r ∧ d ≤ κ / 8 := by
    intro r hr
    obtain ⟨x, hx, hmin⟩ :=
      exists_isMinOn_regularizedPatchObjective (Out := fun v ↦ Fin (n v))
        regions a (Real.exp_pos (-r)) Ω hΩ
    have hder := hasDerivAt_log_regularizedPatchObjective_exp_neg_of_isMinOn
      regions hnested a ha Ω hΩ x hx r hmin
    refine ⟨x, hx, _, congrArg Real.log
      (regularizedPatchObjective_eq_minimum (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-r)) Ω hx hmin),
      hder.hasDerivWithinAt, ?_⟩
    have hterm (j : Fin m) :
        (Matrix.trace
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-r)) Ω x (regions j) *
            (Real.exp (-r) • (x j + Real.exp (-r) • 1) ^ (-1 : ℝ)))).re ≤ 1 / 4 := by
      rw [← CFC.inverse_eq_rpow_neg_one
        ((hx j).1.add_smul_one_posDef (Real.exp_pos (-r))).isStrictlyPositive,
        ← Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_smul]
      exact hreg r hr x hx hmin j
    calc
      _ ≤ ∑ j : Fin m, (a j / 2) * (1 / 4) :=
        Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hterm j) (div_nonneg (ha0 j) (by norm_num))
      _ = κ / 8 := by
        rw [← Finset.sum_mul, ← Finset.sum_div]
        ring
  have hgrowth := lower_envelope_le_affine_of_hasDerivWithinAt
    hg.continuousOn hle hcontact (r := R) ⟨hR, le_rfl⟩
  have hinit : g Rstart ≤ Rstart * κ / 2 := by
    have hn := (regularizedPatchMinimum_exp_bounds (Out := fun v ↦ Fin (n v))
      regions a ha0 hstart Ω hΩ).2
    have hl := Real.log_le_log
      (regularizedPatchMinimum_pos (Out := fun v ↦ Fin (n v))
        regions a ha0 (Real.exp_pos (-Rstart)) Ω hΩ) hn
    simpa only [Real.log_exp] using hl
  have hκ : 0 ≤ κ := Finset.sum_nonneg (fun j _ ↦ ha0 j)
  change g R ≤ κ / 2 * (Rstart + R / 4)
  nlinarith [mul_nonneg hκ hstart]

/-- The original-marginal entropy and full trace-norm distance estimates imply
the source growth bound for the same actual minimum. These two estimates are
explicit premises of this auxiliary implication; a physical application must
derive them from the original area law and Hamiltonian gap.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 362–481. -/
theorem log_regularizedPatchMinimum_exp_neg_le_of_entropy_distance
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (hΩ : ‖Ω‖ = 1) {C u R : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (hR : (16 * C + Real.log 8) * (1 + u) ≤ R)
    (hS : ∀ j : Fin m, _root_.vonNeumannEntropy
      (ManyBody.regionState (Ω) (regions j))
      (ManyBody.regionState_posSemidef (regions j)
        (Ω)).isHermitian ≤ C * (1 + u))
    (hd : ∀ r ∈ Ico ((16 * C + Real.log 8) * (1 + u)) R,
      ∀ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions,
      IsMinOn (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω)
        (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x →
      ∀ j : Fin m, (CFC.abs
        (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-r)) Ω x (regions j) -
          ManyBody.regionState (Ω) (regions j))).trace.re ≤
        1 / 16) :
    Real.log (regularizedPatchMinimum (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω) ≤
      (∑ j, a j) / 2 * ((16 * C + Real.log 8) * (1 + u) + R / 4) := by
  have hstart : 0 ≤ (16 * C + Real.log 8) * (1 + u) :=
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hC.le)
      (Real.log_nonneg (by norm_num))) (by linarith)
  apply log_regularizedPatchMinimum_exp_neg_le_of_regulator_trace
    regions hnested a ha Ω hΩ hstart hR
  intro r hr x hx hmin j
  exact trace_regularizedPatchRegulator_le_quarter_of_isMinOn
    regions hnested a ha Ω hΩ hC hu hr.1 x hx hmin j (hS j) (hd r hr x hx hmin j)

end TNLean.PEPS

end RegularizedPatchMinimumGrowth
