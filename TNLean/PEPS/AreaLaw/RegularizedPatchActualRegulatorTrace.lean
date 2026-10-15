/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimizerStationarity
import QICLean.Entropy.RegionEntropy
import QICLean.Entropy.SpectralTail

/-!
# The regulator trace at an actual regularized patch minimum

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
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (hΩ : ‖Ω‖ = 1) {C u R : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (hR : (16 * C + Real.log 8) * (1 + u) ≤ R)
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x)
    (j : Fin m) :
    let ρ : Matrix (Entropy.RegionConfig n (regions j))
        (Entropy.RegionConfig n (regions j)) ℂ :=
      normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω x (regions j)
    let σ : Matrix (Entropy.RegionConfig n (regions j))
        (Entropy.RegionConfig n (regions j)) ℂ :=
      Entropy.regionState (regions j) (dependentGlobalConfigIsometry Ω)
    _root_.vonNeumannEntropy σ
        (Entropy.regionState_posSemidef (regions j)
          (dependentGlobalConfigIsometry Ω)).isHermitian ≤ C * (1 + u) →
      (CFC.abs (ρ - σ)).trace.re ≤ 1 / 16 →
      (Real.exp (-R) •
        (ρ * (x j + Real.exp (-R) • (1 : Matrix (Entropy.RegionConfig n (regions j))
          (Entropy.RegionConfig n (regions j)) ℂ))⁻¹)).trace.re ≤ 1 / 4 := by
  intro ρ σ hS hd
  have hρ : ρ.PosSemidef :=
    normalizedRegularizedPatchMarginal_posSemidef (Out := fun v ↦ Fin (n v))
      regions a (Real.exp (-R)) Ω x (regions j)
  have hρ1 : ρ.trace = 1 :=
    trace_normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v)) regions a
      (fun k ↦ (ha k).le) (Real.exp_pos (-R)) Ω hΩ hx (regions j)
  have hσ : σ.PosSemidef :=
    Entropy.regionState_posSemidef (regions j) (dependentGlobalConfigIsometry Ω)
  have hσ1 : σ.trace = 1 := by
    dsimp only [σ]
    rw [Entropy.trace_regionState, dependentGlobalConfigIsometry.norm_map, hΩ]
    norm_num
  obtain ⟨hcomm, hle⟩ := normalizedRegularizedPatchMarginal_stationarity_of_isMinOn
    regions hnested a ha (Real.exp_pos (-R)) Ω x hx hmin j
  have hcomm' : Commute ρ (x j) := hcomm.symm
  have hle' : ρ ≤ x j + Real.exp (-R) • (1 : Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) := hle
  exact trace_shiftedRegulator_le_quarter_of_entropy_distance
    (ι := Entropy.RegionConfig n (regions j)) (x := x j) (ρ := ρ) (σ := σ)
    (hx j).1 hρ hσ hρ1 hσ1 hcomm' hC hu hR hS hd hle'

end TNLean.PEPS
