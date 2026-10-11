/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation

/-!
# Common physical marginal inputs: signatures and edge cases

The exact existential statement keeps one ground vector and its quantitative
bounds. The finite-region checks include coincident and empty regions, while
the common-radius checks include negative u and equality of the two budgets.
The rounded scales are checked at a fixed positive exponent gap.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan SpectralFilter
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
namespace TNLeanTest.StatusMarginalInputs

example (depth : Fin 0 → ℤ) (σ : PhysicalPartition (Fin 0)) :
    statusMarginalRegions depth σ = {∅} := by
  simp [statusMarginalRegions, receiving, middle, positiveNear, positiveNearMiddle]

-- A full far side need not lie in the compact truncation set.
example : ¬ receiving (fun _ : Fin 2 ↦ some true) true ⊆ (∅ : Finset (Fin 2)) := by
  simp [receiving]

example : (receiving (fun _ : Fin 2 ↦ some true) true)ᶜ ⊆ (∅ : Finset (Fin 2)) := by
  simp [receiving]

-- These five named regions have only two distinct values at this status.
example : statusMarginalRegions (fun _ : Fin 2 ↦ (0 : ℤ)) (fun _ ↦ some true) =
    {∅, Finset.univ} := by
  simp [statusMarginalRegions, receiving, middle, positiveNear, positiveNearMiddle]

example {V : Type*} [Fintype V] [DecidableEq V]
    (depth : V → ℤ) (σ : PhysicalPartition V) :
    receiving σ false ∈ statusMarginalRegions depth σ ∧
    receiving σ true ∈ statusMarginalRegions depth σ ∧
    middle σ ∈ statusMarginalRegions depth σ ∧
    positiveNear depth σ ∈ statusMarginalRegions depth σ ∧
    positiveNearMiddle depth σ ∈ statusMarginalRegions depth σ := by
  classical
  simp [statusMarginalRegions]

example {ϑ B : ℝ} (hϑ : 0 ≤ ϑ) (hB : 0 < B) :
    Entropy.tailRadius ϑ B ≤ Entropy.tailRadius ϑ B :=
  tailRadius_antitone_budget hϑ hB le_rfl

example {ϑ B B' u : ℝ} (hϑ : 0 ≤ ϑ) (hB : 0 < B) (hBB' : B ≤ B')
    (hu : |u| ≤ Entropy.tailRadius ϑ B') :
    |-u| ≤ Entropy.tailRadius ϑ B := by
  rw [abs_neg]
  exact hu.trans (tailRadius_antitone_budget hϑ hB hBB')

example : 8 * (37 / (8 * 0)) * 0 ≤ (37 : ℕ) := eight_mul_bandCount_mul_le 37 0

example : ∀ᶠ n : ℕ in Filter.atTop,
    let L := ⌊(n : ℝ) ^ (1 - (1 / 10 : ℝ))⌋₊
    let m := ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊
    let D := ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊
    let K := L / (8 * m)
    2 ≤ n ∧ roundedLogRadius 3 n ≤ D ∧ 1 ≤ D ∧ 4 * D ≤ m ∧ 8 * K * m ≤ L :=
  eventually_status_scale_separation (by norm_num) (by norm_num) (by norm_num)

-- Exact quantifier order and quantitative same-vector conclusions.
example
    (R : ℕ) {J Δ Ccard : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCcard : 0 ≤ Ccard) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q],
      ∃ CB : ℝ, 0 < CB ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
          (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ i, S.anchor i ∈ i.val) →
          ∀ L : ℕ, 2 ≤ S.n →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          ((S.truncationSet L).card : ℝ) ≤ Ccard * (S.n : ℝ) ^ 2 →
          S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
          (∀ d : ℕ, 1 ≤ d → d ≤ L →
            (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
          0 < C₀ ∧ 0 < c₀ ∧
          ∃ (e : ℝ) (Ωt : StateSpace Λ q) (B : ℝ),
            1 ≤ B ∧ B ≤ CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) ∧
            IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
            0 ≤ e ∧ e ≤ ε ∧
            (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
            Matrix.traceDistance
                (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
                (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
              Real.sqrt (2 * ε / g) ∧
            ∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
              (k ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (Entropy.surprisalMoment
                      (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                      u * regionalEntropy Λ q Ωt Q + C₀ * B * u ^ 2) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (Entropy.surprisalMoment
                      (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                      u * regionalEntropy Λ q Ωt Q + C₀ * B * u ^ 2) :=
  CollarScan.exists_truncated_statusMarginal_moment_bounds R hJ hΔ hCcard

end TNLeanTest.StatusMarginalInputs
