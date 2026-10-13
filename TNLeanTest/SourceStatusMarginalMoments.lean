/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceStatusMarginalMoments

/-!
# Source-scale status moment signatures and rounding edge cases

The exact signature fixes coefficient order and retains all quantitative
conclusions for one vector. The scalar tests distinguish a zero denominator,
an insufficient collar and the positive-band threshold. The volume tests use
actual ambient rows and include the zero-width collar.
-/

set_option autoImplicit false

open Filter TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan SpectralFilter
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
namespace TNLeanTest.SourceStatusMarginalMoments

example (L : ℕ) : L / (8 * 0) = 0 := by simp

example {L m : ℕ} (hL : L < 8 * m) : L / (8 * m) = 0 :=
  Nat.div_eq_of_lt hL

example : (7 : ℕ) / (8 * 1) = 0 ∧ (8 : ℕ) / (8 * 1) = 1 := by norm_num

example (ell mu : ℝ) :
    ⌊(1 : ℝ) ^ (1 - ell)⌋₊ / (8 * ⌊(1 : ℝ) ^ mu⌋₊) = 0 := by norm_num

example {ell mu : ℝ} (hmu : 0 < mu) (hmuL : mu < 1 - ell) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * ⌊(n : ℝ) ^ mu⌋₊) :=
  eventually_one_le_source_bandCount hmu hmuL

example {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) {n L : ℕ} {C : ℝ} (hLn : L ≤ n)
    (hsize : (T.card : ℝ) ≤ C * (n : ℝ) ^ 2)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) :
    ((A.filter fun x ↦ ambientDepth T hT x.val ≤ L).card : ℝ) ≤
      (C + 1) * (n : ℝ) ^ 2 :=
  card_compact_collar_le_quadratic hT A hLn hsize hrows

example {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) {n : ℕ} {C : ℝ}
    (hsize : (T.card : ℝ) ≤ C * (n : ℝ) ^ 2) :
    ((A.filter fun x ↦ ambientDepth T hT x.val ≤ (0 : ℕ)).card : ℝ) ≤
      (C + 1) * (n : ℝ) ^ 2 := by
  apply card_compact_collar_le_quadratic hT A (Nat.zero_le n) hsize
  intro d hd hd0
  omega

example
    (R : ℕ) {J Δ Ct ell kappa mu : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCt : 0 ≤ Ct) (hell : 0 < ell)
    (hkappa : 0 < kappa) (hkm : kappa < mu) (hmuL : mu < 1 - ell) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ (q : ℕ) [NeZero q],
      ∃ CB : ℝ, 0 < CB ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
          (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ i, S.anchor i ∈ i.val) →
          ∀ L : ℕ, N ≤ S.n →
          L = ⌊(S.n : ℝ) ^ (1 - ell)⌋₊ →
          S.m = ⌊(S.n : ℝ) ^ mu⌋₊ →
          S.D = ⌈(S.n : ℝ) ^ kappa⌉₊ →
          S.K = L / (8 * S.m) →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          (T.card : ℝ) ≤ Ct * (S.n : ℝ) ^ 2 →
          (∀ d : ℕ, 1 ≤ d → d ≤ L →
            (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          1 ≤ S.K ∧
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
  CollarScan.exists_source_statusMarginal_moment_bounds R hJ hΔ hCt hell hkappa hkm hmuL

end TNLeanTest.SourceStatusMarginalMoments
