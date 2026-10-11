/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TargetTypicalWindow

/-! Regression tests for the source target window of one actual truncated vector. -/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option autoImplicit false

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

-- Constants precede every physical instance, scanner and source exponent choice.
-- All-cut estimates and quantitative physical bounds share the target-window witness.
example {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr C_B : ℝ, 0 < Ctr ∧ 0 < C_B ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : StateSpace Λ q) (F : ScannerExponents)
        (T : Finset (ℤ × ℤ)) (hT : T.Nonempty),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) → N ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ d : ℕ, 1 ≤ d → d ≤ F.L S.n →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        let L := F.L S.n
        let X := S.A.filter fun x ↦ x.val ∈ T
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
        let δ := (S.n : ℝ) ^ (-100 : ℝ)
        let B : Finset (Site Λ) → ℝ :=
          fun Y => cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Y
        ((S.truncationSet L).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
        X ⊆ S.truncationSet L ∧ (edgeBoundary Λ X).card ≤ 4 * S.n ∧
        ∃ (e : ℝ) (Ωt : StateSpace Λ q),
          IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
          0 ≤ e ∧ e ≤ ε ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) ∧
          (∀ (Y : Finset (Site Λ)) (u : ℝ),
            |u| ≤ Entropy.tailRadius (2 / g) (B Y) →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Y).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Y +
                512 * Real.exp 1 * (2 / g) * B Y * u ^ 2) ∧
          (∀ (Y : Finset (Site Λ)) (v : ℝ),
            Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt Y).eigenvalues
              (regionalEntropy Λ q Ωt Y) v ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(v / (32 * Real.sqrt ((1 + 2 / g) * B Y)))))) ∧
          B X ≤ C_B * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
          Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
            (regionalEntropy Λ q Ωt X) w ≤ δ ∧
          let p := (reducedState_isHermitian Λ q Ωt X).eigenvalues
          let E := Entropy.typicalSet p (regionalEntropy Λ q Ωt X) w
          let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
          0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
            ∀ i ∈ E, 0 < p i ∧
              Real.exp (-regionalEntropy Λ q Ωt X - w) ≤ p i ∧
              p i ≤ Real.exp (-regionalEntropy Λ q Ωt X + w) :=
  exists_truncated_target_typical_window hq R hJ hΔ hC_T

-- The exact source floor, including its positive lower bound, needs no scale-facts input.
example (F : ScannerExponents) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ ∧ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ ≤ n :=
  F.one_le_L_le hn

-- Singular marginals retain only positive eigenvalues, and the same canonical set
-- is nonempty with mass at least 1 - δ. No full-rank premise is allowed.
example {Λ : Finset (ℤ × ℤ)} {q : ℕ} (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1)
    (X : Finset (Site Λ)) {w δ : ℝ}
    (htail : Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
      (regionalEntropy Λ q Ωt X) w ≤ δ) (hδ : δ < 1) :
    let p := (reducedState_isHermitian Λ q Ωt X).eigenvalues
    let E := Entropy.typicalSet p (regionalEntropy Λ q Ωt X) w
    E.Nonempty ∧
      1 - δ ≤ (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E ∧
      (∀ i, p i = 0 → i ∉ E) ∧
      ∀ i ∈ E, Real.exp (-regionalEntropy Λ q Ωt X - w) ≤ p i ∧
        p i ≤ Real.exp (-regionalEntropy Λ q Ωt X + w) := by
  obtain ⟨_, hz, _, _, hE, hwindow⟩ := target_typicalSet_bounds Ωt hΩt X htail hδ
  refine ⟨hE, hz, ?_, fun i hi ↦ (hwindow i hi).2⟩
  intro i hi hmem
  have hpos := (hwindow i hmem).1
  rw [hi] at hpos
  exact (lt_irrefl 0) hpos

end TNLean.PEPS.AreaLaw.Scan.CollarScan
