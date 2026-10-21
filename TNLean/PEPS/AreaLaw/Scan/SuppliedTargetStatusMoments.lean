/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments

/-!
# Common status moments for a supplied truncated ground vector

The geometric coefficient is chosen before the physical system. The moment
estimates then apply to any supplied ground vector of the same truncated
Hamiltonian, at every completed and pre-charge status. Thus the vector chosen
by physical charge selection need not be chosen again.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Proposition 9.2, lines 386–391 and 400–414, and
`07-comparators.tex`, lines 70–85, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

/-- The actual geometric budgets give all sharp marginal moment estimates
for the supplied truncated ground vector. The geometric scale conditions
are explicit here and follow from the rounded scales in the scanner theorem.
Source: Proposition 9.2, `08-scanner.tex`, lines 386–391 and 400–414. -/
theorem exists_suppliedTarget_statusMarginal_moment_bounds
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ) {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
        (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
        S.graph = domainGraph Λ →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Cr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
        1 ≤ B ∧
          ∀ {J Δ : ℝ} (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q),
            0 < Δ → ‖Ω‖ = 1 →
            ∀ (e : ℝ) (Ωt : StateSpace Λ q),
              IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
                ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) →
              let g := Δ / positiveNormalization 1 (Δ / 2) J
              let C₀ := 512 * Real.exp 1 * (2 / g)
              let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
              0 < C₀ ∧ 0 < c₀ ∧
                ∀ (s : ℕ) (hist : History S.K S.m S.M s) (band : Fin S.K),
                  (s ≤ S.n * S.m →
                    ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                      ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                        Real.log (Entropy.surprisalMoment
                          (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                          u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2) ∧
                  (s + 1 ≤ S.n * S.m →
                    ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                      ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                        Real.log (Entropy.surprisalMoment
                          (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                          u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2) := by
  obtain ⟨CB, hCB, hbudget⟩ := exists_statusMarginal_cutBudget_le_log hq R hCr
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT S hgraph hdepth hanchor L hn hradius hr hDpos hD hL hrows hclear
  obtain ⟨hB, hcut⟩ := hbudget Λ T hT S hgraph hdepth hanchor L hn hradius
    hr hDpos hD hL hrows hclear
  refine ⟨hB, ?_⟩
  intro J Δ h Ω hΔ hΩ e Ωt hgs
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  refine ⟨by positivity, by positivity, ?_⟩
  intro s hist band
  exact ⟨fun hs Q hQ u hu ↦
    S.log_surprisalMoment_truncated_reducedState_le_common h Ω hgraph hanchor hΔ hΩ
      L hgs Q ((hcut s hist band).1 hs Q hQ) hu,
    fun hs Q hQ u hu ↦
      S.log_surprisalMoment_truncated_reducedState_le_common h Ω hgraph hanchor hΔ hΩ
        L hgs Q ((hcut s hist band).2 hs Q hQ) hu⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
