/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.PrefixApproximation
import TNLean.PEPS.AreaLaw.Scan.FrontPrefixFamily
import TNLean.PEPS.AreaLaw.Geometry.TemplateEntropy

/-!
# Entropy of the actual positive terminal regions

The accepted actual-history prefix approximation and disjoint-union entropy
cost transfer one bound on the fixed positive-prefix family to both positive
regions of every completed or pre-charge terminal. The changed-site cost is
the literal `3nD log q`; no terminal entropy certificate is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 868--877, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals
open scoped symmDiff

private theorem abs_entropy_sub_le_of_nested
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    {R T : Finset (Site Λ)} (hRT : R ⊆ T) {b : ℕ}
    (hcard : (T ∆ R).card ≤ b) :
    |regionalEntropy Λ q Ω T - regionalEntropy Λ q Ω R| ≤
      (b : ℝ) * Real.log q := by
  classical
  have hunion : R ∪ (T \ R) = T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h ↦ h.elim (fun hx ↦ hRT hx) And.left,
      fun h ↦ by by_cases hx : x ∈ R <;> tauto⟩
  have hdiff : T \ R ⊆ T ∆ R := by
    intro x hx
    exact Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hx))
  have hc : (T \ R).card ≤ b := (Finset.card_le_card hdiff).trans hcard
  have h := abs_regionalEntropy_union_sub_le Λ q Ω hΩ R (T \ R)
    disjoint_sdiff_self_right
  rw [hunion] at h
  exact h.trans ((regionalEntropy_le_card_mul_log Λ q Ω hΩ (T \ R)).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Real.log_natCast_nonneg q)))

open Classical in
/-- A source bound on the fixed positive-depth prefixes controls both actual
positive terminal regions, uniformly in history and band. Source:
`08-scanner.tex`, lines 868--877. -/
theorem terminalPartition_positiveEntropy_le
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} {q : ℕ}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hn : 0 < S.n) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1) (Bsh : ℝ)
    (hsh : ∀ i : Fin (L + 1),
      regionalEntropy Λ q Ωt (positiveDepthPrefix S.A S.depth (i.val : ℤ)) ≤ Bsh)
    (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
    let σ := terminalPartition S (S.n * S.m) j g
    regionalEntropy Λ q Ωt (positiveNear S.depth σ) ≤
        Bsh + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log q ∧
      regionalEntropy Λ q Ωt (positiveNearMiddle S.depth σ) ≤
        Bsh + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log q := by
  classical
  intro σ
  have hpref : ∃ iN iF : Fin (L + 1),
      positiveDepthPrefix S.A S.depth (iN.val : ℤ) ⊆ positiveNear S.depth σ ∧
      positiveNearMiddle S.depth σ ⊆ positiveDepthPrefix S.A S.depth (iF.val : ℤ) ∧
      (positiveNear S.depth σ ∆ positiveDepthPrefix S.A S.depth (iN.val : ℤ)).card ≤
        3 * S.n * S.D ∧
      (positiveNearMiddle S.depth σ ∆ positiveDepthPrefix S.A S.depth (iF.val : ℤ)).card ≤
        3 * S.n * S.D := by
    dsimp only [σ, terminalPartition]
    cases j with
    | inl j =>
      obtain ⟨hnear, hfar, _, _, hnearCard, hfarCard⟩ :=
        S.state_prefix_approximation_domainGraph hT hgraph hdepth j.2 g hn
          (Nat.le_of_lt_succ j.1.isLt) hr hDpos hD hL hrows
      obtain ⟨⟨iN, hiN⟩, ⟨iF, hiF⟩⟩ :=
        S.front_positiveDepthPrefix_mem_fixed_family hn hL g (j.2.1 g) j.1.val
          (Nat.le_of_lt_succ j.1.isLt)
      exact ⟨iN, iF, by simpa only [hiN] using hnear, by simpa only [hiF] using hfar,
        by simpa only [hiN] using hnearCard, by simpa only [hiF] using hfarCard⟩
    | inr j =>
      obtain ⟨hnear, hfar, _, _, hnearCard, hfarCard⟩ :=
        S.oldChargeState_prefix_approximation_domainGraph hT hgraph hdepth j.2 g hn
          (Nat.succ_le_of_lt j.1.isLt) hr hDpos hD hL hrows
      obtain ⟨⟨iN, hiN⟩, ⟨iF, hiF⟩⟩ :=
        S.front_positiveDepthPrefix_mem_fixed_family hn hL g (j.2.1 g) (j.1.val + 1)
          (Nat.succ_le_of_lt j.1.isLt)
      exact ⟨iN, iF, by simpa only [hiN] using hnear, by simpa only [hiF] using hfar,
        by simpa only [hiN] using hnearCard, by simpa only [hiF] using hfarCard⟩
  obtain ⟨iN, iF, hnear, hfar, hnearCard, hfarCard⟩ := hpref
  have hN := (abs_le.mp (abs_entropy_sub_le_of_nested Ωt hΩt hnear hnearCard)).2
  have hF := (abs_le.mp (abs_entropy_sub_le_of_nested Ωt hΩt hfar
    (by simpa only [symmDiff_comm] using hfarCard))).1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hN hF
  exact ⟨by linarith [hsh iN], by linarith [hsh iF]⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
