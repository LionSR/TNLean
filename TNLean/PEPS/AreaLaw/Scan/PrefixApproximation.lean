/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixCardinality
import TNLean.PEPS.AreaLaw.Scan.GoodSampling

/-!
# Physical prefix approximation of actual scan histories

Actual ambient dilation layers and the prescribed source horizon give nested
whole-row prefixes within `3nD` sites of U and UY. The same bound holds for
P₀ and P₀Y, before removing the target. These are conclusions of the actual
history evaluator, without a supplied prefix approximation certificate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 243–260, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan
namespace CollarScan

open scoped symmDiff

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- Actual completed lattice histories have deterministic nested-prefix
comparisons with at most `3nD` changed sites. Full near sets and the entropy
regions with the fixed target removed obey the same bound. -/
theorem state_prefix_approximation_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K)
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) :
    positiveDepthPrefix S.A S.depth (S.front g (h.1 g) k false - 1) ⊆ positiveNear S.depth
      (S.state h g) ∧
    positiveNearMiddle S.depth (S.state h g) ⊆ positiveDepthPrefix S.A S.depth (-S.front g (h.1
      g) k true) ∧
    ((receiving (S.state h g) false) ∆ depthPrefix S.A S.depth (S.front g (h.1 g) k false -
      1)).card ≤ 3 * S.n * S.D ∧
    ((receiving (S.state h g) false ∪ middle (S.state h g)) ∆
      depthPrefix S.A S.depth (-S.front g (h.1 g) k true)).card ≤ 3 * S.n * S.D ∧
    ((positiveNear S.depth (S.state h g)) ∆ positiveDepthPrefix S.A S.depth (S.front g (h.1 g) k
      false - 1)).card ≤
      3 * S.n * S.D ∧
    ((positiveNearMiddle S.depth (S.state h g)) ∆ positiveDepthPrefix S.A S.depth (-S.front g
      (h.1 g) k true)).card ≤
      3 * S.n * S.D := by
  have hb := S.prefix_uncertainty_rows h.1 g hn hk hr hDpos hD hL
  have hs := S.state_prefix_sandwich h g hn hk hr hDpos hD
    (fun x hx ↦ depthRow_length_le_of_ambientRows hT hdepth hrows
      (S.state_depth_bounds h g hL x hx))
    (abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth)
  apply prefix_sandwich_card_bounds S.A S.depth (S.state h g)
    (S.front g (h.1 g) k false) (S.front g (h.1 g) k true) S.n S.D S.r₀ hr hDpos hs
  · intro d hd
    simpa only [depthRow, Finset.length_toList] using
      depthRow_length_le_of_ambientRows hT hdepth hrows (Finset.Icc_subset_Icc hb.1.1 hb.1.2 hd)
  · intro d hd
    simpa only [depthRow, Finset.length_toList] using
      depthRow_length_le_of_ambientRows hT hdepth hrows (Finset.Icc_subset_Icc hb.2.1 hb.2.2 hd)

/-- Actual pre-charge lattice histories have deterministic nested-prefix
comparisons with at most `3nD` changed sites. Full near sets and the entropy
regions with the fixed target removed obey the same bound. -/
theorem oldChargeState_prefix_approximation_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K)
    (hn : 0 < S.n) (hk : (k + 1) ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) :
    positiveDepthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false - 1) ⊆ positiveNear S.depth
      (S.oldChargeState h g) ∧
    positiveNearMiddle S.depth (S.oldChargeState h g) ⊆ positiveDepthPrefix S.A S.depth
      (-S.front g (h.1 g) (k + 1) true) ∧
    ((receiving (S.oldChargeState h g) false) ∆ depthPrefix S.A S.depth (S.front g (h.1 g) (k +
      1) false - 1)).card ≤ 3 * S.n * S.D ∧
    ((receiving (S.oldChargeState h g) false ∪ middle (S.oldChargeState h g)) ∆
      depthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true)).card ≤ 3 * S.n * S.D ∧
    ((positiveNear S.depth (S.oldChargeState h g)) ∆ positiveDepthPrefix S.A S.depth (S.front g
      (h.1 g) (k + 1) false - 1)).card ≤
      3 * S.n * S.D ∧
    ((positiveNearMiddle S.depth (S.oldChargeState h g)) ∆ positiveDepthPrefix S.A S.depth
      (-S.front g (h.1 g) (k + 1) true)).card ≤
      3 * S.n * S.D := by
  have hb := S.prefix_uncertainty_rows h.1 g hn hk hr hDpos hD hL
  have hs := S.oldChargeState_prefix_sandwich h g hn hk hr hDpos hD
    (fun x hx ↦ depthRow_length_le_of_ambientRows hT hdepth hrows
      (S.oldChargeState_depth_bounds h g hL x hx))
    (abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth)
  apply prefix_sandwich_card_bounds S.A S.depth (S.oldChargeState h g)
    (S.front g (h.1 g) (k + 1) false) (S.front g (h.1 g) (k + 1) true) S.n S.D S.r₀ hr hDpos hs
  · intro d hd
    simpa only [depthRow, Finset.length_toList] using
      depthRow_length_le_of_ambientRows hT hdepth hrows (Finset.Icc_subset_Icc hb.1.1 hb.1.2 hd)
  · intro d hd
    simpa only [depthRow, Finset.length_toList] using
      depthRow_length_le_of_ambientRows hT hdepth hrows (Finset.Icc_subset_Icc hb.2.1 hb.2.2 hd)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
