/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixApproximation
import TNLean.PEPS.AreaLaw.Scan.PrefixBoundary

/-!
# Physical cut-edge bounds for actual scan statuses

The two positive-depth prefix comparisons give `20nD` edges for U and UY,
and hence `40nD` for Y. Keeping the target gives `16nD` for P₀ and its
opposite-side complement V. Edges are undirected physical lattice edges,
counted once; the degree-four estimate is not an endpoint count.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 243–260, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing the near region from the near-with-middle region leaves exactly
Y, because the actual middle has positive depth. -/
theorem middle_eq_positiveNearMiddle_sdiff_positiveNear (depth : V → ℤ)
    (σ : PhysicalPartition V) (hpos : ∀ x, σ x = none → 0 < depth x) :
    middle σ = positiveNearMiddle depth σ \ positiveNear depth σ := by
  ext x
  cases he : σ x with
  | none => simp [middle, positiveNearMiddle, positiveNear, receiving, he, hpos x he]
  | some b => cases b <;> simp [middle, positiveNearMiddle, positiveNear, receiving, he]

/-- The far receiving side is the complement of the near side and middle. -/
theorem receiving_far_eq_compl (σ : PhysicalPartition V) :
    receiving σ true = (receiving σ false ∪ middle σ)ᶜ := by
  ext x
  cases he : σ x with
  | none => simp [receiving, middle, he]
  | some b => cases b <;> simp [receiving, middle, he]

private theorem physical_status_cut_bounds {Λ T : Finset (ℤ × ℤ)}
    (hT : T.Nonempty) (A : Finset (Site Λ)) (depth : Site Λ → ℤ)
    (hdepth : depth = fun x ↦ ambientDepth T hT x.val)
    (σ : PhysicalPartition (Site Λ)) {n D L r₀ : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (jN jF : ℤ) (hjN : jN ≤ L) (hjF : jF ≤ L)
    (hpos : ∀ x, σ x = none → 0 < depth x)
    (hP : ((receiving σ false) ∆ depthPrefix A depth jN).card ≤ 3 * n * D)
    (hPY : ((receiving σ false ∪ middle σ) ∆ depthPrefix A depth jF).card ≤ 3 * n * D)
    (hU : ((positiveNear depth σ) ∆ positiveDepthPrefix A depth jN).card ≤ 3 * n * D)
    (hUY : ((positiveNearMiddle depth σ) ∆ positiveDepthPrefix A depth jF).card ≤
      3 * n * D) :
    (edgeBoundary Λ (positiveNear depth σ)).card ≤ 20 * n * D ∧
    (edgeBoundary Λ (positiveNearMiddle depth σ)).card ≤ 20 * n * D ∧
    (edgeBoundary Λ (middle σ)).card ≤ 40 * n * D ∧
    (edgeBoundary Λ (receiving σ false)).card ≤ 16 * n * D ∧
    (edgeBoundary Λ (receiving σ true)).card ≤ 16 * n * D := by
  have hbase (j : ℤ) (hj : j ≤ L) :
      (edgeBoundary Λ (depthPrefix A depth j)).card ≤ 4 * n := by
    simpa only [hdepth] using card_edgeBoundary_depthPrefix_le Λ T hT A hL hrows hclear hj
  have hpositive (j : ℤ) (hj : j ≤ L) :
      (edgeBoundary Λ (positiveDepthPrefix A depth j)).card ≤ 8 * n := by
    simpa only [hdepth] using
      card_edgeBoundary_positiveDepthPrefix_le Λ T hT A hL hrows hclear hj
  have hnD : n ≤ n * D := by simpa using Nat.mul_le_mul_left n hD
  have hU' : (edgeBoundary Λ (positiveNear depth σ)).card ≤ 20 * n * D := by
    have := card_edgeBoundary_le_add_four_mul_symmDiff Λ
      (positiveNear depth σ) (positiveDepthPrefix A depth jN)
    have := hpositive jN hjN
    nlinarith
  have hUY' : (edgeBoundary Λ (positiveNearMiddle depth σ)).card ≤ 20 * n * D := by
    have := card_edgeBoundary_le_add_four_mul_symmDiff Λ
      (positiveNearMiddle depth σ) (positiveDepthPrefix A depth jF)
    have := hpositive jF hjF
    nlinarith
  refine ⟨hU', hUY', ?_, ?_, ?_⟩
  · rw [middle_eq_positiveNearMiddle_sdiff_positiveNear depth σ hpos]
    have := card_edgeBoundary_sdiff_le Λ (positiveNearMiddle depth σ) (positiveNear depth σ)
    nlinarith
  · have := card_edgeBoundary_le_add_four_mul_symmDiff Λ
      (receiving σ false) (depthPrefix A depth jN)
    have := hbase jN hjN
    nlinarith
  · rw [receiving_far_eq_compl, edgeBoundary_compl]
    have := card_edgeBoundary_le_add_four_mul_symmDiff Λ
      (receiving σ false ∪ middle σ) (depthPrefix A depth jF)
    have := hbase jF hjF
    nlinarith

namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- Every completed physical status has at most `40nD` cut edges in
each of U, UY, Y, P₀, V, with sharper constants for all but Y. No prefix,
edge-count, or good-history certificate is assumed. -/
theorem state_cut_bounds_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K)
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    (edgeBoundary Λ (positiveNear S.depth (S.state h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (positiveNearMiddle S.depth (S.state h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (middle (S.state h g))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.state h g) false)).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.state h g) true)).card ≤ 16 * S.n * S.D := by
  have hb := S.prefix_uncertainty_rows h.1 g hn hk hr hDpos hD hL
  have ha := state_prefix_approximation_domainGraph hT S hgraph hdepth
    h g hn hk hr hDpos hD hL hrows
  have hLpos : 1 ≤ L := by
    have hK : 0 < S.K := Nat.zero_lt_of_lt g.isLt
    have hm : 0 < S.m := by omega
    have hp : 0 < 8 * S.K * S.m := Nat.mul_pos (Nat.mul_pos (by decide) hK) hm
    omega
  exact physical_status_cut_bounds hT S.A S.depth hdepth (S.state h g) hLpos hDpos
    hrows hclear (S.front g (h.1 g) k false - 1) (-S.front g (h.1 g) k true)
    (by
      have := hb.1.2
      have : (0 : ℤ) ≤ (S.D + S.r₀ : ℕ) := by positivity
      omega)
    hb.2.2 (fun x hx ↦ by have := Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hx); omega)
    ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2

/-- Every pre-charge physical status has at most `40nD` cut edges in
each of U, UY, Y, P₀, V, with sharper constants for all but Y. No prefix,
edge-count, or good-history certificate is assumed. -/
theorem oldChargeState_cut_bounds_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K)
    (hn : 0 < S.n) (hk : (k + 1) ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    (edgeBoundary Λ (positiveNear S.depth (S.oldChargeState h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (positiveNearMiddle S.depth (S.oldChargeState h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (middle (S.oldChargeState h g))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.oldChargeState h g) false)).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.oldChargeState h g) true)).card ≤ 16 * S.n * S.D := by
  have hb := S.prefix_uncertainty_rows h.1 g hn hk hr hDpos hD hL
  have ha := oldChargeState_prefix_approximation_domainGraph hT S hgraph hdepth
    h g hn hk hr hDpos hD hL hrows
  have hLpos : 1 ≤ L := by
    have hK : 0 < S.K := Nat.zero_lt_of_lt g.isLt
    have hm : 0 < S.m := by omega
    have hp : 0 < 8 * S.K * S.m := Nat.mul_pos (Nat.mul_pos (by decide) hK) hm
    omega
  exact physical_status_cut_bounds hT S.A S.depth hdepth (S.oldChargeState h g) hLpos hDpos
    hrows hclear (S.front g (h.1 g) (k + 1) false - 1) (-S.front g (h.1 g) (k + 1) true)
    (by
      have := hb.1.2
      have : (0 : ℤ) ≤ (S.D + S.r₀ : ℕ) := by positivity
      omega)
    hb.2.2 (fun x hx ↦ by
      have := Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hx)
      omega)
    ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
