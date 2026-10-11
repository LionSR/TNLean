/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution

/-!
# Physical sizes of actual scan moves and split supports

Every induced-domain graph ball injects into its ambient sup-norm square.
A fill moves at most its one scheduled site, and a charge moves only the
selected ball's old middle part. A truncated designated support has the same
square bound only when it meets the actual middle and a receiving side:
then the variable truncation radius reduces to the base radius.

These bounds need neither goodness nor the row, clearance, or time-horizon
hypotheses. They concern physical sites only, before adding auxiliary factors.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 331–352, and `08-scanner.tex`, lines 125–137 and
225–233, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- A finite graph-distance bound in an induced lattice domain implies membership
in the ambient square, including for domains with holes or disconnected components. -/
theorem mem_ambientDilation_singleton_of_domainGraph_edist_le
    {Λ : Finset (ℤ × ℤ)} {x a : Site Λ} {r : ℕ}
    (h : (domainGraph Λ).edist x a ≤ (r : ℕ∞)) :
    x.val ∈ ambientDilation {a.val} r := by
  have hd := abs_ambientDepth_sub_le_domainGraph {a.val} (Finset.singleton_nonempty _) h
  have hz : ambientDepth {a.val} (Finset.singleton_nonempty _) a.val = 0 := by
    simp [ambientDepth, ambientSupDistance]
  rw [hz, sub_zero, abs_of_nonneg (ambientDepth_nonneg _ _ _)] at hd
  exact (ambientDepth_le_iff_mem_dilation _ _ _ _).mp hd

/-- A graph ball has at most `(2r+1)²` physical sites. No geometric regularity
of the finite domain is required. -/
theorem card_domainGraph_ball_le (Λ : Finset (ℤ × ℤ)) (a : Site Λ) (r : ℕ) :
    (Finset.univ.filter fun x ↦ (domainGraph Λ).edist a x ≤ (r : ℕ∞)).card ≤
      (2 * r + 1) ^ 2 := by
  classical
  calc
    _ ≤ (ambientDilation {a.val} r).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro x hx
        apply mem_ambientDilation_singleton_of_domainGraph_edist_le
        simpa only [SimpleGraph.edist_comm] using (Finset.mem_filter.mp hx).2
      · exact Subtype.val_injective.injOn
    _ ≤ (2 * r + 1) ^ 2 := by
      simpa using Geometry.card_ambientDilation_le {a.val} r

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- A fill moves at most one site, including a blank or already assigned slot. -/
theorem card_fill_moved_le_one (A : Finset V) (depth : V → ℤ) (n : ℕ)
    (lo hi : ℤ) (k : ℕ) (σ : PhysicalPartition V) :
    (middle σ \ middle (fill A depth n lo hi k σ)).card ≤ 1 := by
  classical
  cases he : fillSlot A depth n lo hi (fillSide k) (fillCount k (fillSide k)) with
  | none => simp [fill, he]
  | some x =>
    simp only [fill, he, middle_sdiff_middle_assign]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)

namespace CollarScan

variable [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
/-- Every actual charge ball has the induced-lattice square bound. -/
theorem card_ball_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ) (i : I) :
    (S.ball i).card ≤ (2 * S.r₀ + 1) ^ 2 := by
  simpa only [ball, hgraph] using card_domainGraph_ball_le Λ (S.anchor i) S.r₀

/-- The actual charge moves no more than its ball's middle intersection. Blank
slots and disabled charges move no sites. Both receiving sides are included. -/
theorem card_chargeStep_moved_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (g r k : ℕ) (c : Bool × Fin S.M) (σ : PhysicalPartition (Site Λ)) :
    (middle σ \ middle (S.chargeStep g r k c σ)).card ≤ (2 * S.r₀ + 1) ^ 2 := by
  classical
  cases he : S.selected g r k c with
  | none => simp [chargeStep, he]
  | some i =>
    simp only [chargeStep, he, charge]
    split_ifs
    · rw [middle_sdiff_middle_assign]
      exact (Finset.card_le_card Finset.inter_subset_left).trans
        (S.card_ball_le_domainGraph hgraph i)
    · simp

/-- A designated support splitting a completed status has base-radius size.
This makes no assertion about an arbitrary unsplit designated support. -/
theorem card_designatedSupport_le_of_state_split_domainGraph
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hL : 8 * S.K * S.m ≤ L) (hs : S.designatedSplitIncidence (S.state h g) L i side) :
    (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).card ≤
      (2 * S.r₀ + 1) ^ 2 := by
  rw [S.designatedSupport_eq_ball_of_state_split h g side i hL hs]
  exact S.card_ball_le_domainGraph hgraph i

/-- A designated support splitting a pre-charge status has base-radius size.
The only scale assumption places the actual middle in the truncation set. -/
theorem card_designatedSupport_le_of_old_split_domainGraph
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hL : 8 * S.K * S.m ≤ L)
    (hs : S.designatedSplitIncidence (S.oldChargeState h g) L i side) :
    (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).card ≤
      (2 * S.r₀ + 1) ^ 2 := by
  rw [S.designatedSupport_eq_ball_of_split h g side i hL hs]
  exact S.card_ball_le_domainGraph hgraph i

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
