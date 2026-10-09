/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BandUniqueness
import TNLean.PEPS.AreaLaw.Scan.BandNesting

/-!
# Terminal splitting of actual designated supports

The source terminal split is a physical partition condition: a support meets
the middle and exactly one receiving side in one band, and is contained in a
single part in every other band. This is different from crossing the entropy
cut obtained by removing the fixed inner target from the near side.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(1), and `06-transport.tex`, lines 336–352,
at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- A support splits exactly one physical band and one of its receiving sides;
in every other band the entire support belongs to one part. -/
def IsTerminalSplit {K : ℕ} (σ : Fin K → PhysicalPartition V)
    (support : Finset V) (g : Fin K) (side : Bool) : Prop :=
  (support ∩ middle (σ g)).Nonempty ∧
    (support ∩ receiving (σ g) side).Nonempty ∧
    Disjoint support (receiving (σ g) (!side)) ∧
    ∀ g' ≠ g, ∃ part : Option Bool, ∀ x ∈ support, σ g' x = part

namespace CollarScan

variable (S : CollarScan V I)

/-- Within the source horizon, a designated support has at most one actual
splitting band and side. The hypotheses are ambient geometry and source scales. -/
theorem state_designatedSplitIncidence_unique_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g g' : Fin S.K) (side side' : Bool) (i : I)
    (hs : S.designatedSplitIncidence (S.state h g) L i side)
    (hs' : S.designatedSplitIncidence (S.state h g') L i side') :
    g = g' ∧ side = side' := by
  have bounds (f : Fin S.K) (s : Bool)
      (he : S.designatedSplitIncidence (S.state h f) L i s) :
      S.front f (h.1 f) k s - S.r₀ ≤ orientedDepth S.depth s (S.anchor i) ∧
      orientedDepth S.depth s (S.anchor i) ≤ S.front f (h.1 f) k s + S.D + 2 * S.r₀ := by
    have heq := S.designatedSupport_eq_ball_of_state_split h f s i hL he
    exact state_split_anchor_bounds_domainGraph hT S hgraph hdepth h f s i hn hL hrows hclear
      (by simpa only [designatedSplitIncidence, heq] using he)
  exact S.front_intervals_unique h.1 hn hk hr hDpos hD g g' side side' (S.depth (S.anchor i))
    (bounds g side hs) (bounds g' side' hs')

/-- Within the source horizon, a designated support has at most one actual
splitting band and side. The hypotheses are ambient geometry and source scales. -/
theorem old_designatedSplitIncidence_unique_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g g' : Fin S.K) (side side' : Bool) (i : I)
    (hs : S.designatedSplitIncidence (S.oldChargeState h g) L i side)
    (hs' : S.designatedSplitIncidence (S.oldChargeState h g') L i side') :
    g = g' ∧ side = side' := by
  have bounds (f : Fin S.K) (s : Bool)
      (he : S.designatedSplitIncidence (S.oldChargeState h f) L i s) :
      S.front f (h.1 f) (k + 1) s - S.r₀ ≤ orientedDepth S.depth s (S.anchor i) ∧
      orientedDepth S.depth s (S.anchor i) ≤ S.front f (h.1 f) (k + 1) s + S.D + 2 * S.r₀ := by
    have heq := S.designatedSupport_eq_ball_of_split h f s i hL he
    exact old_split_anchor_bounds_domainGraph hT S hgraph hdepth h f s i hn hL hrows hclear
      (by simpa only [designatedSplitIncidence, heq] using he)
  exact S.front_intervals_unique h.1 hn hk hr hDpos hD g g' side side' (S.depth (S.anchor i))
    (bounds g side hs) (bounds g' side' hs')

omit [Fintype I] [LinearOrder I] in
private theorem ball_other_band_initial_part (offset : Fin S.K → Fin S.m)
    (g g' : Fin S.K) (hgg : g' ≠ g) (i : I) (hr : S.r₀ ≤ S.m)
    (hball : S.ball i ⊆ S.A)
    (hdepth : ∀ x ∈ S.ball i, |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hmid : (S.ball i ∩ middle
      (initialPartition S.A S.depth (S.lower g (offset g)) (S.upper g (offset g)))).Nonempty) :
    ∀ x ∈ S.ball i,
      initialPartition S.A S.depth (S.lower g' (offset g')) (S.upper g' (offset g')) x =
        some (decide (g' < g)) := by
  obtain ⟨y, hy⟩ := hmid
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  have hi := (Finset.mem_filter.mp hym).2
  have hlow := (initial_middle_depth S.A S.depth _ _ hi false).2
  have hupp := (initial_middle_depth S.A S.depth _ _ hi true).2
  have hyv := abs_le.mp (hdepth y hyb)
  have ho : ((offset g).val : ℤ) < S.m := by exact_mod_cast (offset g).isLt
  have ho' : ((offset g').val : ℤ) < S.m := by exact_mod_cast (offset g').isLt
  have ho0 : (0 : ℤ) ≤ (offset g).val := by positivity
  have ho0' : (0 : ℤ) ≤ (offset g').val := by positivity
  have hrr : (S.r₀ : ℤ) ≤ S.m := by exact_mod_cast hr
  have hm : (0 : ℤ) < S.m := by exact_mod_cast (Nat.zero_lt_of_lt (offset g).isLt)
  simp only [initialFront, orientedDepth, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hlow hupp
  intro x hx
  have hxv := abs_le.mp (hdepth x hx)
  have hxA := hball hx
  rcases lt_or_gt_of_ne hgg with hbefore | hafter
  · have horder : (g'.val : ℤ) + 1 ≤ g.val := by exact_mod_cast hbefore
    have hhigh : S.upper g' (offset g') < S.depth x := by
      simp only [upper, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    have hlo : S.lower g' (offset g') ≤ S.upper g' (offset g') := by
      simp only [lower, upper]; omega
    simp [initialPartition, hxA, show ¬ S.depth x ≤ S.lower g' (offset g') by omega,
      hhigh, hbefore]
  · have horder : (g.val : ℤ) + 1 ≤ g'.val := by exact_mod_cast hafter
    have hsmall : S.depth x ≤ S.lower g' (offset g') := by
      simp only [lower, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    simp [initialPartition, hxA, hsmall, show ¬ g' < g by omega]

/-- Every site of a ball meeting one band's actual middle is in the initial near
side of each later band, or the initial far side of each earlier band. -/
theorem state_ball_other_band_initial_part {k : ℕ} (h : History S.K S.m S.M k)
    (g g' : Fin S.K) (hgg : g' ≠ g) (i : I) (hr : S.r₀ ≤ S.m)
    (hball : S.ball i ⊆ S.A)
    (hdepth : ∀ x ∈ S.ball i, |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hmid : (S.ball i ∩ middle (S.state h g)).Nonempty) :
    ∀ x ∈ S.ball i,
      initialPartition S.A S.depth (S.lower g' (h.1 g')) (S.upper g' (h.1 g')) x =
        some (decide (g' < g)) := by
  apply S.ball_other_band_initial_part h.1 g g' hgg i hr hball hdepth
  obtain ⟨y, hy⟩ := hmid
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  exact ⟨y, Finset.mem_inter.mpr ⟨hyb, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) y
      (Finset.mem_filter.mp hym).2).1⟩⟩⟩

/-- Every site of a ball meeting one band's actual middle is in the initial near
side of each later band, or the initial far side of each earlier band. -/
theorem oldChargeState_ball_other_band_initial_part {k : ℕ} (h : History S.K S.m S.M k)
    (g g' : Fin S.K) (hgg : g' ≠ g) (i : I) (hr : S.r₀ ≤ S.m)
    (hball : S.ball i ⊆ S.A)
    (hdepth : ∀ x ∈ S.ball i, |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hmid : (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) :
    ∀ x ∈ S.ball i,
      initialPartition S.A S.depth (S.lower g' (h.1 g')) (S.upper g' (h.1 g')) x =
        some (decide (g' < g)) := by
  apply S.ball_other_band_initial_part h.1 g g' hgg i hr hball hdepth
  obtain ⟨y, hy⟩ := hmid
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  exact ⟨y, Finset.mem_inter.mpr ⟨hyb, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    S.oldChargeState_initial_none h g y (Finset.mem_filter.mp hym).2⟩⟩⟩

/-- An actual designated split incidence satisfies the full physical terminal
split definition: exactly one receiving side, and a single part in every other band. -/
theorem state_designatedSplitIncidence_isTerminalSplit_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g : Fin S.K) (side : Bool) (i : I)
    (hs : S.designatedSplitIncidence (S.state h g) L i side) :
    IsTerminalSplit (S.state h)
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side := by
  have heq := S.designatedSupport_eq_ball_of_state_split h g side i hL hs
  have hm : (S.ball i ∩ middle (S.state h g)).Nonempty := by
    simpa only [heq] using hs.2
  have hvar (x : Site Λ) (hx : x ∈ S.ball i) :
      |S.depth x - S.depth (S.anchor i)| ≤ S.r₀ := by
    have hd : (domainGraph Λ).edist (S.anchor i) x ≤ (S.r₀ : ℕ∞) := by
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hx
    simpa only [hdepth, abs_sub_comm] using abs_ambientDepth_sub_le_domainGraph T hT hd
  have hball : S.ball i ⊆ S.A := by
    obtain ⟨y, hy⟩ := hm
    obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
    have hyn := (Finset.mem_filter.mp hym).2
    have hyA := (initial_middle_depth S.A S.depth _ _
      (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) y hyn).1 false).1
    have hyL := (Finset.mem_Icc.mp (S.state_depth_bounds h g hL y hyn)).2
    have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
      ⟨y, hyA, by simpa only [hdepth] using hyL,
        by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
    simpa only [ball, hgraph] using hb
  refine ⟨hs.2, hs.1, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxside
    have hop : S.designatedSplitIncidence (S.state h g) L i (!side) :=
      ⟨⟨x, Finset.mem_inter.mpr ⟨hx, hxside⟩⟩, hs.2⟩
    have he := (state_designatedSplitIncidence_unique_domainGraph hT S hgraph hdepth h
      hn hk hr hDpos hD hL hrows hclear g g side (!side) i hs hop).2
    cases side <;> simp at he
  · intro g' hgg
    refine ⟨some (decide (g' < g)), ?_⟩
    intro x hx
    rw [heq] at hx
    exact S.bandState_of_initial_assigned _ _ _ _ _ _
      (S.state_ball_other_band_initial_part h g g' hgg i (by omega) hball hvar hm x hx)
/-- An actual designated split incidence satisfies the full physical terminal
split definition: exactly one receiving side, and a single part in every other band. -/
theorem old_designatedSplitIncidence_isTerminalSplit_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g : Fin S.K) (side : Bool) (i : I)
    (hs : S.designatedSplitIncidence (S.oldChargeState h g) L i side) :
    IsTerminalSplit (S.oldChargeState h)
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side := by
  have heq := S.designatedSupport_eq_ball_of_split h g side i hL hs
  have hm : (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty := by
    simpa only [heq] using hs.2
  have hvar (x : Site Λ) (hx : x ∈ S.ball i) :
      |S.depth x - S.depth (S.anchor i)| ≤ S.r₀ := by
    have hd : (domainGraph Λ).edist (S.anchor i) x ≤ (S.r₀ : ℕ∞) := by
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hx
    simpa only [hdepth, abs_sub_comm] using abs_ambientDepth_sub_le_domainGraph T hT hd
  have hball : S.ball i ⊆ S.A := by
    obtain ⟨y, hy⟩ := hm
    obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
    have hyn := (Finset.mem_filter.mp hym).2
    have hyA := (initial_middle_depth S.A S.depth _ _
      (S.oldChargeState_initial_none h g y hyn) false).1
    have hyL := (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL y hyn)).2
    have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
      ⟨y, hyA, by simpa only [hdepth] using hyL,
        by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
    simpa only [ball, hgraph] using hb
  refine ⟨hs.2, hs.1, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxside
    have hop : S.designatedSplitIncidence (S.oldChargeState h g) L i (!side) :=
      ⟨⟨x, Finset.mem_inter.mpr ⟨hx, hxside⟩⟩, hs.2⟩
    have he := (old_designatedSplitIncidence_unique_domainGraph hT S hgraph hdepth h
      hn hk hr hDpos hD hL hrows hclear g g side (!side) i hs hop).2
    cases side <;> simp at he
  · intro g' hgg
    refine ⟨some (decide (g' < g)), ?_⟩
    intro x hx
    rw [heq] at hx
    exact S.oldChargeState_of_initial_assigned h g'
      (S.oldChargeState_ball_other_band_initial_part h g g' hgg i (by omega) hball hvar hm x hx)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
