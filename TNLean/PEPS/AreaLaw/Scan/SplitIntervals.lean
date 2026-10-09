/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AssignedLead
import TNLean.PEPS.AreaLaw.Scan.GoodSampling

/-!
# Unconditional split intervals

Actual old and completed histories confine a splitting ball's anchor to the
interval from `front-r₀` to `front+D+2r₀`. The upper bound uses unconditional
assigned-site lead. The lower bound uses the consumed deterministic rows.
For the induced lattice graph, depth variation and containment in the chosen
color follow from actual ambient depth and cut clearance.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 274–284, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Completed histories have no unassigned site behind a completed fill row. -/
theorem bandState_front_le (g r k : ℕ) (choices : Fin k → Bool × Fin S.M)
    (side : Bool) (x : V) (hn : 0 < S.n)
    (hrow : (orientedRow S.depth side (orientedDepth S.depth side x)).length ≤ S.n)
    (hx : S.bandState g r k choices x = none) :
    S.front g r k side ≤ orientedDepth S.depth side x := by
  obtain ⟨hinit, hslots⟩ := S.bandState_unassigned g r k choices x hx
  exact nominalFront_le_of_unconsumed S.A S.depth hn _ _ k side x hinit hrow hslots

omit [Fintype I] [LinearOrder I] in
private theorem split_bounds (σ : PhysicalPartition V) (j : ℤ) (side : Bool) (i : I)
    (hball : S.ball i ⊆ S.A)
    (hfront : ∀ x, σ x = none → j ≤ orientedDepth S.depth side x)
    (hlead : ∀ x, x ∈ S.A → σ x = some side →
      orientedDepth S.depth side x ≤ j + S.D + S.r₀)
    (hdepth : ∀ x ∈ S.ball i, |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hsplit : (S.ball i ∩ receiving σ side).Nonempty ∧
      (S.ball i ∩ middle σ).Nonempty) :
    j - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤ j + S.D + 2 * S.r₀ := by
  have hv (x : V) (hx : x ∈ S.ball i) :
      |orientedDepth S.depth side x - orientedDepth S.depth side (S.anchor i)| ≤ S.r₀ := by
    cases side <;>
      simpa only [orientedDepth, Bool.false_eq_true, ↓reduceIte, neg_sub_neg, abs_sub_comm]
        using hdepth x hx
  obtain ⟨x, hx⟩ := hsplit.2
  obtain ⟨y, hy⟩ := hsplit.1
  obtain ⟨hxb, hxm⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyb, hyr⟩ := Finset.mem_inter.mp hy
  have hlow := hfront x (Finset.mem_filter.mp hxm).2
  have hupp := hlead y (hball hyb) (Finset.mem_filter.mp hyr).2
  have hxv := abs_le.mp (hv x hxb)
  have hyv := abs_le.mp (hv y hyb)
  omega

/-- Every actual old split has an anchor in a narrow interval, without goodness. -/
theorem old_split_anchor_bounds {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (i : I) (hn : 0 < S.n) (hball : S.ball i ⊆ S.A)
    (hrow : ∀ x, S.oldChargeState h g x = none →
      (depthRow S.depth (S.depth x)).length ≤ S.n)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hsplit : (S.ball i ∩ receiving (S.oldChargeState h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) :
    S.front g (h.1 g) (k + 1) side - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤
        S.front g (h.1 g) (k + 1) side + S.D + 2 * S.r₀ := by
  apply S.split_bounds _ _ side i hball _
    (fun x hxA hx ↦ S.oldChargeState_assigned_lead h g hdepth side x hxA hx)
    (hdepth i) hsplit
  intro x hx
  apply S.oldChargeState_front_le h g side x hn _ hx
  cases side <;> simpa [orientedRow, orientedDepth] using hrow x hx

/-- The same interval confines splits in a completed history, including the new
leaf after any recorded charge. -/
theorem state_split_anchor_bounds {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (i : I) (hn : 0 < S.n) (hball : S.ball i ⊆ S.A)
    (hrow : ∀ x, S.state h g x = none → (depthRow S.depth (S.depth x)).length ≤ S.n)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hsplit : (S.ball i ∩ receiving (S.state h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.state h g)).Nonempty) :
    S.front g (h.1 g) k side - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤ S.front g (h.1 g) k side + S.D + 2 * S.r₀ := by
  apply S.split_bounds _ _ side i hball _
    (fun x hxA hx ↦ S.bandState_assigned_lead g (h.1 g) k
      (fun t ↦ h.2 t g) hdepth side x hxA hx) (hdepth i) hsplit
  intro x hx
  apply S.bandState_front_le g (h.1 g) k (fun t ↦ h.2 t g) side x hn _ hx
  cases side <;> simpa [orientedRow, orientedDepth] using hrow x hx

/-- Every completed middle remains inside the original compact depth window. -/
theorem state_depth_bounds {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) (x : V)
    (hx : S.state h g x = none) : S.depth x ∈ Finset.Icc (1 : ℤ) L := by
  have hinit := (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hx).1
  have hlo := (initial_middle_depth S.A S.depth _ _ hinit false).2
  have hhi := (initial_middle_depth S.A S.depth _ _ hinit true).2
  have hoffset := (h.1 g).isLt
  have hupper : 8 * g.val * S.m + 5 * S.m + (h.1 g).val ≤ L := by
    calc
      _ ≤ 8 * g.val * S.m + 8 * S.m := by omega
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  simp only [initialFront, orientedDepth, Bool.false_eq_true, ↓reduceIte, lower, upper] at *
  rw [Finset.mem_Icc]
  constructor <;> omega

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- At a fixed front time, an anchor can reach at most one band on a fixed side,
even when the two histories have different offsets. The separation is uniform
in time because deterministic front advances do not depend on the band. -/
theorem split_interval_band_unique {g g' r r' k a b : ℕ} {z : ℤ}
    (hm : 0 < S.m) (hwidth : a + b ≤ S.m) (hr : r < S.m) (hr' : r' < S.m)
    (side : Bool)
    (h : S.front g r k side - a ≤ z ∧ z ≤ S.front g r k side + b)
    (h' : S.front g' r' k side - a ≤ z ∧ z ≤ S.front g' r' k side + b) : g = g' := by
  by_contra hne
  have hg : (g : ℤ) + 1 ≤ g' ∨ (g' : ℤ) + 1 ≤ g := by omega
  have hm' : (0 : ℤ) < S.m := by exact_mod_cast hm
  have hw' : (a : ℤ) + b ≤ S.m := by exact_mod_cast hwidth
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hr0' : (0 : ℤ) ≤ r' := by positivity
  have hr1 : (r : ℤ) < S.m := by exact_mod_cast hr
  have hr1' : (r' : ℤ) < S.m := by exact_mod_cast hr'
  cases side <;>
    simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
      ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h h'
  all_goals rcases hg with hg | hg <;> nlinarith

omit [Fintype I] [LinearOrder I] in
private theorem domainGraph_row_bound {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {L : ℕ} (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (x : Site Λ) (hx : S.depth x ∈ Finset.Icc (1 : ℤ) L) :
    (depthRow S.depth (S.depth x)).length ≤ S.n := by
  have ht := Finset.mem_Icc.mp hx
  have htnat : ((S.depth x).toNat : ℤ) = S.depth x := by omega
  have hb := depthRow_ambientDepth_length_le_of_row_bound T hT
    (Subtype.val : Site Λ → ℤ × ℤ) Subtype.val_injective hrows
    (show 1 ≤ (S.depth x).toNat by omega) (show (S.depth x).toNat ≤ L by omega)
  rw [← hdepth] at hb
  simpa only [htnat] using hb

omit [Fintype I] [LinearOrder I] in
private theorem domainGraph_split_ball_subset {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (σ : PhysicalPartition (Site Λ)) (i : I)
    (hmiddle : ∀ x, σ x = none → x ∈ S.A ∧ S.depth x ≤ L)
    (hsplit : (S.ball i ∩ middle σ).Nonempty) : S.ball i ⊆ S.A := by
  obtain ⟨y, hy⟩ := hsplit
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyA, hydepth⟩ := hmiddle y (Finset.mem_filter.mp hym).2
  have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
    ⟨y, hyA, by simpa only [hdepth] using hydepth,
      by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
  simpa only [ball, hgraph] using hb

/-- Actual old splits in the induced lattice graph satisfy the unconditional
anchor interval. Ambient row counts and physical cut clearance discharge the
geometric hypotheses; goodness is not required. -/
theorem old_split_anchor_bounds_domainGraph {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 0 < S.n) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hsplit : (S.ball i ∩ receiving (S.oldChargeState h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) :
    S.front g (h.1 g) (k + 1) side - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤
        S.front g (h.1 g) (k + 1) side + S.D + 2 * S.r₀ := by
  apply S.old_split_anchor_bounds h g side i hn _ _
    (S.abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT hgraph hdepth) hsplit
  · apply domainGraph_split_ball_subset hT S hgraph hdepth hclear _ i _ hsplit.2
    intro x hx
    exact ⟨(initial_middle_depth S.A S.depth _ _
      (S.oldChargeState_initial_none h g x hx) false).1,
      (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hx)).2⟩
  · intro x hx
    exact domainGraph_row_bound hT S hdepth hrows x (S.oldChargeState_depth_bounds h g hL x hx)

/-- The same geometric interval holds for every completed actual history,
including the new leaves after arbitrary charges. -/
theorem state_split_anchor_bounds_domainGraph {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 0 < S.n) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hsplit : (S.ball i ∩ receiving (S.state h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.state h g)).Nonempty) :
    S.front g (h.1 g) k side - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤ S.front g (h.1 g) k side + S.D + 2 * S.r₀ := by
  apply S.state_split_anchor_bounds h g side i hn _ _
    (S.abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT hgraph hdepth) hsplit
  · apply domainGraph_split_ball_subset hT S hgraph hdepth hclear _ i _ hsplit.2
    intro x hx
    exact ⟨(initial_middle_depth S.A S.depth _ _
      (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hx).1 false).1,
      (Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hx)).2⟩
  · intro x hx
    exact domainGraph_row_bound hT S hdepth hrows x (S.state_depth_bounds h g hL x hx)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
