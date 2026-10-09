/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AncestryLead
import TNLean.PEPS.AreaLaw.Scan.GoodSampling

/-!
# Actual charge ancestry in the physical domain graph

The ambient clearance localizes every successful charge ball inside the
chosen color. Consequently backward ancestry remains in that color even on
the far side, where the physical exterior was initially assigned. No
ancestry or ball-containment certificate is supplied as a hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–311, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {I : Type*} [Fintype I] [LinearOrder I]

namespace CollarScan

/-- Every physically assigned site of the chosen color has a chronological
charge ancestry rooted at an initial or actual deterministic fill site.
Containment of all predecessor sites, including far-side predecessors, follows
from the domain graph and the source clearance condition. -/
theorem bandState_has_chargeAncestry_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (g : Fin S.K) (r : Fin S.m) (choices : ℕ → Bool × Fin S.M)
    {L : ℕ} (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (k : ℕ) (side : Bool) (x : Site Λ) (hxA : x ∈ S.A)
    (hx : S.bandState g r k (fun j ↦ choices j) x = some side) :
    ∃ events, S.ChargeAncestry g r choices side k x events := by
  apply S.bandState_has_chargeAncestry g r choices _ k side x hxA hx
  intro t i _ hmeet
  let h : History S.K S.m S.M t := (fun _ ↦ r, fun j _ ↦ choices j)
  obtain ⟨y, hy⟩ := hmeet
  obtain ⟨hyball, hymid⟩ := Finset.mem_inter.mp hy
  have hynone : S.oldChargeState h g y = none := (Finset.mem_filter.mp hymid).2
  have hyA := (initial_middle_depth S.A S.depth _ _
    (S.oldChargeState_initial_none h g y hynone) false).1
  have hydepth := (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL y hynone)).2
  have hygraph : (domainGraph Λ).edist (S.anchor i) y ≤ (S.r₀ : ℕ∞) := by
    simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyball
  have hsub := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
    ⟨y, hyA, by simpa only [hdepth] using hydepth, hygraph⟩
  simpa only [ball, hgraph] using hsub

/-- Possible bad endpoints lie in the actual initial collar of the chosen color.
No cardinality of the ambient physical domain or its far exterior enters this set. -/
theorem bad_bandState_mem_collar {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) (g : Fin S.K) (r : Fin S.m) {L k : ℕ}
    (hL : 8 * S.K * S.m ≤ L) (choices : Fin k → Bool × Fin S.M)
    (side : Bool) (x : V) (hxA : x ∈ S.A)
    (hx : S.bandState g r k choices x = some side)
    (hbad : 2 * S.front g r k side + S.D < 2 * orientedDepth S.depth side x) :
    x ∈ S.A ∧ S.depth x ≤ L := by
  have hinit := S.bad_bandState_initial_none g r k choices side x hxA hx hbad
  have hupper := (initial_middle_depth S.A S.depth _ _ hinit true).2
  have hbound : 8 * g.val * S.m + 5 * S.m + r.val ≤ L := by
    calc
      _ ≤ 8 * g.val * S.m + 8 * S.m := by omega
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  refine ⟨hxA, ?_⟩
  simp only [initialFront, orientedDepth, upper, ↓reduceIte] at hupper
  have hboundZ : ((8 * g.val * S.m + 5 * S.m + r.val : ℕ) : ℤ) ≤ L := by
    exact_mod_cast hbound
  omega

/-- A physically bad completed-pair endpoint forces a long selected-charge
ancestry inside a short pair-time window. Ambient depth variation and all
ancestry existence hypotheses are discharged from the physical domain graph. -/
theorem bad_bandState_has_long_chargeAncestry_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (g : Fin S.K) (r : Fin S.m) (choices : ℕ → Bool × Fin S.M)
    {L : ℕ} (hL : 8 * S.K * S.m ≤ L) (hn : 0 < S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (k : ℕ) (side : Bool) (x : Site Λ) (hxA : x ∈ S.A)
    (hx : S.bandState g r k (fun j ↦ choices j) x = some side)
    (hbad : 2 * S.front g r k side + S.D < 2 * orientedDepth S.depth side x) :
    ∃ events, S.ChargeAncestry g r choices side k x events ∧ events ≠ [] ∧
      (S.D : ℤ) < 4 * S.r₀ * events.length ∧
      ∀ e ∈ events, (k : ℤ) - (e.1 + 1) ≤
        4 * S.n * ((S.r₀ : ℤ) * events.length + 1) := by
  obtain ⟨events, he⟩ := S.bandState_has_chargeAncestry_domainGraph hT hgraph hdepth
    g r choices hL hclear k side x hxA hx
  refine ⟨events, he, he.bad_length_and_time S hn ?_ hbad⟩
  exact S.abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT hgraph hdepth

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
