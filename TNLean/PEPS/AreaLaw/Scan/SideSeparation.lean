/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusContainment
import TNLean.PEPS.AreaLaw.Scan.BandMargins
import TNLean.PEPS.AreaLaw.Scan.GoodSampling

/-!
# Designated supports cannot meet both receiving sides

The actual near side lies in the compact truncation set. A designated support
meeting it and the far side is therefore the base-radius graph ball. Clearance
puts that ball wholly inside the chosen color, where the unconditional lead
bounds apply to both sides. The source window margins separate these leads by
more than a ball diameter, excluding such a support for every history.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(1), lines 225–247, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- The actual near side remains in the truncation set at every completed history,
including the fixed target. No row bound or good-history condition is needed. -/
theorem state_near_subset_truncationSet {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    receiving (S.state h g) false ⊆ S.truncationSet L := by
  intro x hx
  apply S.state_far_compl_subset_truncationSet h g hL
  have hxnear := (Finset.mem_filter.mp hx).2
  simp [receiving, hxnear]

/-- The actual near side remains in the truncation set immediately before a charge. -/
theorem oldChargeState_near_subset_truncationSet {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    receiving (S.oldChargeState h g) false ⊆ S.truncationSet L := by
  intro x hx
  apply S.oldChargeState_far_compl_subset_truncationSet h g hL
  have hxnear := (Finset.mem_filter.mp hx).2
  simp [receiving, hxnear]

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
private theorem front_sum_lt_neg_lead {k : ℕ} (g r : ℕ)
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) :
    S.front g r k false + S.front g r k true + 2 * S.D + 4 * S.r₀ < 0 := by
  have hn' : ((fillCount k false / S.n : ℕ) : ℤ) ≤ S.m := by
    exact_mod_cast fillCount_div_le_window hn hk false
  have hf' : ((fillCount k true / S.n : ℕ) : ℤ) ≤ S.m := by
    exact_mod_cast fillCount_div_le_window hn hk true
  have hr' : (S.r₀ : ℤ) ≤ S.D := by exact_mod_cast hr
  have hDpos' : (1 : ℤ) ≤ S.D := by exact_mod_cast hDpos
  have hD' : (4 : ℤ) * S.D ≤ S.m := by exact_mod_cast hD
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

omit [Fintype I] [LinearOrder I] in
private theorem designatedSupport_not_near_far_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (g r : ℕ) (σ : PhysicalPartition (Site Λ))
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hnear : receiving σ false ⊆ S.truncationSet L)
    (hlead : ∀ side x, x ∈ S.A → σ x = some side →
      orientedDepth S.depth side x ≤ S.front g r k side + S.D + S.r₀)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (i : I) :
    ¬ ((designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving σ false).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving σ true).Nonempty) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  obtain ⟨hxD, hxP⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyD, hyF⟩ := Finset.mem_inter.mp hy
  have hxσ := (Finset.mem_filter.mp hxP).2
  have hyσ := (Finset.mem_filter.mp hyF).2
  have hcross : () ∈ crossingLabels S.graph (S.truncationSet L) S.r₀
      (fun _ : Unit ↦ S.anchor i) (receiving σ false) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxD, hxP⟩,
      y, hyD, by simp [receiving, hyσ]⟩
  have heq : designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) =
      S.ball i := by
    simpa only [QuantumCircuit.graphBall, ball] using
      (truncationRadius_eq_of_mem_crossingLabels hnear hcross).2.2
  rw [heq] at hxD hyD
  have hxcompact := Finset.mem_filter.mp (hnear hxP)
  have hball : S.ball i ⊆ S.A := by
    have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
      ⟨x, hxcompact.1, by simpa only [hdepth] using hxcompact.2,
        by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hxD⟩
    simpa only [ball, hgraph] using hb
  have hxl := hlead false x hxcompact.1 hxσ
  have hyl := hlead true y (hball hyD) hyσ
  have hxv := abs_le.mp (abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth i x hxD)
  have hyv := abs_le.mp (abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth i y hyD)
  have hsep := S.front_sum_lt_neg_lead g r hn hk hr hDpos hD
  simp only [orientedDepth, Bool.false_eq_true, ↓reduceIte] at hxl hyl
  omega

/-- A designated support cannot meet both physical receiving sides in any completed
history within the source horizon. This also excludes a direct near-to-far split
with no middle incidence. -/
theorem state_designatedSupport_not_near_far_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g : Fin S.K) (i : I) :
    ¬ ((designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.state h g) false).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.state h g) true).Nonempty) := by
  apply designatedSupport_not_near_far_domainGraph hT S hgraph hdepth g (h.1 g)
    (S.state h g) hn hk hr hDpos hD (S.state_near_subset_truncationSet h g hL) _ hclear i
  apply S.bandState_assigned_lead
  exact abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth

/-- A designated support cannot meet both physical receiving sides immediately
before an actual charge, including histories with an unusually long charge lead. -/
theorem old_designatedSupport_not_near_far_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g : Fin S.K) (i : I) :
    ¬ ((designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.oldChargeState h g) false).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.oldChargeState h g) true).Nonempty) := by
  apply designatedSupport_not_near_far_domainGraph hT S hgraph hdepth g (h.1 g)
    (S.oldChargeState h g) hn hk hr hDpos hD
    (S.oldChargeState_near_subset_truncationSet h g hL) _ hclear i
  apply S.oldChargeState_assigned_lead
  exact abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
