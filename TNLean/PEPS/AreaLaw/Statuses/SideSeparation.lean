/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Statuses.StatusContainment
import TNLean.PEPS.AreaLaw.Histories.BandMargins
import TNLean.PEPS.AreaLaw.Histories.GoodSampling
import TNLean.PEPS.AreaLaw.Statuses.PrefixFiniteFamily

/-!
# Designated supports cannot meet both receiving sides

The actual near side lies in the compact truncation set. A designated support
meeting it and the far side is therefore the base-radius graph ball. Clearance
puts that ball wholly inside the chosen color, where the unconditional lead
bounds apply to both sides. The source window margins separate these leads by
more than a ball diameter, excluding such a support for every history.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(1), lines 225–247, at `openai/math@adc7f124`.

## Scanner fronts inside the original collar

The near comparison threshold is the lower band endpoint plus the number of
completed advances. The far threshold is the upper endpoint minus that number.
Throughout the fill horizon, both thresholds lie below the original collar depth.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## One finite prefix family for all scanner fronts

The original region, depth function and collar depth determine a finite nested
family before any band, offset or round is chosen. Both deterministic comparison
fronts select members of this same family throughout the fill horizon.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, and Lemma 9.1(2), lines 243–250,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proof is written independently from the manuscript; no upstream Lean
proof is copied or adapted.
-/

section

open ManyBody (planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- The upper endpoint of each band lies below the original collar depth.
Source: OpenAI area-law manuscript, `08-scanner.tex`, `scanner:fronts`,
lines 83–124, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem upper_le {L : ℕ} (g : Fin S.K) (r : Fin S.m)
    (hL : 8 * S.K * S.m ≤ L) : S.upper g r ≤ (L : ℤ) := by
  have hg : g.val + 1 ≤ S.K := g.isLt
  have hgm := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 hg)
  have hr := r.isLt
  simp only [upper]
  exact_mod_cast (show 8 * g.val * S.m + 5 * S.m + r.val ≤ L by nlinarith)

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
private theorem designatedSupport_not_near_far_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (g r : ℕ) (σ : PhysicalPartition ↥Λ)
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
  have hcross : () ∈ ManyBody.crossingTerms
      (fun _ : Unit ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i))
      (receiving σ false) := by
    exact ManyBody.mem_crossingTerms.mpr ⟨⟨x, hxD, hxP⟩, y, hyD, by simp [receiving, hyσ]⟩
  have heq : designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) =
      S.ball i := by
    exact (truncationRadius_eq_of_mem_crossingTerms hnear hcross).2.2.trans
      (Finset.ext fun _ ↦ by simp [ball, ManyBody.mem_graphBall])
  rw [heq] at hxD hyD
  have hxcompact := Finset.mem_filter.mp (hnear hxP)
  have hball := ball_subset_of_mem_ball_planeDomainGraph hT S hgraph hdepth hclear hxD
    hxcompact.1 hxcompact.2
  have hxl := hlead false x hxcompact.1 hxσ
  have hyl := hlead true y (hball hyD) hyσ
  have hxv := abs_le.mp
    (abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball hT S hgraph hdepth i x hxD)
  have hyv := abs_le.mp
    (abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball hT S hgraph hdepth i y hyD)
  have hsep := S.front_sum_lt_neg_lead g r hn hk hr hDpos hD
  simp only [orientedDepth, Bool.false_eq_true, ↓reduceIte] at hxl hyl
  omega

/-- A designated support cannot meet both physical receiving sides in any completed
history within the source horizon. This also excludes a direct near-to-far split
with no middle incidence. -/
theorem state_designatedSupport_not_near_far_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
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
  apply designatedSupport_not_near_far_planeDomainGraph hT S hgraph hdepth g (h.1 g)
    (S.state h g) hn hk hr hDpos hD (S.state_near_subset_truncationSet h g hL) _ hclear i
  apply S.bandState_assigned_lead
  exact abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball hT S hgraph hdepth

/-- A designated support cannot meet both physical receiving sides immediately
before an actual charge, including histories with an unusually long charge lead. -/
theorem old_designatedSupport_not_near_far_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
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
  apply designatedSupport_not_near_far_planeDomainGraph hT S hgraph hdepth g (h.1 g)
    (S.oldChargeState h g) hn hk hr hDpos hD
    (S.oldChargeState_near_subset_truncationSet h g hL) _ hclear i
  apply S.oldChargeState_assigned_lead
  exact abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball hT S hgraph hdepth

end CollarScan
end TNLean.PEPS.AreaLaw.Scan

end

section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- Both positive-depth comparison thresholds stay below the original collar
depth throughout the fill horizon. Source: OpenAI area-law manuscript,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem front_comparison_thresholds_le {V I : Type*}
    (S : CollarScan V I) (g : Fin S.K) (r : Fin S.m) {t L : ℕ}
    (hn : 0 < S.n) (ht : t ≤ S.n * S.m) (hL : 8 * S.K * S.m ≤ L) :
    S.front g r t false - 1 ≤ (L : ℤ) ∧
      -S.front g r t true ≤ (L : ℤ) := by
  have hupper := S.upper_le g r hL
  have hshift : ((fillCount t false / S.n : ℕ) : ℤ) ≤ (S.m : ℤ) := by
    exact_mod_cast fillCount_div_le_window hn ht false
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hupper ⊢
  have hfar : 0 ≤ ((fillCount t true / S.n : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

end TNLean.PEPS.AreaLaw.Scan.CollarScan

end

section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- Both actual deterministic comparison fronts select members of the same
finite prefix family, fixed before the band, offset and round are chosen. -/
theorem front_positiveDepthPrefix_mem_fixed_family {V I : Type*}
    (S : CollarScan V I) {L : ℕ} (hn : 0 < S.n) (hL : 8 * S.K * S.m ≤ L) :
    let Q := fun i : Fin (L + 1) ↦ positiveDepthPrefix S.A S.depth (i.val : ℤ)
    ∀ (g : Fin S.K) (r : Fin S.m) (t : ℕ), t ≤ S.n * S.m →
      positiveDepthPrefix S.A S.depth (S.front g r t false - 1) ∈ Set.range Q ∧
      positiveDepthPrefix S.A S.depth (-S.front g r t true) ∈ Set.range Q := by
  dsimp only
  intro g r t ht
  have hfront := S.front_comparison_thresholds_le g r hn ht hL
  exact ⟨positiveDepthPrefix_mem_range_fin_of_le S.A S.depth hfront.1,
    positiveDepthPrefix_mem_range_fin_of_le S.A S.depth hfront.2⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan

end
