/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth

/-!
# Target and positive-depth receiving regions

For a nonempty finite target \(T\) and a chosen color \(A\), put \(X=A\cap T\).
At every completed fill–charge history, and immediately before its next charge,
\(X\) remains on the near side. Adjoining \(X\) to the positive-depth near
region recovers the full near region; the same holds for the union of the near
and middle regions. The far region is the complement of this latter union in
the physical domain.

## Main statements

- `CollarScan.state_receiving_regions`: the three region identities after a
  completed history.
- `CollarScan.oldChargeState_receiving_regions`: the identities after the next
  deterministic fill and before its charge.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–24 and 83–98, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

/-- If the target remains near and contains every nonpositive-depth near or middle
site, adjoining it to the positive-depth regions recovers the full regions.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 21–24 and 83–98,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
private theorem target_positiveNear_regions
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) (depth : V → ℤ) (σ : PhysicalPartition V)
    (hX : X ⊆ receiving σ false)
    (hnonpos : ∀ x, x ∈ receiving σ false ∪ middle σ → depth x ≤ 0 → x ∈ X) :
    receiving σ false = X ∪ positiveNear depth σ ∧
    receiving σ false ∪ middle σ = X ∪ positiveNearMiddle depth σ ∧
    receiving σ true = (X ∪ positiveNearMiddle depth σ)ᶜ := by
  constructor
  · ext x
    simp only [Finset.mem_union, positiveNear, Finset.mem_filter]
    grind
  · have hcases (x : V) : σ x = none ∨ σ x = some false ∨ σ x = some true :=
      (show ∀ s : Option Bool, s = none ∨ s = some false ∨ s = some true from by decide) (σ x)
    grind [positiveNearMiddle, receiving, middle, Finset.mem_compl]

/-- Ambient depth identifies the nonpositive part of a persistent physical partition
with the target. Source: OpenAI area-law manuscript, `08-scanner.tex`, lines
21–24 and 83–98, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
private theorem target_positiveNear_regions_of_ambientDepth
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) (depth : Site Λ → ℤ)
    (hdepth : depth = fun x ↦ ambientDepth T hT x.val)
    (σ : PhysicalPartition (Site Λ))
    (hX : (A.filter fun x ↦ x.val ∈ T) ⊆ receiving σ false)
    (hfar : ∀ x, x ∉ A → σ x = some true) :
    let X := A.filter fun x ↦ x.val ∈ T
    receiving σ false = X ∪ positiveNear depth σ ∧
    receiving σ false ∪ middle σ = X ∪ positiveNearMiddle depth σ ∧
    receiving σ true = (X ∪ positiveNearMiddle depth σ)ᶜ := by
  intro X
  refine target_positiveNear_regions X depth σ hX
    (fun x hx hd ↦ Finset.mem_filter.mpr ⟨?_, ?_⟩)
  case refine_1 => grind [receiving, middle]
  case refine_2 =>
    rw [hdepth] at hd
    simpa only [ambientDilation_zero] using
      (ambientDepth_le_iff_mem_dilation T hT x.val 0).mp hd

namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The chosen-color target remains on the near side of every actual completed history.
Source: OpenAI, A two-dimensional area law from a global spectral gap,
08-scanner.tex, lines 21–24 and 83–98, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem state_target_subset_receiving_near
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X : Finset (Site Λ) := S.A.filter fun x ↦ x.val ∈ T
    X ⊆ receiving (S.state h g) false := by
  intro X x hx
  obtain ⟨hxA, hxT⟩ := Finset.mem_filter.mp hx
  simp only [receiving, Finset.mem_filter, Finset.mem_univ, true_and]
  apply S.bandState_of_initial_assigned
  have hd : S.depth x ≤ 0 := by
    rw [hdepth]
    exact (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
      (by simpa only [ambientDilation_zero] using hxT)
  simp [initialPartition, hxA, show S.depth x ≤ S.lower g (h.1 g) from
    hd.trans (by unfold lower; positivity)]

/-- The target remains near after the deterministic fill and before a charge.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 21–24 and 83–98,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem oldChargeState_target_subset_receiving_near
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X : Finset (Site Λ) := S.A.filter fun x ↦ x.val ∈ T
    X ⊆ receiving (S.oldChargeState h g) false := by
  intro X x hx
  obtain ⟨hxA, hxT⟩ := Finset.mem_filter.mp hx
  simp only [receiving, Finset.mem_filter, Finset.mem_univ, true_and]
  apply S.oldChargeState_of_initial_assigned h g
  have hd : S.depth x ≤ 0 := by
    rw [hdepth]
    exact (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
      (by simpa only [ambientDilation_zero] using hxT)
  simp [initialPartition, hxA, show S.depth x ≤ S.lower g (h.1 g) from
    hd.trans (by unfold lower; positivity)]

/-- The receiving regions after a completed history are obtained by adjoining the
chosen-color target to their positive-depth parts. The far region is the complement
of the target together with the positive-depth near and middle regions.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 21–24 and 83–98,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem state_receiving_regions
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    receiving (S.state h g) false = X ∪ positiveNear S.depth (S.state h g) ∧
    receiving (S.state h g) false ∪ middle (S.state h g) =
      X ∪ positiveNearMiddle S.depth (S.state h g) ∧
    receiving (S.state h g) true = (X ∪ positiveNearMiddle S.depth (S.state h g))ᶜ := by
  refine target_positiveNear_regions_of_ambientDepth hT S.A S.depth hdepth (S.state h g)
    (state_target_subset_receiving_near hT S hdepth h g) (fun x hx ↦ ?_)
  apply S.bandState_of_initial_assigned
  simp [initialPartition, hx]

/-- Immediately before a charge, adjoining the chosen-color target to the
positive-depth near and middle regions recovers the full near and middle regions;
the far region is their complement.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 21–24 and 83–98,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem oldChargeState_receiving_regions
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    receiving (S.oldChargeState h g) false =
      X ∪ positiveNear S.depth (S.oldChargeState h g) ∧
    receiving (S.oldChargeState h g) false ∪ middle (S.oldChargeState h g) =
      X ∪ positiveNearMiddle S.depth (S.oldChargeState h g) ∧
    receiving (S.oldChargeState h g) true =
      (X ∪ positiveNearMiddle S.depth (S.oldChargeState h g))ᶜ := by
  refine target_positiveNear_regions_of_ambientDepth hT S.A S.depth hdepth
    (S.oldChargeState h g) (oldChargeState_target_subset_receiving_near hT S hdepth h g)
    (fun x hx ↦ ?_)
  apply S.oldChargeState_of_initial_assigned h g
  simp [initialPartition, hx]

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
