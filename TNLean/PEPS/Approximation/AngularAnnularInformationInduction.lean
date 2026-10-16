/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.AngularInformationBound
import TNLean.PEPS.Approximation.AngularAnnularCells
import QICLean.Entropy.FiniteProductInformation

/-!
# The finite annular information induction

At each dyadic scale, the old selected cells and the current enlarged
exterior lie inside the two regions controlled at the preceding scale.
The first old group is empty. The exact finite set of new cells has one
uniform cardinality bound. A reset estimate at each scale consequently
gives the same information bound at every scale, including the last one.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 681–785, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The per-scale reset estimate is an explicit premise of this induction
lemma; it is supplied by the separate cell and information-reset estimates.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

open AngularGrid

open Classical in
/-- The literal annular induction with its per-scale reset estimate stated
explicitly. All physical inclusions, the initial empty group, the new-cell
count, and the final removal of padding follow from the geometric data.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 681–785. -/
theorem mutualInformation_le_of_annular_reset {L q : ℕ}
    (Ω : StateSpace L q) (hΩ : ‖Ω‖ = 1)
    {X E : Finset (SquareLatticeVertex L L)}
    {n t a a' d A₀ ε : ℝ} {V : Finset (ℝ × ℝ)} {m₀ : ℕ}
    (hn : 0 < n) (ha : 0 ≤ a) (ha' : 0 < a') (ha'a : a' < a / 100)
    (hd : 0 < d) (hda' : d < a' / 4) (hε : 0 ≤ ε)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X,
      dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n)
    (hV : V.card ≤ m₀)
    (hsep : AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n t a V)
    (c : DyadicCutoff n t) :
    let sample : Set (ℝ × ℝ) → Finset (SquareLatticeVertex L L) :=
      fun Z ↦ Finset.univ.filter (fun v ↦ sitePosition L v ∈ Z)
    let A : ℕ → Set (ℝ × ℝ) :=
      cumulativeLayer (sitePosition L '' X) n V c.last
    let s : ℕ → ℝ := dyadicScale n
    let R : ℕ → Set (ℝ × ℝ) → Finset (SquareLatticeVertex L L) :=
      fun j Z ↦ sample (selectedRegion (0, 0) (d * s j) ((3 / 2) * a' * s j) Z)
    let C : ℕ → Finset (SquareLatticeVertex L L) :=
      fun j ↦ sample (near ((3 / 2) * a' * s j) (sitePosition L '' E))
    let R₀ : ℕ → Finset (SquareLatticeVertex L L) :=
      fun j ↦ sample (near (a' * s j) (A j))
    let C₀ : ℕ → Finset (SquareLatticeVertex L L) :=
      fun j ↦ sample (near (a' * s j) (sitePosition L '' E))
    (∀ j : ℕ, j ≤ c.last → ∀ Aold : Set (ℝ × ℝ), Aold ⊆ A j →
      ∀ S : Finset (ℤ × ℤ),
        (∀ i, i ∈ S ↔
          touches (0, 0) (d * s j) ((3 / 2) * a' * s j) (A j) i ∧
          ¬ touches (0, 0) (d * s j) ((3 / 2) * a' * s j) Aold i) →
        S.card ≤ (m₀ + 1) * (2 * ⌈(max A₀ 2 + (3 / 2) * a') / d⌉₊ + 3) ^ 2 →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω (R j Aold) (C j) ≤ ε →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω (R₀ j) (C₀ j) ≤ ε) →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω X E ≤ ε := by
  classical
  intro sample A s R C R₀ C₀ hstep
  have hmono (P P' Q Q' : Finset (SquareLatticeVertex L L))
      (hP : P ⊆ P') (hQ : Q ⊆ Q') (hPQ : Disjoint P' Q') :
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω P Q ≤
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω P' Q' := by
    have hleft := FiniteProduct.mutualInformation_mono_left
      (fun _ ↦ Fin q) Ω P P' Q hP (hPQ.mono_right hQ)
    have hright := FiniteProduct.mutualInformation_mono_left
      (fun _ ↦ Fin q) Ω Q Q' P' hQ hPQ.symm
    exact hleft.trans (by simpa only [FiniteProduct.mutualInformation,
      Finset.union_comm, add_comm] using hright)
  have hsep' (j : ℕ) (hj : j ≤ c.last) (x : ℝ × ℝ) (hx : x ∈ A j)
      (y : ℝ × ℝ) (hy : y ∈ sitePosition L '' E) :
      (a / 2) * s j ≤ dist x y := by
    simpa only [div_mul_eq_mul_div] using
      cumulativeLayer_separation c hn.le ha hsep hj hx hy
  have hdisj (j : ℕ) (hj : j ≤ c.last) : Disjoint (R₀ j) (C₀ j) := by
    have hRC := angular_physical_disjoint (o := (0, 0)) Set.univ
      ha' ha'a hd hda' (dyadicScale_pos hn j) (hsep' j hj)
    have hcore := angular_core_subsets (o := (0, 0)) Set.univ (A j)
      (sitePosition L '' E) ha'.le hd (dyadicScale_pos hn j)
    exact Finset.disjoint_left.mpr fun v hvR hvC ↦
      Set.disjoint_left.mp hRC
        (hcore.1 ⟨Set.mem_univ _, (Finset.mem_filter.mp hvR).2⟩)
        (hcore.2 ⟨Set.mem_univ _, (Finset.mem_filter.mp hvC).2⟩)
  have hdiam' : ∀ x ∈ sitePosition L '' X, ∀ y ∈ sitePosition L '' X,
      dist x y ≤ A₀ * n := by
    simpa only [Set.forall_mem_image, Finset.mem_coe] using hdiam
  have hI : ∀ j : ℕ, j ≤ c.last →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω (R₀ j) (C₀ j) ≤ ε := by
    intro j
    induction j with
    | zero =>
        intro hj
        obtain ⟨S, hS, hcard⟩ := exists_annularLayer_selectedIndices
          (r := (3 / 2) * a') hn hd hdiam' hV (0, 0) c.last 0
        refine hstep 0 hj ∅ (Set.empty_subset _) S ?_ hcard ?_
        · simpa [A, s, touches, near] using hS
        · have hRempty : R 0 ∅ = ∅ := by
            simp [R, sample, selectedRegion, touches, near]
          simpa only [hRempty, FiniteProduct.mutualInformation, Finset.empty_union,
            FiniteProduct.entropy_empty (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω hΩ,
            zero_add, sub_self] using hε
    | succ j ih =>
        intro hj
        obtain ⟨S, hS, hcard⟩ := exists_annular_newIndices
          (r := (3 / 2) * a') hn hd hdiam' hV (0, 0) c.last j
        apply hstep (j + 1) hj (A j)
          (cumulativeLayer_mono _ _ _ _ (Nat.le_succ j)) S hS hcard
        have hscale : 2 * a' * s (j + 1) = a' * s j := by
          simpa only [s, mul_assoc, mul_left_comm] using
            congrArg (fun z : ℝ ↦ a' * z) (two_mul_dyadicScale_succ n j)
        have hR : R (j + 1) (A j) ⊆ R₀ j := fun v hv ↦
          Finset.mem_filter.mpr ⟨Finset.mem_univ v, by
            simpa only [hscale] using old_selectedRegion_subset
              (o := (0, 0)) (s := s (j + 1)) (A j) ha' hd hda'
              (dyadicScale_pos hn (j + 1)) (Finset.mem_filter.mp hv).2⟩
        have hC : C (j + 1) ⊆ C₀ j := fun v hv ↦
          Finset.mem_filter.mpr ⟨Finset.mem_univ v, by
            simpa only [hscale] using exterior_near_subset
              (s := s (j + 1)) (sitePosition L '' E) ha'.le
              (dyadicScale_pos hn (j + 1)).le (Finset.mem_filter.mp hv).2⟩
        exact (hmono _ _ _ _ hR hC (hdisj j ((Nat.le_succ j).trans hj))).trans
          (ih ((Nat.le_succ j).trans hj))
  have hX : X ⊆ R₀ c.last := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, sitePosition L v,
      by simpa only [A, cumulativeLayer_last hn.le] using
        (Set.mem_image_of_mem (sitePosition L) hv),
      by simpa only [dist_self] using
        mul_nonneg ha'.le (dyadicScale_pos hn c.last).le⟩
  have hE : E ⊆ C₀ c.last := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, sitePosition L v,
      Set.mem_image_of_mem (sitePosition L) hv,
      by simpa only [dist_self] using
        mul_nonneg ha'.le (dyadicScale_pos hn c.last).le⟩
  exact (hmono _ _ _ _ hX hE (hdisj c.last le_rfl)).trans (hI c.last le_rfl)

end TNLean.PEPS.Approximation
