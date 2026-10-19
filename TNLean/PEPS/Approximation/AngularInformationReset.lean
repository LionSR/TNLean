/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.AngularInformationGeometry

/-!
# Information reset for the padded annular regions

The smaller ambient enlargements lie inside the physical selected-cell
region and enlarged exterior, with at least half the padding radius between
each core and the corresponding physical complement. Thus the original-gap
information reset applies whenever its width fits inside this buffer.

Source: polynomial-PEPS manuscript, Proposition 3.4,
`02-information.tex`, lines 729–745, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open Classical in
/-- **The information reset for the padded annular regions, with explicit constants.** The
original-gap information reset applies to the actual padded annular regions with the reset
width `C_p = resetWidth J Δ p` and the size threshold `L₀ = resetThreshold q J Δ p` of
Lemma 3.3.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 736–745, with the constants
of Lemma 3.3 at lines 606–608 and 612–630. -/
theorem angular_information_reset_of_resetThreshold_le (q : ℕ) (hq : 1 ≤ q)
    (J : ℝ) (hJ : 0 ≤ J) {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∀ L : ℕ, resetThreshold q J Δ p ≤ L →
      ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (o : ℝ × ℝ) (A E : Set (ℝ × ℝ)) (a' d s : ℝ),
          0 ≤ a' → 0 < d → 0 < s →
          let R : Finset (SquareLatticeVertex L L) := Finset.univ.filter
            (fun v ↦ sitePosition L v ∈
              AngularGrid.selectedRegion o (d * s) ((3 / 2) * a' * s) A)
          let C : Finset (SquareLatticeVertex L L) := Finset.univ.filter
            (fun v ↦ sitePosition L v ∈ AngularGrid.near ((3 / 2) * a' * s) E)
          let R₀ : Finset (SquareLatticeVertex L L) := Finset.univ.filter
            (fun v ↦ sitePosition L v ∈ AngularGrid.near (a' * s) A)
          let C₀ : Finset (SquareLatticeVertex L L) := Finset.univ.filter
            (fun v ↦ sitePosition L v ∈ AngularGrid.near (a' * s) E)
          Disjoint R C → ∀ b : ℝ, 0 ≤ b →
            FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
            resetWidth J Δ p * (1 + b + Real.log L) ≤ a' * s / 2 →
            FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤
              (L : ℝ) ^ (-p) := by
  have hreset :=
    SquareHamiltonian.information_reset_of_resetThreshold_le q hq J hJ (Δ := Δ) (p := p) hΔ hp
  intro L hL h E₀ Ω hΩ o A E a' d s ha' hd hs R C R₀ C₀ hRC b hb hI hw
  have hsub := AngularGrid.angular_core_subsets (o := o) Set.univ A E ha' hd hs
  have hR₀ : R₀ ⊆ R := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      (hsub.1 ⟨Set.mem_univ _, (Finset.mem_filter.mp hv).2⟩).2⟩
  have hC₀ : C₀ ⊆ C := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      (hsub.2 ⟨Set.mem_univ _, (Finset.mem_filter.mp hv).2⟩).2⟩
  apply hreset L hL h E₀ Ω hΩ R C R₀ C₀ hRC hR₀ hC₀ b hb hI
  · intro x hx y hy
    have hx' : sitePosition L x ∈ Set.univ ∩ AngularGrid.near (a' * s) A :=
      ⟨Set.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    have hy' : sitePosition L y ∈ Set.univ \
        AngularGrid.selectedRegion o (d * s) ((3 / 2) * a' * s) A :=
      ⟨Set.mem_univ _, fun hmem ↦
        hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hmem⟩)⟩
    have hdist := AngularGrid.angular_target_core_clearance (o := o) hd hs hx' hy'
    simpa only [dist_sitePosition_eq_supDist] using hw.trans_lt hdist
  · intro x hx y hy
    have hdist := AngularGrid.angular_exterior_core_clearance
      (Λ := Set.univ) (E := E) (a' := a') (s := s)
      (x := sitePosition L x) (y := sitePosition L y)
      ⟨Set.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      ⟨Set.mem_univ _, fun hmem ↦
        hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hmem⟩)⟩
    simpa only [dist_sitePosition_eq_supDist] using hw.trans_lt hdist

open Classical in
/-- The original-gap information reset applied to the actual padded annular
regions. The reset constant and size threshold precede every region, scale,
grid, Hamiltonian and ground vector. They are `resetWidth J Δ p` and
`resetThreshold q J Δ p` (`angular_information_reset_of_resetThreshold_le`).

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 729–745. -/
theorem exists_angular_information_reset (q : ℕ) (hq : 1 ≤ q)
    (J : ℝ) (hJ : 0 ≤ J) {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∃ Cp L₀ : ℝ, 0 < Cp ∧
      ∀ L : ℕ, L₀ ≤ L →
        ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
          h.IsGappedGroundState E₀ Ω Δ →
          ∀ (o : ℝ × ℝ) (A E : Set (ℝ × ℝ)) (a' d s : ℝ),
            0 ≤ a' → 0 < d → 0 < s →
            let R : Finset (SquareLatticeVertex L L) := Finset.univ.filter
              (fun v ↦ sitePosition L v ∈
                AngularGrid.selectedRegion o (d * s) ((3 / 2) * a' * s) A)
            let C : Finset (SquareLatticeVertex L L) := Finset.univ.filter
              (fun v ↦ sitePosition L v ∈ AngularGrid.near ((3 / 2) * a' * s) E)
            let R₀ : Finset (SquareLatticeVertex L L) := Finset.univ.filter
              (fun v ↦ sitePosition L v ∈ AngularGrid.near (a' * s) A)
            let C₀ : Finset (SquareLatticeVertex L L) := Finset.univ.filter
              (fun v ↦ sitePosition L v ∈ AngularGrid.near (a' * s) E)
            Disjoint R C → ∀ b : ℝ, 0 ≤ b →
              FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
              Cp * (1 + b + Real.log L) ≤ a' * s / 2 →
              FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤
                (L : ℝ) ^ (-p) :=
  ⟨resetWidth J Δ p, resetThreshold q J Δ p, resetWidth_pos hJ hΔ hp,
    angular_information_reset_of_resetThreshold_le q hq J hJ hΔ hp⟩

end TNLean.PEPS.Approximation
