/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularWholeCellInformationFromCollar
import TNLean.PEPS.Approximation.AngularResetWidthFromCellInformation
import TNLean.PEPS.Approximation.AngularInformationReset

/-!
# Uniform information reset at a single annular scale

A fixed bound on the number of new cells gives one logarithmic lower scale
for the information reset. The old region and every new cell are compared
against the same physical sample of the enlarged ambient exterior.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 692–778, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open AngularGrid

open Classical in
/-- Uniform information reset at one annular scale under the sublinear collar
bound. The cell-count bound and geometric constants are fixed before the
system size, Hamiltonian, state, scale and ambient regions. The same exterior
sample occurs in the old information bound and the selected-cell estimate.

**Scope restriction (sublinear collar bound):** The collar estimate remains an
explicit premise; see `docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 692–778, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_angular_single_scale_reset_of_sublinearCollarBound
    (q : ℕ) (hq : 1 ≤ q) (J : ℝ) (hJ : 0 ≤ J)
    {Δ D₀ Ctpl a a' d p : ℝ} (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBound q 1 J Δ D₀ Ctpl)
    (ha' : 0 < a') (ha'a : a' < a / 100)
    (hd : 0 < d) (hda : d < a' / 4) (hd1 : d ≤ 1)
    (hp : 0 < p) (N : ℕ) :
    ∃ D L₀ : ℝ, 1 ≤ D ∧ Real.exp 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ (L : ℝ) →
        ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
          h.IsGappedGroundState E₀ Ω Δ →
          ∀ s : ℝ, D * Real.log (L : ℝ) ≤ s →
            ∀ (o : ℝ × ℝ) (Aold A E : Set (ℝ × ℝ)), Aold ⊆ A →
              (∀ x ∈ A, ∀ y ∈ E, (a / 2) * s ≤ dist x y) →
              ∀ S : Finset (ℤ × ℤ),
                (∀ i, i ∈ S ↔
                  touches o (d * s) ((3 / 2) * a' * s) A i ∧
                  ¬ touches o (d * s) ((3 / 2) * a' * s) Aold i) →
                S.card ≤ N →
                let Rold : Finset (Vertex L) := Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈
                    selectedRegion o (d * s) ((3 / 2) * a' * s) Aold)
                let C : Finset (Vertex L) := Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ near ((3 / 2) * a' * s) E)
                let R₀ : Finset (Vertex L) := Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ near (a' * s) A)
                let C₀ : Finset (Vertex L) := Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ near (a' * s) E)
                FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q)
                  Ω Rold C ≤ (L : ℝ) ^ (-p) →
                FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q)
                  Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  let c := (a / 2 - 3 * a' - d) / d
  have hc : 0 < c := div_pos (angular_clearance_pos ha' ha'a hda) hd
  obtain ⟨C₁, K, hC₁, hK, hcell⟩ :=
    exists_mutualInformation_selectedRegion_le_square_of_sublinearCollarBound hJ hΔ hcol hc
  obtain ⟨Cp, Lr, hCp, hreset⟩ := exists_angular_information_reset q hq J hJ hΔ hp
  obtain ⟨D, Lw, hD, hLw, hwidth⟩ :=
    exists_angular_reset_width_lt_of_cell_information a' d Cp C₁ N K p
      ha' hd hd1 hCp hC₁ (Nat.cast_nonneg N) hK hp
  refine ⟨D, max Lw Lr, hD, hLw.trans (le_max_left _ _), ?_⟩
  intro L hL h E₀ Ω hΩ s hs o Aold A E hA hsep S hS hSN Rold C R₀ C₀ hold
  obtain ⟨hds, hw⟩ := hwidth L ((le_max_left _ _).trans hL) s hs
  have hs0 : 0 < s := (mul_pos_iff_of_pos_left hd).mp (zero_lt_one.trans_le hds)
  have hclear : ∀ x ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A,
      ∀ v ∈ C, c * (d * s) ≤ dist x (sitePosition L v) := by
    intro x hx v hv
    have hdist := angular_selectedRegion_clearance hd hs0 hsep hx (Finset.mem_filter.mp hv).2
    have hcoef : c * (d * s) = (a / 2 - 3 * a' - d) * s := by
      dsimp [c]
      field_simp
    simpa only [hcoef] using hdist
  have hMI := hcell (d * s) hds o ((3 / 2) * a' * s) Aold A hA S hS
    L h E₀ Ω hΩ C ((L : ℝ) ^ (-p)) hclear hold
  let R : Finset (Vertex L) := Finset.univ.filter
    (fun v ↦ sitePosition L v ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A)
  have hRC : Disjoint R C := by
    apply Finset.disjoint_left.mpr
    intro v hv hvC
    have hdist := hclear (sitePosition L v) (Finset.mem_filter.mp hv).2 v hvC
    rw [dist_self] at hdist
    exact (not_le_of_gt (mul_pos hc (zero_lt_one.trans_le hds))) hdist
  have hcost : 0 ≤ C₁ * (1 + Real.log (d * s)) ^ K :=
    mul_nonneg hC₁.le (Real.rpow_nonneg (by linarith [Real.log_nonneg hds]) _)
  have hcard : (S.card : ℝ) ≤ N := by exact_mod_cast hSN
  let b := (L : ℝ) ^ (-p) + (N : ℝ) * (C₁ * (1 + Real.log (d * s)) ^ K)
  have hb : 0 ≤ b := add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L) _)
    (mul_nonneg (Nat.cast_nonneg N) hcost)
  have hbound : FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω R C ≤ b :=
    hMI.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hcost))
  have hw' : Cp * (1 + b + Real.log (L : ℝ)) ≤ a' * s / 2 := by
    dsimp [b]
    nlinarith only [hw, mul_pos ha' hs0]
  exact hreset L ((le_max_right _ _).trans hL) h E₀ Ω hΩ o A E a' d s
    ha'.le hd hs0 hRC b hb hbound hw'

end TNLean.PEPS.Approximation
