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

**Scope restriction (sublinear collar bound):**
`angular_single_scale_reset_of_sublinearCollarBoundAt` and
`exists_angular_single_scale_reset_of_sublinearCollarBound` keep the collar estimate as an
explicit premise; see `docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 692–778, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open AngularGrid

/-- The clearance coefficient `c = (a/2 - 3a' - d) / d` of Proposition 3.4: the distance
`(a/2 - 3a' - d) s` between a selected cell and the enlarged exterior, in units of the cell
side `d s`.

Source: polynomial-PEPS manuscript, equation `eq:info-cell-clearance`, `02-information.tex`,
lines 716–723. -/
noncomputable def angularClearance (a a' d : ℝ) : ℝ := (a / 2 - 3 * a' - d) / d

/-- The size threshold of the reset at one annular scale: the larger of the cell-reset
threshold `angularCellResetThreshold a' d C_p C₁ M K` and the threshold
`resetThreshold q J Δ p` of Lemma 3.3. Here `C_p = resetWidth J Δ p` is the reset width of
Lemma 3.3, `M` bounds the number of new cells, and `C₁ = cellInformationConstant q c C_tpl N
C_a N_a`, `K = cellInformationExponent c C_tpl N C_a N_a` are the constants of Lemma 3.2 at the
clearance coefficient `c = angularClearance a a' d`, the collar threshold `N` and the
amplification constant and threshold `C_a`, `N_a`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`, lines 727–774. -/
noncomputable def angularSingleScaleThreshold (q : ℕ) (J Δ a a' d p Ctpl : ℝ) (N : ℕ)
    (Ca : ℝ) (Na M : ℕ) : ℝ :=
  max (angularCellResetThreshold a' d (resetWidth J Δ p)
      (cellInformationConstant q (angularClearance a a' d) Ctpl N Ca Na) M
      (cellInformationExponent (angularClearance a a' d) Ctpl N Ca Na))
    (resetThreshold q J Δ p)

/-- The single-scale reset threshold is at least `e`. -/
theorem exp_one_le_angularSingleScaleThreshold (q : ℕ) (J Δ a a' d p Ctpl : ℝ) (N : ℕ)
    (Ca : ℝ) (Na M : ℕ) :
    Real.exp 1 ≤ angularSingleScaleThreshold q J Δ a a' d p Ctpl N Ca Na M :=
  (exp_one_le_angularCellResetThreshold _ _ _ _ _ _).trans (le_max_left _ _)

open Classical in
/-- **Uniform information reset at one annular scale, with explicit constants.** Assume the
range-one sublinear collar bound with constant `C` and threshold `N`, and the range-one
amplification bound at the input constant `max(C, 1)` and order `1` with constant `C_a` and
threshold `N_a`. Let `M` bound the number of new cells. Then every slope
`D ≥ angularCellResetSlope (resetWidth J Δ p) a' d` and every size
`L ≥ angularSingleScaleThreshold q J Δ a a' d p C_tpl N C_a N_a M` give the information reset
at every scale `s ≥ D log L`. The threshold does not depend on `D`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 692–780, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem angular_single_scale_reset_of_sublinearCollarBoundAt
    (q : ℕ) (hq : 1 ≤ q) (J : ℝ) (hJ : 0 ≤ J)
    {Δ D₀ Ctpl C Ca a a' d p : ℝ} {N Na : ℕ} (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    (hamp : AreaLaw.AmplificationBoundAt q 1 J Δ (max C 1) 1 Ca Na)
    (ha' : 0 < a') (ha'a : a' < a / 100)
    (hd : 0 < d) (hda : d < a' / 4) (hd1 : d ≤ 1)
    (hp : 0 < p) (M : ℕ) {D : ℝ} (hD : angularCellResetSlope (resetWidth J Δ p) a' d ≤ D) :
    ∀ L : ℕ, angularSingleScaleThreshold q J Δ a a' d p Ctpl N Ca Na M ≤ (L : ℝ) →
      ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ s : ℝ, D * Real.log (L : ℝ) ≤ s →
          ∀ (o : ℝ × ℝ) (Aold A E : Set (ℝ × ℝ)), Aold ⊆ A →
            (∀ x ∈ A, ∀ y ∈ E, (a / 2) * s ≤ dist x y) →
            ∀ S : Finset (ℤ × ℤ),
              (∀ i, i ∈ S ↔
                touches o (d * s) ((3 / 2) * a' * s) A i ∧
                ¬ touches o (d * s) ((3 / 2) * a' * s) Aold i) →
              S.card ≤ M →
              let Rold : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈
                  selectedRegion o (d * s) ((3 / 2) * a' * s) Aold)
              let Cs : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ near ((3 / 2) * a' * s) E)
              let R₀ : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ near (a' * s) A)
              let C₀ : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ near (a' * s) E)
              FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q)
                Ω Rold Cs ≤ (L : ℝ) ^ (-p) →
              FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q)
                Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  let c := angularClearance a a' d
  have hc : 0 < c := div_pos (angular_clearance_pos ha' ha'a hda) hd
  set C₁ := cellInformationConstant q c Ctpl N Ca Na
  set K := cellInformationExponent c Ctpl N Ca Na
  have hC₁ : 0 < C₁ := cellInformationConstant_pos q c Ctpl N Ca Na
  have hK : 0 ≤ K := (cellInformationExponent_pos c Ctpl N Ca Na).le
  have hcell :=
    mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt hJ hcol hamp hc
  have hreset := angular_information_reset_of_resetThreshold_le q hq J hJ hΔ hp
  have hwidth := angular_reset_width_lt_of_cell_information (N := (M : ℝ)) ha' hd hd1
    (resetWidth_pos hJ hΔ hp) hC₁ (Nat.cast_nonneg M) hK hp hD
  intro L hL h E₀ Ω hΩ s hs o Aold A E hA hsep S hS hSN Rold Cs R₀ C₀ hold
  obtain ⟨hds, hw⟩ := hwidth L ((le_max_left _ _).trans hL) s hs
  have hs0 : 0 < s := (mul_pos_iff_of_pos_left hd).mp (zero_lt_one.trans_le hds)
  have hclear : ∀ x ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A,
      ∀ v ∈ Cs, c * (d * s) ≤ dist x (sitePosition L v) := by
    intro x hx v hv
    have hdist := angular_selectedRegion_clearance hd hs0 hsep hx (Finset.mem_filter.mp hv).2
    have hcoef : c * (d * s) = (a / 2 - 3 * a' - d) * s := by
      simp only [c, angularClearance]
      field_simp
    simpa only [hcoef] using hdist
  have hMI := hcell (d * s) hds o ((3 / 2) * a' * s) Aold A hA S hS
    L h E₀ Ω hΩ Cs ((L : ℝ) ^ (-p)) hclear hold
  let R : Finset (Vertex L) := Finset.univ.filter
    (fun v ↦ sitePosition L v ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A)
  have hRC : Disjoint R Cs := by
    apply Finset.disjoint_left.mpr
    intro v hv hvC
    have hdist := hclear (sitePosition L v) (Finset.mem_filter.mp hv).2 v hvC
    rw [dist_self] at hdist
    exact (not_le_of_gt (mul_pos hc (zero_lt_one.trans_le hds))) hdist
  have hcost : 0 ≤ C₁ * (1 + Real.log (d * s)) ^ K :=
    mul_nonneg hC₁.le (Real.rpow_nonneg (by linarith [Real.log_nonneg hds]) _)
  have hcard : (S.card : ℝ) ≤ M := by exact_mod_cast hSN
  let b := (L : ℝ) ^ (-p) + (M : ℝ) * (C₁ * (1 + Real.log (d * s)) ^ K)
  have hb : 0 ≤ b := add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L) _)
    (mul_nonneg (Nat.cast_nonneg M) hcost)
  have hbound : FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω R Cs ≤ b :=
    hMI.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hcost))
  have hw' : resetWidth J Δ p * (1 + b + Real.log (L : ℝ)) ≤ a' * s / 2 := by
    dsimp [b]
    nlinarith only [hw, mul_pos ha' hs0]
  exact hreset L ((le_max_right _ _).trans hL) h E₀ Ω hΩ o A E a' d s
    ha'.le hd hs0 hRC b hb hbound hw'

open Classical in
/-- Uniform information reset at one annular scale under the sublinear collar
bound. The cell-count bound and geometric constants are fixed before the
system size, Hamiltonian, state, scale and ambient regions. The constants are
`angularCellResetSlope (resetWidth J Δ p) a' d` and `angularSingleScaleThreshold`
(`angular_single_scale_reset_of_sublinearCollarBoundAt`). The same exterior
sample occurs in the old information bound and the selected-cell estimate.

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
  obtain ⟨C, Ncol, hcol⟩ := hcol
  obtain ⟨Ca, Na, hamp⟩ := AreaLaw.amplificationBound (q := q) (R := 1) (J := J) hΔ (max C 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) 1 le_rfl
  exact ⟨_, _, one_le_angularCellResetSlope _ _ _,
    exp_one_le_angularSingleScaleThreshold q J Δ a a' d p Ctpl Ncol Ca Na N,
    angular_single_scale_reset_of_sublinearCollarBoundAt q hq J hJ hΔ hcol hamp
      ha' ha'a hd hda hd1 hp N le_rfl⟩

end TNLean.PEPS.Approximation
