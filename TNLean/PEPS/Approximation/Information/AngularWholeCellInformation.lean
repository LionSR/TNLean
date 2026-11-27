/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionConditionalInformation
import TNLean.PEPS.Approximation.Information.AngularInformationGeometry
import TNLean.PEPS.Approximation.Information.AngularInformationBound
import TNLean.PEPS.Approximation.Information.SquareCellConditionalInformation
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Information before resetting a selected group of cells

The initial group consists of all cells touching the old ambient enlargement.
The new group is obtained by adding the finitely many further selected cells.
The state and exterior region remain fixed throughout the additions.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 692–732, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.

## Information of a selected group of square-lattice cells

The original ground state satisfies a uniform information bound for each finite
group of newly selected cells. The old selected region remains in the conditioning
system, and the constants are independent of the subsequent grid and Hamiltonian.
They are the named constants `cellInformationConstant` and `cellInformationExponent` of
Lemma 3.2 (`mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt`).

**Scope restriction (sublinear collar bound):** The sublinear collar estimate is
an explicit premise. This theorem supplies the corresponding conditional step in
polynomial-PEPS Proposition 3.4; it does not derive the collar estimate. See
`docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Source: polynomial-PEPS manuscript, Lemma 3.2 and Proposition 3.4,
`02-information.tex`, lines 163–311 and 692–732, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (Config Qudits SquareLatticeVertex)

section


namespace TNLean.PEPS.Approximation

open AngularGrid

open Classical in
/-- A uniform cell conditional-information estimate bounds the information
of the selected physical region by the old information plus one cost per new
cell. The conditioning systems are arbitrary unions of whole grid cells.
Positive ambient clearance supplies the required physical disjointness.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 692–732.
The analytic cell estimate is an explicit premise of this finite summation. -/
theorem mutualInformation_selectedRegion_le_of_cell_bound
    {L q : ℕ} (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)))
    (E : Finset (Vertex L))
    {o : ℝ × ℝ} {s r c b₀ Kcell : ℝ} (hs : 0 < s) (hc : 0 < c)
    {Aold A : Set (ℝ × ℝ)} (hA : Aold ⊆ A) (S : Finset (ℤ × ℤ))
    (hS : ∀ i, i ∈ S ↔ touches o s r A i ∧ ¬ touches o s r Aold i)
    (hclear : ∀ x ∈ selectedRegion o s r A, ∀ v ∈ E,
      c * s ≤ dist x (sitePosition L v))
    (hcell : ∀ i ∈ S, ∀ I : Set (ℤ × ℤ), i ∉ I →
      let G : Finset (Vertex L) :=
        Finset.univ.filter (fun v ↦ sitePosition L v ∈ cell o s i)
      let B : Finset (Vertex L) :=
        Finset.univ.filter (fun v ↦ owner o s (sitePosition L v) ∈ I)
      E ⊆ (G ∪ B)ᶜ →
      (∀ x ∈ closure (cell o s i), ∀ v ∈ E,
        c * s ≤ dist x (sitePosition L v)) →
      ManyBody.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
        Ω G E B ≤ Kcell)
    (hold : ManyBody.regionMutualInformation Ω
      (Finset.univ.filter (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold))
      E ≤ b₀) :
    ManyBody.regionMutualInformation Ω
      (Finset.univ.filter (fun v ↦ sitePosition L v ∈ selectedRegion o s r A)) E ≤
        b₀ + (S.card : ℝ) * Kcell := by
  classical
  let G : (ℤ × ℤ) → Finset (Vertex L) :=
    fun i ↦ Finset.univ.filter (fun v ↦ sitePosition L v ∈ cell o s i)
  let B : Finset (Vertex L) :=
    Finset.univ.filter (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold)
  have hregion : Finset.univ.filter
      (fun v ↦ sitePosition L v ∈ selectedRegion o s r A) = B ∪ S.biUnion G := by
    ext v
    simp only [B, G, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro ⟨i, hi, hv⟩
      by_cases holdi : touches o s r Aold i
      · exact Or.inl ⟨i, holdi, hv⟩
      · exact Or.inr ⟨i, (hS i).mpr ⟨hi, holdi⟩, hv⟩
    · rintro (hv | ⟨i, hi, hv⟩)
      · exact selectedRegion_mono hA hv
      · exact ⟨i, ((hS i).mp hi).1, hv⟩
  have hconditioning (t : Finset (ℤ × ℤ)) : Finset.univ.filter
      (fun v ↦ owner o s (sitePosition L v) ∈
        ({i | touches o s r Aold i} ∪ (t : Set (ℤ × ℤ)))) = B ∪ t.biUnion G := by
    ext v
    simp only [B, G, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion, Set.mem_union, Set.mem_ofPred_eq,
      Finset.mem_coe, mem_selectedRegion_iff_touches_owner hs]
    constructor
    · rintro (ho | ht)
      · exact Or.inl ho
      · exact Or.inr ⟨owner o s (sitePosition L v), ht, mem_cell_owner hs⟩
    · rintro (ho | ⟨i, hi, hv⟩)
      · exact Or.inl ho
      · exact Or.inr (by simpa only [owner_eq_of_mem_cell hs hv] using hi)
  have hexterior : ∀ v ∈ E, sitePosition L v ∉ selectedRegion o s r A := by
    intro v hv hvin
    have hzero := hclear (sitePosition L v) hvin v hv
    exact (not_le_of_gt (mul_pos hc hs)) (by simpa only [dist_self] using hzero)
  have hclosure (i : ℤ × ℤ) (hi : i ∈ S) :
      ∀ x ∈ closure (cell o s i), ∀ v ∈ E, c * s ≤ dist x (sitePosition L v) := by
    intro x hx v hv
    apply selected_cell_closure_clearance
      (C := sitePosition L '' (E : Set (Vertex L))) ((hS i).mp hi).1
      ?_ x hx (sitePosition L v) (Set.mem_image_of_mem _ hv)
    rintro y hy z ⟨w, hw, rfl⟩
    exact hclear y hy w hw
  have hcost : ∀ i ∈ S, ∀ t : Finset (ℤ × ℤ), t ⊆ S → i ∉ t →
      ManyBody.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
        Ω (G i) E (B ∪ t.biUnion G) ≤ Kcell := by
    intro i hi t hts hit
    have hnot : i ∉ ({j | touches o s r Aold j} ∪ (t : Set (ℤ × ℤ))) :=
      not_or.mpr ⟨((hS i).mp hi).2, hit⟩
    rw [← hconditioning t]
    convert hcell i hi _ hnot ?_ (hclosure i hi) using 1
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro v hv
      simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact fun hmem ↦ hexterior v hv (hmem.elim
        (fun hvi ↦ ⟨i, ((hS i).mp hi).1, hvi⟩)
        (fun howner ↦ howner.elim
          (fun ho ↦ selectedRegion_mono hA
            ((mem_selectedRegion_iff_touches_owner hs).mpr ho))
          (fun ht ↦ ⟨owner o s (sitePosition L v),
            ((hS _).mp (hts ht)).1, mem_cell_owner hs⟩)))
  have hsum := ManyBody.regionMutualInformation_union_biUnion_le_of_conditional
    (fun _ : Vertex L ↦ Fin q) Ω B E G S (fun _ ↦ Kcell) hcost
  have hfinal := hsum.trans (add_le_add hold (le_refl (∑ _i ∈ S, Kcell)))
  simpa only [← hregion, Finset.sum_const, nsmul_eq_mul] using hfinal

end TNLean.PEPS.Approximation

end

section

open scoped Matrix.Norms.L2Operator


open ManyBody (IsGapped groundSpace SquareInteraction)

namespace TNLean.PEPS.Approximation

open AngularGrid

open Classical in
/-- **Information of a selected group of cells, with named constants.** Under the range-one
sublinear collar bound with constant `C` and threshold `N`, and the range-one amplification
bound at the input constant `max(C, 1)` and order `1` with constant `C_a` and threshold `N_a`,
adding the newly selected physical cells raises the information with the exterior by at most
`C₁ (1 + log s) ^ K` per cell, with `C₁ = cellInformationConstant q c C_tpl N C_a N_a` and
`K = cellInformationExponent c C_tpl N C_a N_a` of Lemma 3.2.

Source: polynomial-PEPS manuscript, Lemma 3.2 and Proposition 3.4,
`02-information.tex`, lines 161–178 and 713–734. The sublinear collar bound is
an explicit premise of this intermediate implication. -/
theorem mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt
    {q : ℕ} {J Δ D₀ Ctpl C Ca : ℝ} {N Na : ℕ}
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    (hamp : AreaLaw.AmplificationBoundAt q 1 J Δ (max C 1) 1 Ca Na)
    {c : ℝ} (hc : 0 < c) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (r : ℝ) (Aold A : Set (ℝ × ℝ)),
      Aold ⊆ A → ∀ S : Finset (ℤ × ℤ),
        (∀ i, i ∈ S ↔ touches o s r A i ∧ ¬ touches o s r Aold i) →
        ∀ (L : ℕ) (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
            (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ)
            (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
          ∀ (E : Finset (Vertex L)) (b₀ : ℝ),
            (∀ x ∈ selectedRegion o s r A, ∀ v ∈ E,
              c * s ≤ dist x (sitePosition L v)) →
            ManyBody.regionMutualInformation Ω
              (Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold)) E ≤ b₀ →
            ManyBody.regionMutualInformation Ω
              (Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ selectedRegion o s r A)) E ≤
              b₀ + (S.card : ℝ) * (cellInformationConstant q c Ctpl N Ca Na *
                (1 + Real.log s) ^ cellInformationExponent c Ctpl N Ca Na) := by
  have hcell :=
    cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt hcol hamp hc
  intro s hs o r Aold A hA S hS L h hh hhJ E₀ Ω hΩ hgap hspan E b₀ hclear hold
  exact mutualInformation_selectedRegion_le_of_cell_bound Ω E
    (zero_lt_one.trans_le hs) hc hA S hS hclear
    (fun i _ I hi ↦ hcell s hs o i I hi L h hh hhJ E₀ Ω hΩ hgap hspan E) hold

open Classical in
/-- The original-gap collar hypothesis gives uniform information costs for
adding the actual newly selected physical cells. The constants precede the
scale, grid, ambient sets, physical Hamiltonian, ground vector and exterior.
The old information estimate is retained as the induction input. The constants
are `cellInformationConstant` and `cellInformationExponent`
(`mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt`), at the collar
constant and threshold and at the amplification constant and threshold
`collarAmplificationConstant` and `collarAmplificationThreshold`.

Source: polynomial-PEPS manuscript, Lemma 3.2 and Proposition 3.4,
`02-information.tex`, lines 163–311 and 692–732. The sublinear collar bound is
an explicit premise of this intermediate implication. -/
theorem exists_mutualInformation_selectedRegion_le_square_of_sublinearCollarBound
    {q : ℕ} {J Δ D₀ Ctpl : ℝ} (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBound q 1 J Δ D₀ Ctpl)
    {c : ℝ} (hc : 0 < c) :
    ∃ C₁ K : ℝ, 0 < C₁ ∧ 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (r : ℝ) (Aold A : Set (ℝ × ℝ)),
        Aold ⊆ A → ∀ S : Finset (ℤ × ℤ),
          (∀ i, i ∈ S ↔ touches o s r A i ∧ ¬ touches o s r Aold i) →
          ∀ (L : ℕ) (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
              (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ)
              (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))),
            ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
            groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
            ∀ (E : Finset (Vertex L)) (b₀ : ℝ),
              (∀ x ∈ selectedRegion o s r A, ∀ v ∈ E,
                c * s ≤ dist x (sitePosition L v)) →
              ManyBody.regionMutualInformation Ω
                (Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold)) E ≤ b₀ →
              ManyBody.regionMutualInformation Ω
                (Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ selectedRegion o s r A)) E ≤
                b₀ + (S.card : ℝ) * (C₁ * (1 + Real.log s) ^ K)
 := by
  obtain ⟨C, N, Ca, Na, hcol, hamp⟩ :=
    exists_sublinearCollarBoundAt_amplificationBoundAt hΔ hcol
  exact ⟨_, _, cellInformationConstant_pos q c Ctpl N Ca Na,
    (cellInformationExponent_pos c Ctpl N Ca Na).le,
    mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt hcol hamp hc⟩

end TNLean.PEPS.Approximation

end
