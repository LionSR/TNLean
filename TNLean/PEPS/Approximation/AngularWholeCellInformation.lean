/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProductConditionalSum
import TNLean.PEPS.Approximation.AngularInformationGeometry
import TNLean.PEPS.Approximation.AngularInformationBound

/-!
# Information before resetting a selected group of cells

The initial group consists of all cells touching the old ambient enlargement.
The new group is obtained by adding the finitely many further selected cells.
The state and exterior region remain fixed throughout the additions.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 692–732, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

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
    {L q : ℕ} (Ω : StateSpace L q) (E : Finset (Vertex L))
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
      FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
        Ω G E B ≤ Kcell)
    (hold : FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω
      (Finset.univ.filter (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold))
      E ≤ b₀) :
    FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω
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
      FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
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
  have hsum := FiniteProduct.mutualInformation_union_biUnion_le_of_conditional
    (fun _ : Vertex L ↦ Fin q) Ω B E G S (fun _ ↦ Kcell) hcost
  have hfinal := hsum.trans (add_le_add hold (le_refl (∑ _i ∈ S, Kcell)))
  simpa only [← hregion, Finset.sum_const, nsmul_eq_mul] using hfinal

end TNLean.PEPS.Approximation
