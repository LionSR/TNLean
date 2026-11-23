/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Hamiltonian.Models
import TNLean.Lattice.Sheet.RegionalOperatorForms
import TNLean.Lattice.Sheet.SupportedSchmidtRank
import TNLean.Lattice.Sheet.LeftSupportedSchmidtRank

/-!
# Nearest-neighbour edges at two cuts of a finite chain

The cuts are immediately after sites u and v, with u < v. The three regions are
[0,u+1), [u+1,v+1), and the complement of their union. A valid edge r acts on
[r,r+2), and the condition r+1 < L makes both sites actual chain sites.

This is the elementary support classification needed for ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut` and `item:small-sr` (local source lines 806–831),
and the algebraic step in `prop:Cheby-AGSP-eff` (lines 1324–1332). The convention
here agrees with the explicitly named cuts (i1,i1+1) and (i2,i2+1).
Adjacent cuts are allowed; their crossing supports share the middle site.

## Bond operators at two cuts

A family of operators supported on the bonds of a finite chain admits one
collection of three regional families and two crossing factors. Every
ordinary bond operator is the sum of its three regional terms. The same
crossing factors satisfy the tensor identities and the rank bound q².
All choices depend only on the operator family and the cuts.

This statement concerns the literal bond family, with one label for each
edge. The grouped window operators, their coefficient counts, cut movement
and matrix product operator construction are separate assertions.

### References

Supporting locality algebra for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines 1324–1332.

## Two windows with independently supported bulk operators

The two windows retain their individual nearest-neighbour terms and the three
bulk operators retain their given supports. The same two crossing factors
satisfy both tensor identities and the bound q². In particular, when the
windows touch, the middle bulk support is a singleton.

### References

ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1332.
-/

section

open ManyBody (interval interval_mono mem_interval)

namespace TNLean.MPS.AreaLaw

/-- Nearest-neighbour supports at cuts immediately following u and v.
The edge indexed by r has interval support [r,r+2).
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut` and `item:small-sr`, lines 806–831. -/
theorem interval_edge_classification_of_lt
    {L u v : ℕ} (huv : u < v) (hv : v + 1 < L) :
    interval L u (u + 2) ⊆
        interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1) ∧
      interval L u (u + 2) ∩ interval L 0 (u + 1) =
        {⟨u, by omega⟩} ∧
      Disjoint (interval L v (v + 2)) (interval L 0 (u + 1)) ∧
      interval L v (v + 2) ∩ interval L (u + 1) (v + 1) =
        {⟨v, by omega⟩} ∧
      ∀ r : ℕ, r + 1 < L → r ≠ u → r ≠ v →
        interval L r (r + 2) ⊆ interval L 0 (u + 1) ∨
        interval L r (r + 2) ⊆ interval L (u + 1) (v + 1) ∨
        interval L r (r + 2) ⊆
          (interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1))ᶜ := by
  classical
  have hUnion (x : Fin L) :
      x ∈ interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1) ↔
        x.val < v + 1 := by
    simp only [Finset.mem_union, mem_interval]
    omega
  have hOutside (x : Fin L) :
      x ∈ (interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1))ᶜ ↔
        v + 1 ≤ x.val := by
    rw [Finset.mem_compl, hUnion]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply (hUnion x).mpr
    have hx' := mem_interval.mp hx
    omega
  · ext x
    simp only [Finset.mem_inter, mem_interval, Finset.mem_singleton, Fin.ext_iff]
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    have hxr := mem_interval.mp hx
    have hxl := mem_interval.mp hx'
    omega
  · ext x
    simp only [Finset.mem_inter, mem_interval, Finset.mem_singleton, Fin.ext_iff]
    omega
  · intro r _hr hru hrv
    by_cases hleft : r < u
    · left
      exact interval_mono (Nat.zero_le r) (by omega)
    · by_cases hmiddle : r < v
      · right
        left
        exact interval_mono (by omega) (by omega)
      · right
        right
        intro x hx
        apply (hOutside x).mpr
        have hx' := mem_interval.mp hx
        omega

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix QuantumCircuit
open scoped Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Actual two crossing factors and three regional families of the terms of a
nearest-neighbour bond interaction, all in one three-region partition.
Supporting locality algebra for ALVV, arXiv:1602.08828v2, eq:H-mid-cut,
lines 810–821, and prop:Cheby-AGSP-eff, lines 1324–1332. -/
theorem exists_threeSplit_edge_factors
    {L q : ℕ}
    (H : ManyBody.BondInteraction L q)
    (u v : Fin (L - 1)) (huv : u.val < v.val)
    {T E : Finset (Fin L)} (hT : T = interval L 0 (u.val + 1))
    (hE : E = interval L (u.val + 1) (v.val + 1)) (hTE : Disjoint T E) :
    ∃ (HL : Fin (L - 1) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (HM : Fin (L - 1) → Matrix (E → Fin q) (E → Fin q) ℂ)
      (HR : Fin (L - 1) → Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ)
      (VR : Matrix ((E → Fin q) × ({x // x ∉ T ∪ E} → Fin q))
        ((E → Fin q) × ({x // x ∉ T ∪ E} → Fin q)) ℂ),
      (∀ r, r ≠ u → r ≠ v →
        (H.term r).submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
          (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
              (1 : Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
      (H.term u).submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
        UL ⊗ₖ (1 : Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ) ∧
      (H.term v).submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            ({x // x ∉ T ∪ E} → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            ({x // x ∉ T ∪ E} → Fin q)).symm ∧
      operatorSchmidtRank UL ≤ q ^ 2 ∧ operatorSchmidtRank VR ≤ q ^ 2 := by
  classical
  subst hT hE
  set T := interval L 0 (u.val + 1)
  set E := interval L (u.val + 1) (v.val + 1)
  set g := threeSplit q T E hTE
  have hv : v.val + 1 < L := by omega
  obtain ⟨huD, huT, hvD, hvE, hord⟩ :=
    interval_edge_classification_of_lt (L := L) huv hv
  obtain ⟨UL, hUL, hrUL⟩ :=
    exists_threeSplit_eq_kronecker_one_rank_le hTE huD (H.mem u)
  obtain ⟨VR, hVR, hrVR⟩ :=
    exists_threeSplit_eq_reindex_one_kronecker_rank_le hTE hvD (H.mem v)
  have hULrank : operatorSchmidtRank UL ≤ q ^ 2 := by
    simpa only [T, huT, Finset.card_singleton, Nat.mul_one] using hrUL
  have hVRrank : operatorSchmidtRank VR ≤ q ^ 2 := by
    simpa only [E, hvE, Finset.card_singleton, Nat.mul_one] using hrVR
  have hlocal : ∀ r : Fin (L - 1),
      ∃ (B : Matrix (T → Fin q) (T → Fin q) ℂ)
        (C : Matrix (E → Fin q) (E → Fin q) ℂ)
        (D : Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ),
        r ≠ u → r ≠ v →
          (H.term r).submatrix g.symm g.symm =
            (B ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
                (1 : Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ) +
              ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ C) ⊗ₖ
                (1 : Matrix ({x // x ∉ T ∪ E} → Fin q) ({x // x ∉ T ∪ E} → Fin q) ℂ) +
              (1 : Matrix ((T → Fin q) × (E → Fin q))
                ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ D := by
    intro r
    by_cases hru : r = u
    · exact ⟨0, 0, 0, by simp [hru]⟩
    · by_cases hrv : r = v
      · exact ⟨0, 0, 0, by simp [hrv]⟩
      · rcases hord r.val (by omega) (fun h => hru (Fin.ext h))
          (fun h => hrv (Fin.ext h)) with hrT | hrE | hrU
        · obtain ⟨B, hB⟩ := exists_threeSplit_eq_kronecker_one_kronecker_one hTE
            (Finset.coe_subset.mpr hrT) (H.mem r)
          refine ⟨B, 0, 0, ?_⟩
          intro _ _
          simpa using hB
        · obtain ⟨C, hC⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one hTE
            (Finset.coe_subset.mpr hrE) (H.mem r)
          refine ⟨0, C, 0, ?_⟩
          intro _ _
          simpa using hC
        · obtain ⟨D, hD⟩ := exists_threeSplit_eq_one_kronecker hTE
            (Finset.coe_subset.mpr hrU) (H.mem r)
          refine ⟨0, 0, D, ?_⟩
          intro _ _
          simpa using hD
  choose HL HM HR hlocal using hlocal
  exact ⟨HL, HM, HR, UL, VR, hlocal, hUL, hVR, hULrank, hVRrank⟩

end TNLean.MPS.AreaLaw
end

end

section

open ManyBody (disjoint_interval_interval interval interval_mono mem_interval)

open Matrix QuantumCircuit
open scoped Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Simultaneous regional forms for the two-window family of ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The three bulk operators
are independently supplied; no equality with complementary bond sums is required. -/
theorem exists_threeSplit_two_window_factors
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L)))
    (hL : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L 0 (a + 1) : Finset (Fin L)))
    (hM : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + 2 * ℓ) (b + 1) : Finset (Fin L)))
    (hR : F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + 2 * ℓ) L : Finset (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) :
    let T := interval L 0 ((a + p.val) + 1)
    let E := interval L ((a + p.val) + 1) ((b + s.val) + 1)
    let hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
    let g := threeSplit q T E hTE
    ∃ (HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (E → Fin q) (E → Fin q) ℂ)
      (HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
        Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ)
      (VR : Matrix ((E → Fin q) × ({v // v ∉ T ∪ E} → Fin q))
        ((E → Fin q) × ({v // v ∉ T ∪ E} → Fin q)) ℂ),
      (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
        (F r).submatrix g.symm g.symm =
          (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
      (F (Sum.inl (Sum.inl p))).submatrix g.symm g.symm =
        UL ⊗ₖ (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) ∧
      (F (Sum.inl (Sum.inr s))).submatrix g.symm g.symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            ({v // v ∉ T ∪ E} → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            ({v // v ∉ T ∪ E} → Fin q)).symm ∧
      operatorSchmidtRank UL ≤ q ^ 2 ∧ operatorSchmidtRank VR ≤ q ^ 2 := by
  classical
  intro T E hTE g
  have huv : a + p.val < b + s.val := by
    have := p.isLt
    omega
  have hv : b + s.val + 1 < L := by
    have := s.isLt
    omega
  obtain ⟨huD, huT, hvD, hvE, hord⟩ :=
    interval_edge_classification_of_lt (L := L) huv hv
  obtain ⟨UL, hUL, hrUL⟩ :=
    exists_threeSplit_eq_kronecker_one_rank_le hTE huD (hleft p)
  obtain ⟨VR, hVR, hrVR⟩ :=
    exists_threeSplit_eq_reindex_one_kronecker_rank_le hTE hvD (hright s)
  have hULrank : operatorSchmidtRank UL ≤ q ^ 2 := by
    simpa only [T, huT, Finset.card_singleton, Nat.mul_one] using hrUL
  have hVRrank : operatorSchmidtRank VR ≤ q ^ 2 := by
    simpa only [E, hvE, Finset.card_singleton, Nat.mul_one] using hrVR
  have hregional : ∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
      F r ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) T ∨
        F r ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) E ∨
        F r ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ((T ∪ E)ᶜ : Finset (Fin L)) := by
    intro r hru hrv
    have hp := p.isLt
    have hs := s.isLt
    have hmono (t : ℕ) (ht : t + 1 < L)
        (htu : t ≠ a + p.val) (htv : t ≠ b + s.val)
        {A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
        (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (interval L t (t + 2) : Finset (Fin L))) :
        A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) T ∨
          A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) E ∨
          A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ((T ∪ E)ᶜ : Finset (Fin L)) := by
      rcases hord t ht htu htv with hT | hE | hU
      · exact Or.inl (ManyBody.supportedOperators_mono (Finset.coe_subset.mpr hT) hA)
      · exact Or.inr (Or.inl (ManyBody.supportedOperators_mono (Finset.coe_subset.mpr hE) hA))
      · exact Or.inr (Or.inr (ManyBody.supportedOperators_mono (Finset.coe_subset.mpr hU) hA))
    rcases r with (t | t) | j
    · have ht := t.isLt
      refine hmono (a + t.val) (by omega) ?_ (by omega) (hleft t)
      intro h
      apply hru
      exact congrArg (fun z : Fin (2 * ℓ) ↦
        (Sum.inl (Sum.inl z) : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))
        (Fin.ext (Nat.add_left_cancel h))
    · have ht := t.isLt
      refine hmono (b + t.val) (by omega) (by omega) ?_ (hright t)
      intro h
      apply hrv
      exact congrArg (fun z : Fin (2 * ℓ) ↦
        (Sum.inl (Sum.inr z) : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))
        (Fin.ext (Nat.add_left_cancel h))
    · fin_cases j
      · left
        exact ManyBody.supportedOperators_mono
          (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) hL
      · right
        left
        exact ManyBody.supportedOperators_mono
          (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) hM
      · right
        right
        apply ManyBody.supportedOperators_mono ?_ hR
        intro x hx
        have hx' := (mem_interval.mp hx).1
        change x ∈ (T ∪ E)ᶜ
        simp only [Finset.mem_compl, Finset.mem_union, T, E, mem_interval]
        omega
  have hlocal : ∀ r : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3),
      ∃ (B : Matrix (T → Fin q) (T → Fin q) ℂ)
        (C : Matrix (E → Fin q) (E → Fin q) ℂ)
        (D : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ),
        r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
          (F r).submatrix g.symm g.symm =
            (B ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
                (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
              ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ C) ⊗ₖ
                (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
              (1 : Matrix ((T → Fin q) × (E → Fin q))
                ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ D := by
    intro r
    by_cases hru : r = Sum.inl (Sum.inl p)
    · exact ⟨0, 0, 0, by simp [hru]⟩
    · by_cases hrv : r = Sum.inl (Sum.inr s)
      · exact ⟨0, 0, 0, by simp [hrv]⟩
      · rcases hregional r hru hrv with hrT | hrE | hrU
        · obtain ⟨B, hB⟩ := exists_threeSplit_eq_kronecker_one_kronecker_one hTE
            (Set.Subset.rfl) hrT
          refine ⟨B, 0, 0, ?_⟩
          intro _ _
          simpa using hB
        · obtain ⟨C, hC⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one hTE
            (Set.Subset.rfl) hrE
          refine ⟨0, C, 0, ?_⟩
          intro _ _
          simpa using hC
        · obtain ⟨D, hD⟩ := exists_threeSplit_eq_one_kronecker hTE
            (Set.Subset.rfl) hrU
          refine ⟨0, 0, D, ?_⟩
          intro _ _
          simpa using hD
  choose HL HM HR hlocal using hlocal
  exact ⟨HL, HM, HR, UL, VR, hlocal, hUL, hVR, hULrank, hVRrank⟩

end TNLean.MPS.AreaLaw
end

end
