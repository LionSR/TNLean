/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoCutOperatorForms

/-!
# Two windows with independently supported bulk operators

The two windows retain their individual nearest-neighbour terms and the three
bulk operators retain their given supports. The same two crossing factors
satisfy both tensor identities and the bound q². In particular, when the
windows touch, the middle bulk support is a singleton.

## References

ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1332.
-/

open Matrix QuantumCircuit
open scoped Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Simultaneous regional forms for the two-window family of ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The three bulk operators
are independently supplied; no equality with complementary bond sums is required. -/
theorem exists_threeSplit_twoWindow_factors
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) :
    let T := interval L 0 ((a + p.val) + 1)
    let E := interval L ((a + p.val) + 1) ((b + s.val) + 1)
    let hTE : Disjoint T E := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [T, E, mem_interval] at hx hx'
      omega
    let g := threeSplit q T E hTE
    ∃ (HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (E → Fin q) (E → Fin q) ℂ)
      (HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
        Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ)
      (VR : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ),
      (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
        (F r).submatrix g.symm g.symm =
          (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
      (F (Sum.inl (Sum.inl p))).submatrix g.symm g.symm =
        UL ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) ∧
      (F (Sum.inl (Sum.inr s))).submatrix g.symm g.symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm ∧
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
      F r ∈ supportedOperators q (T : Set (Fin L)) ∨
        F r ∈ supportedOperators q (E : Set (Fin L)) ∨
        F r ∈ supportedOperators q ((T ∪ E)ᶜ : Finset (Fin L)) := by
    intro r hru hrv
    have hp := p.isLt
    have hs := s.isLt
    have hmono (t : ℕ) (ht : t + 1 < L)
        (htu : t ≠ a + p.val) (htv : t ≠ b + s.val)
        {A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
        (hA : A ∈ supportedOperators q
          (interval L t (t + 2) : Set (Fin L))) :
        A ∈ supportedOperators q (T : Set (Fin L)) ∨
          A ∈ supportedOperators q (E : Set (Fin L)) ∨
          A ∈ supportedOperators q ((T ∪ E)ᶜ : Finset (Fin L)) := by
      rcases hord t ht htu htv with hT | hE | hU
      · exact Or.inl (supportedOperators_mono (Finset.coe_subset.mpr hT) hA)
      · exact Or.inr (Or.inl (supportedOperators_mono (Finset.coe_subset.mpr hE) hA))
      · exact Or.inr (Or.inr (supportedOperators_mono (Finset.coe_subset.mpr hU) hA))
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
        exact supportedOperators_mono
          (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) hL
      · right
        left
        exact supportedOperators_mono
          (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) hM
      · right
        right
        apply supportedOperators_mono ?_ hR
        intro x hx
        have hx' := (mem_interval.mp hx).1
        change x ∈ (T ∪ E)ᶜ
        simp only [Finset.mem_compl, Finset.mem_union, T, E, mem_interval]
        omega
  have hlocal : ∀ r : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3),
      ∃ (B : Matrix (T → Fin q) (T → Fin q) ℂ)
        (C : Matrix (E → Fin q) (E → Fin q) ℂ)
        (D : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ),
        r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
          (F r).submatrix g.symm g.symm =
            (B ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
                (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
              ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ C) ⊗ₖ
                (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
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
