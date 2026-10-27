/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.RegionalOperatorForms
import TNLean.Lattice.Sheet.SupportedSchmidtRank
import TNLean.Lattice.Sheet.LeftSupportedSchmidtRank
import TNLean.MPS.AreaLaw.TwoCutEdgeSupports

/-!
# Bond operators at two cuts

A family of operators supported on the bonds of a finite chain admits one
collection of three regional families and two crossing factors. Every
ordinary bond operator is the sum of its three regional terms. The same
crossing factors satisfy the tensor identities and the rank bound q².
All choices depend only on the operator family and the cuts.

This statement concerns the literal bond family, with one label for each
edge. The grouped window operators, their coefficient counts, cut movement
and matrix product operator construction are separate assertions.

## References

Supporting locality algebra for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines 1324–1332.
-/

open Matrix QuantumCircuit
open scoped Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Actual two crossing factors and three regional families of an original
nearest-neighbour bond family, all in one three-region partition.
Supporting locality algebra for ALVV, arXiv:1602.08828v2, eq:H-mid-cut,
lines 810–821, and prop:Cheby-AGSP-eff, lines 1324–1332. -/
theorem exists_threeSplit_edge_factors
    {L q : ℕ}
    (H : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ r, H r ∈ supportedOperators q
      (interval L r.val (r.val + 2) : Set (Fin L)))
    (u v : Fin (L - 1)) (huv : u.val < v.val)
    {T E : Finset (Fin L)} (hT : T = interval L 0 (u.val + 1))
    (hE : E = interval L (u.val + 1) (v.val + 1)) (hTE : Disjoint T E) :
    ∃ (HL : Fin (L - 1) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (HM : Fin (L - 1) → Matrix (E → Fin q) (E → Fin q) ℂ)
      (HR : Fin (L - 1) → Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ)
      (VR : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ),
      (∀ r, r ≠ u → r ≠ v →
        (H r).submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
          (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
      (H u).submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
        UL ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) ∧
      (H v).submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm ∧
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
    exists_threeSplit_eq_kronecker_one_rank_le hTE huD (hsupp u)
  obtain ⟨VR, hVR, hrVR⟩ :=
    exists_threeSplit_eq_reindex_one_kronecker_rank_le hTE hvD (hsupp v)
  have hULrank : operatorSchmidtRank UL ≤ q ^ 2 := by
    simpa only [T, huT, Finset.card_singleton, Nat.mul_one] using hrUL
  have hVRrank : operatorSchmidtRank VR ≤ q ^ 2 := by
    simpa only [E, hvE, Finset.card_singleton, Nat.mul_one] using hrVR
  have hlocal : ∀ r : Fin (L - 1),
      ∃ (B : Matrix (T → Fin q) (T → Fin q) ℂ)
        (C : Matrix (E → Fin q) (E → Fin q) ℂ)
        (D : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ),
        r ≠ u → r ≠ v →
          (H r).submatrix g.symm g.symm =
            (B ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
                (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
              ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ C) ⊗ₖ
                (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
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
            (Finset.coe_subset.mpr hrT) (hsupp r)
          refine ⟨B, 0, 0, ?_⟩
          intro _ _
          simpa using hB
        · obtain ⟨C, hC⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one hTE
            (Finset.coe_subset.mpr hrE) (hsupp r)
          refine ⟨0, C, 0, ?_⟩
          intro _ _
          simpa using hC
        · obtain ⟨D, hD⟩ := exists_threeSplit_eq_one_kronecker hTE
            (Finset.coe_subset.mpr hrU) (hsupp r)
          refine ⟨0, 0, D, ?_⟩
          intro _ _
          simpa using hD
  choose HL HM HR hlocal using hlocal
  exact ⟨HL, HM, HR, UL, VR, hlocal, hUL, hVR, hULrank, hVRrank⟩

end TNLean.MPS.AreaLaw
