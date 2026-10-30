/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.OneMarkerRank

/-!
# The physical window family in the AKLV frequency argument

The labels are the actual middle interactions and the two exterior operators. At a
chosen middle edge every other term lies on one side of the cut. The weighted-frequency
rank bound is derived from these supports, with the exact residual-frequency count.

**Local fix (count):** The corrected commuting-gap binomial coefficient is recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--662. The left
exterior may include the first window site; this weakens the support hypothesis and
includes the printed support convention. No positivity, Hermiticity or gap is needed
for this algebraic rank estimate. The low-frequency partition and central-cut assembly
are separate results.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- The actual finite alphabet of middle and exterior interactions in AKLV,
arXiv:1301.1162v1, Lemma 4.2, lines 604--617. -/
def aklvWindowFamily {L q s : ℕ}
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Fin s ⊕ Fin 2 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  Sum.elim H ![HL, HR]

/-- The alphabet sum is exactly the middle interaction plus its two exterior operators.
AKLV, arXiv:1301.1162v1, the Hamiltonian preceding Lemma 4.2, lines 530--540. -/
theorem sum_aklvWindowFamily {L q s : ℕ}
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ j, aklvWindowFamily H HL HR j) = HL + (∑ j, H j) + HR := by
  simp only [aklvWindowFamily, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

open Classical in
/-- An arbitrary weighted sum on one actual frequency slice has the corrected rank bound
at its distinguished physical cut. The cardinality factor is computed from the window
alphabet, not supplied. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--662. -/
theorem operatorSchmidtRank_aklv_window_one_marker_le {L q a s : ℕ}
    (hq : 1 ≤ q) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L)) (u : Fin s) (t k : ℕ) :
    let I := {j : Fin s ⊕ Fin 2 // j ≠ Sum.inl u}
    let E := @Finset.piAntidiag I ℕ (Classical.decEq I) _ _ _ Finset.univ t
    let ordinary := fun j : I ↦ aklvWindowFamily H HL HR j.val
    ∀ weight : E → ℂ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (a + u.val + 1))
        (∑ α : E, weight α •
          WordMultiplicity.oneMarkerCoefficient ordinary (H u) t k α.val)) ≤
      (t + s).choose s * ((t + 2 * k + 1).choose (2 * k + 1) * q ^ (2 * k)) := by
  intro I E ordinary weight
  let : DecidableEq I := Classical.decEq I
  let X : Fin s ⊕ Fin 2 → Finset (Fin L) :=
    Sum.elim (fun j ↦ interval L (a + j.val) (a + j.val + 2))
      ![interval L 0 (a + 1), interval L (a + s) L]
  have hAll (j : Fin s ⊕ Fin 2) : Entropy.IsSupportedOn (aklvWindowFamily H HL HR j) (X j) := by
    cases j with
    | inl j => exact hH j
    | inr j => fin_cases j <;> assumption
  have hside (j : I) : X j.val ⊆ leftBlock L (a + u.val + 1) ∨
      Disjoint (X j.val) (leftBlock L (a + u.val + 1)) := by
    obtain ⟨j, hne⟩ := j
    cases j with
    | inl j =>
      have hju : j ≠ u := fun h ↦ hne (congrArg Sum.inl h)
      rcases lt_or_gt_of_ne hju with hlt | hgt
      · left
        intro v hv
        change v ∈ interval L (a + j.val) (a + j.val + 2) at hv
        rw [mem_interval] at hv
        rw [mem_leftBlock]
        have hj := Fin.lt_def.mp hlt
        omega
      · right
        apply Finset.disjoint_left.mpr
        intro v hv hcut
        change v ∈ interval L (a + j.val) (a + j.val + 2) at hv
        rw [mem_interval] at hv
        rw [mem_leftBlock] at hcut
        have hj := Fin.lt_def.mp hgt
        omega
    | inr j =>
      fin_cases j
      · left
        intro v hv
        change v ∈ interval L 0 (a + 1) at hv
        rw [mem_interval] at hv
        rw [mem_leftBlock]
        omega
      · right
        apply Finset.disjoint_left.mpr
        intro v hv hcut
        change v ∈ interval L (a + s) L at hv
        rw [mem_interval] at hv
        rw [mem_leftBlock] at hcut
        omega
  have hT : Entropy.IsSupportedOn (H u)
      (interval L ((a + u.val + 1) - 1) ((a + u.val + 1) + 1)) := by
    have hlo : a + u.val + 1 - 1 = a + u.val := by omega
    have hhi : a + u.val + 1 + 1 = a + u.val + 2 := by omega
    simpa only [hlo, hhi] using hH u
  have hIcard : Fintype.card I = s + 1 := by
    change Fintype.card {j : Fin s ⊕ Fin 2 // ¬j = Sum.inl u} = s + 1
    rw [Fintype.card_subtype_compl]
    simp
  have hEcard : E.card = (t + s).choose s := by
    dsimp only [E]
    rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
      Finset.card_univ, Sym.card_sym_eq_choose, hIcard]
    have heq : s + 1 + t - 1 = t + s := by omega
    simpa only [heq] using (Nat.choose_symm_add (a := t) (b := s))
  have hrank := operatorSchmidtRank_one_marker_of_chain_supports_le
    (cut := a + u.val + 1) hq (by omega) (by omega) ordinary
    (fun j : I ↦ X j.val) (fun j ↦ hAll j.val) hside (H u) hT t k weight
  change _ ≤ E.card * ((t + 2 * k + 1).choose (2 * k + 1) * q ^ (2 * k)) at hrank
  rw [hEcard] at hrank
  exact hrank

end TNLean.MPS.AreaLaw
