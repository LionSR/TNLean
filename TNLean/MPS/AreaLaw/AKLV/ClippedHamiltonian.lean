/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.Normalization
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteHierarchy

/-!
# The norm and spatial decomposition of the actual AKLV truncation

Only the two enlarged exterior sums are clipped. The remaining `s-2` original
interactions form a shorter window with the same central cut. Subtracting the
three regional energies gives a positive operator of norm at most `2*t+s`.
The decomposition used for the rank estimate is obtained from these actual
operators; neither a spectral ceiling nor a spatial decomposition is supplied.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, equation (5) and the subsequent
definition of the two exterior truncations; Section 4, Lemma 4.2.

**Scope restriction (window width):** The window contains at least six
interactions. The support convention and the aggregate middle energy shift
are those recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem two_block_outer_selector :
    (Finset.univ : Finset (Fin 2)).image
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) = {0, 2} := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

open Classical in
private theorem aklv_clipped_hamiltonian_formula {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (e : Fin 3 → ℝ) (t : ℝ) :
    let C := aklvRegionalHamiltonians (a + 2) (a + s - 1) h
    let F := fun j : Fin 3 ↦ cfc (fun x : ℝ ↦ min x (e j + t)) (C j)
    let H := fun j : Fin (s - 2) ↦ h ⟨a + 1 + j.val, by omega⟩
    aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ =
      (F 0 - (((∑ j, e j) : ℝ) : ℂ) • 1) + (∑ j, H j) + F 2 := by
  intro C F H
  have hmiddle : (∑ j, H j) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + 1 ≤ i.val ∧ i.val < a + s - 1), h i := by
    refine Finset.sum_bij (fun j _ ↦ (⟨a + 1 + j.val, by omega⟩ : Fin (L - 1)))
      ?_ ?_ ?_ ?_
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro i _ j _ hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      change a + 1 + i.val = a + 1 + j.val at hval
      omega
    · intro j hj
      have hp := (Finset.mem_filter.mp hj).2
      refine ⟨⟨j.val - (a + 1), by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      change a + 1 + (j.val - (a + 1)) = j.val
      omega
    · intro j _
      rfl
  have hretained : C 1 +
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        i.val + 1 ∈ ({a + 2, a + s - 1} : Finset ℕ)), h i) = ∑ j, H j := by
    rw [hmiddle]
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + 2 ≤ i.val ∧ i.val + 1 < a + s - 1), h i) + _ = _
    simp only [Finset.sum_filter, Finset.mem_insert, Finset.mem_singleton,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all <;> omega
  change (∑ j, ((if j ∈ (Finset.univ : Finset (Fin 2)).image
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) then F j else C j) -
      (e j : ℂ) • 1)) + _ = _
  rw [two_block_outer_selector, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) by decide,
    show (1 : Fin 3) ∉ ({0, 2} : Finset (Fin 3)) by decide,
    show (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) by decide, ite_true, ite_false]
  rw [show (∑ j, H j) = C 1 +
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        i.val + 1 ∈ ({a + 2, a + s - 1} : Finset ℕ)), h i) from hretained.symm,
    Fin.sum_univ_three]
  push_cast
  rw [add_smul, add_smul]
  abel


open Classical in
/-- The actual two clipped exteriors and the retained original bonds give a
shorter window of width `s-2`. Its central cut is the original central cut.
AKLV, arXiv:1301.1162v1, Section 6.1, equation (5), and Lemma 4.2. -/
theorem aklv_clipped_hamiltonian_decomposition {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (e : Fin 3 → ℝ) (t : ℝ) :
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
    let H := fun j : Fin (s - 2) ↦ h ⟨a + 1 + j.val, by omega⟩
    ∃ HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      Entropy.IsSupportedOn HL (interval L 0 (a + 2)) ∧
      Entropy.IsSupportedOn HR (interval L (a + s - 1) L) ∧
      (∀ j, Entropy.IsSupportedOn (H j)
        (interval L (a + 1 + j.val) (a + 1 + j.val + 2))) ∧
      B = HL + (∑ j, H j) + HR ∧
      a + 1 + (s - 2) / 2 = a + s / 2 := by
  intro B H
  let C := aklvRegionalHamiltonians (a + 2) (a + s - 1) h
  let F (j : Fin 3) := cfc (fun x : ℝ ↦ min x (e j + t)) (C j)
  let HL := F 0 - (((∑ j, e j) : ℝ) : ℂ) • 1
  let HR := F 2
  have hC (j : Fin 3) : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (C j)
      (interval L ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.castSucc)
        ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.succ)) :=
    isSupportedOn_sum_internal_bonds L q _ _ h hsupp
  have hF (j : Fin 3) : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (F j)
      (interval L ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.castSucc)
        ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.succ)) := by
    exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators
      (LocalSolution.cfc_mem_supportedOperators _
        (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hC j)))
  have hleft : Entropy.IsSupportedOn HL (interval L 0 (a + 2)) := by
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    exact Submodule.sub_mem _
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hF 0))
      (Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _))
  refine ⟨HL, HR, hleft, hF 2, fun j ↦ hsupp _, ?_, by omega⟩
  exact aklv_clipped_hamiltonian_formula hs ha h e t

open Classical in
/-- The actual clipped Hamiltonian is positive and has norm at most `2*t+s`.
The energies are the regional lower bounds used in the source normalization;
only the nonnegativity of the middle minimum is needed for the upper bound.
AKLV, arXiv:1301.1162v1, Section 6.1, the definition of `H^(t)`. -/
theorem aklv_clipped_hamiltonian_posSemidef_norm_le {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e : Fin 3 → ℝ)
    (he : ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef)
    (he1 : 0 ≤ e 1) {t : ℝ} (ht : 0 ≤ t) :
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
    B.PosSemidef ∧ ‖B‖ ≤ 2 * t + s := by
  intro B
  let C := aklvRegionalHamiltonians (a + 2) (a + s - 1) h
  let F (j : Fin 3) := cfc (fun x : ℝ ↦ min x (e j + t)) (C j)
  let H := fun j : Fin (s - 2) ↦ h ⟨a + 1 + j.val, by omega⟩
  let J := Finset.univ.filter (fun i : Fin (L - 1) ↦
    i.val + 1 ∈ ({a + 2, a + s - 1} : Finset ℕ))
  have hC (j : Fin 3) : (C j).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)
  have heC := aklv_normalization_le_two_block_regions hs h h0 e he
  have hcenter := (Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
    C e t ({0, 2} : Finset (Fin 3)) (fun j ↦ (hC j).isHermitian) heC
    0 (fun j ↦ by simp) ht).1
  have hB0 : B.PosSemidef := by
    change ((∑ j, ((if j ∈ (Finset.univ : Finset (Fin 2)).image
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) then F j else C j) -
      (e j : ℂ) • 1)) + ∑ i ∈ J, h i).PosSemidef
    rw [two_block_outer_selector]
    exact hcenter.add (Matrix.nonneg_iff_posSemidef.mp
      (Finset.sum_nonneg fun i _ ↦ h0 i))
  have hFcap (j : Fin 3) : F j ≤ (e j + t) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    simpa only [Matrix.energyTruncation, Complex.coe_smul] using
      (hC j).isHermitian.energyTruncation_le_smul_one (e j + t)
  have hHcap : (∑ j, H j) ≤ ((s - 2 : ℕ) : ℝ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms Finset.univ H
        (fun j _ ↦ h0 ⟨a + 1 + j.val, by omega⟩)
        (fun j _ ↦ h1 ⟨a + 1 + j.val, by omega⟩)).2
  have hBcap : B ≤ (2 * t + s) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    dsimp only [B]
    rw [aklv_clipped_hamiltonian_formula hs ha h e t]
    calc
      _ ≤ ((e 0 + t) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) -
          (((∑ j, e j) : ℝ) : ℂ) • 1) +
          ((s - 2 : ℕ) : ℝ) • 1 + (e 2 + t) • 1 :=
        add_le_add (add_le_add (sub_le_sub_right (hFcap 0) _) hHcap) (hFcap 2)
      _ = (2 * t + ((s - 2 : ℕ) : ℝ) - e 1) • 1 := by
        rw [Fin.sum_univ_three, Complex.coe_smul]
        module
      _ ≤ (2 * t + s) • 1 := by
        apply smul_le_smul_of_nonneg_right _ zero_le_one
        have hcast : ((s - 2 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 2
        linarith
  exact ⟨hB0, (CStarAlgebra.norm_le_iff_le_algebraMap B (by positivity) hB0.nonneg).mpr
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hBcap)⟩

end TNLean.MPS.AreaLaw
