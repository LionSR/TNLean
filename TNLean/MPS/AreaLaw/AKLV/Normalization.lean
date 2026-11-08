/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.DisjointRegionalGround
import TNLean.MPS.AreaLaw.AKLV.TwoBlockTruncation

/-!
# The three energy normalizations in the AKLV geometry

The three reference sums are the original left exterior, the middle bulk after
removing its three boundary bonds on each side, and the original right exterior.
Their supports are pairwise disjoint. Their actual lowest energies and a common
unit ground vector are constructed, giving ground energy at most six for the
centered full Hamiltonian.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, the normalization before equation (5).
The two operators subsequently clipped are the enlarged exterior sums containing
one further boundary bond, not the reference sums used to choose the minima.

**Local fix (middle energy shift):** The source range `4,...,s-3` contains `s-6`
terms, whereas its printed individual subtraction uses `s-7`. This module subtracts
the actual middle lowest energy once from the aggregate sum. A redistribution among
its individual terms would use `s-6`. The correction and remaining robustness
argument are recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Endpoints of the three disjoint regions used to choose the original energies.
AKLV, arXiv:1301.1162v1, Section 6.1, the normalization before equation (5).
The middle interaction labels are `4,...,s-3` in the source's one-based convention. -/
def aklvNormalizationEndpoints (L a s : ℕ) : Fin 3 → ℕ × ℕ :=
  ![(0, a + 1), (a + 3, a + s - 2), (a + s, L)]

/-- The three actual original reference Hamiltonians whose lowest energies are
subtracted in AKLV, arXiv:1301.1162v1, Section 6.1, before equation (5). -/
def aklvNormalizationHamiltonians {L q : ℕ} (a s : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Fin 3 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  let p := aklvNormalizationEndpoints L a s
  fun j ↦ ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ (p j).1 ≤ i.val ∧ i.val + 1 < (p j).2), h i

private theorem aklv_normalization_bond_data {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) :
    let p := aklvNormalizationEndpoints L a s
    let R := fun j ↦ interval L (p j).1 (p j).2
    let A := aklvNormalizationHamiltonians a s h
    let J := Finset.univ.filter (fun i : Fin (L - 1) ↦
      i.val ∈ ({a, a + 1, a + 2, a + s - 3, a + s - 2, a + s - 1} : Finset ℕ))
    Pairwise (fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A j) (R j)) ∧
      J.card ≤ 6 ∧ (∑ i, h i) = (∑ j, A j) + ∑ i ∈ J, h i := by
  intro p R A J
  have hR : Pairwise fun i j ↦ Disjoint (R i) (R j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    change v ∈ interval L (p i).1 (p i).2 at hvi
    change v ∈ interval L (p j).1 (p j).2 at hvj
    rw [mem_interval] at hvi hvj
    fin_cases i <;> fin_cases j <;> simp_all [p, aklvNormalizationEndpoints] <;> omega
  have hA (j : Fin 3) :
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A j) (R j) := by
    exact isSupportedOn_sum_internal_bonds L q (p j).1 (p j).2 h hsupp
  have hJ : J.card ≤ 6 := by
    have hc := Finset.card_le_card_of_injOn Fin.val
      (s := J) (t := {a, a + 1, a + 2, a + s - 3, a + s - 2, a + s - 1})
      (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
      (by intro i _ j _ hij; exact Fin.ext hij)
    exact hc.trans Finset.card_le_six
  refine ⟨hR, hA, hJ, ?_⟩
  rw [Fin.sum_univ_three]
  change (∑ i, h i) =
    (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      0 ≤ i.val ∧ i.val + 1 < a + 1), h i) +
    (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      a + 3 ≤ i.val ∧ i.val + 1 < a + s - 2), h i) +
    (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      a + s ≤ i.val ∧ i.val + 1 < L), h i) +
    ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      i.val ∈ ({a, a + 1, a + 2, a + s - 3, a + s - 2, a + s - 1} : Finset ℕ)), h i
  simp only [Finset.sum_filter, Finset.mem_insert, Finset.mem_singleton,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  split_ifs <;> simp_all <;> omega

open Classical in
/-- The original three disjoint bulk minima and a normalized ground vector of the
centered full Hamiltonian are constructed from the physical interactions. The
relative ground energy lies in `[0,6]`, as in AKLV, arXiv:1301.1162v1, Section 6.1,
before equation (5). No regional minimum, common vector, or energy budget is supplied. -/
theorem exists_aklv_energy_normalization {L q a s : ℕ} (hq : 0 < q)
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let A := aklvNormalizationHamiltonians a s h
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E0 : ℝ),
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star x ⬝ᵥ x = 1 ∧
      (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      (∀ j, 0 ≤ e j) ∧
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E0 : ℂ) • z ∧
      (H - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 6 := by
  intro A
  let p := aklvNormalizationEndpoints L a s
  let R := fun j ↦ interval L (p j).1 (p j).2
  let I := fun j ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ (p j).1 ≤ i.val ∧ i.val + 1 < (p j).2)
  let J := Finset.univ.filter (fun i : Fin (L - 1) ↦
    i.val ∈ ({a, a + 1, a + 2, a + s - 3, a + s - 2, a + s - 1} : Finset ℕ))
  let Y := ∑ i ∈ J, h i
  obtain ⟨hR, hAs, hJ, hH⟩ := aklv_normalization_bond_data hs ha h hsupp
  have hA (j : Fin 3) : (A j).PosSemidef ∧
      A j ≤ ((I j).card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms (I j) h
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  have hY : Y.PosSemidef ∧
      Y ≤ (J.card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms J h
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  obtain ⟨e, x, hxunit, hx, he, hclip⟩ :=
    Matrix.exists_disjoint_regional_clipping_structure hq R A
      (fun j ↦ (I j).card) hR hAs (fun j ↦ (hA j).1)
      (fun j ↦ (hA j).2) Y J.card hY.1 hY.2
  obtain ⟨_, _, _, _, _, _, E0, z, hzunit, hz, hElow, hE0, hE6⟩ :=
    hclip 0 le_rfl ∅
  have hcenter :
      (∑ j, (A j - (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))) + Y =
        (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 := by
    rw [hH, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_smul]
    abel
  refine ⟨e, x, z, E0, hxunit, hx, he, ?_, hzunit, ?_, ?_, hE0,
    hE6.trans (by exact_mod_cast hJ)⟩
  · exact fun j ↦ (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hx j) hxunit
  · simpa only [Finset.notMem_empty, ite_false, hcenter] using hz
  · simpa only [Finset.notMem_empty, ite_false, hcenter] using hElow

/-- The two actual enlarged exterior sums are exactly the original exterior
reference sums plus their adjacent boundary bonds. Their centered supports are
`[0,a+2)` and `[a+s-1,L)`. AKLV, arXiv:1301.1162v1, Section 6.1, the definition
of `H^(t)` after equation (5). -/
theorem aklv_two_block_exterior_data {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) :
    let A := aklvNormalizationHamiltonians a s h
    let C := aklvRegionalHamiltonians (a + 2) (a + s - 1) h
    C 0 = A 0 + h ⟨a, by omega⟩ ∧
      C 2 = h ⟨a + s - 1, by omega⟩ + A 2 ∧
      ∀ eL eR : ℝ,
        Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (C 0 - (eL : ℂ) • 1) (interval L 0 (a + 2)) ∧
        Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (C 2 - (eR : ℂ) • 1) (interval L (a + s - 1) L) := by
  intro A C
  let il : Fin (L - 1) := ⟨a, by omega⟩
  let ir : Fin (L - 1) := ⟨a + s - 1, by omega⟩
  have hlset : Finset.univ.filter (fun i : Fin (L - 1) ↦
      0 ≤ i.val ∧ i.val + 1 < a + 2) =
      insert il (Finset.univ.filter (fun i : Fin (L - 1) ↦
        0 ≤ i.val ∧ i.val + 1 < a + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    dsimp only [il]
    omega
  have hrset : Finset.univ.filter (fun i : Fin (L - 1) ↦
      a + s - 1 ≤ i.val ∧ i.val + 1 < L) =
      insert ir (Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + s ≤ i.val ∧ i.val + 1 < L)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    dsimp only [ir]
    omega
  have hl : C 0 = A 0 + h il := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      0 ≤ i.val ∧ i.val + 1 < a + 2), h i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        0 ≤ i.val ∧ i.val + 1 < a + 1), h i) + h il
    rw [hlset, Finset.sum_insert (by simp [il])]
    exact add_comm _ _
  have hr : C 2 = h ir + A 2 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      a + s - 1 ≤ i.val ∧ i.val + 1 < L), h i) = h ir +
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + s ≤ i.val ∧ i.val + 1 < L), h i)
    rw [hrset, Finset.sum_insert (by simp [ir]; omega)]
  have hsupport (j : Fin 3) : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (C j) (interval L ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.castSucc)
        ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.succ)) := by
    exact isSupportedOn_sum_internal_bonds L q _ _ h hsupp
  have hcenter (j : Fin 3) (e : ℝ) :
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (C j - (e : ℂ) • 1)
        (interval L ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.castSucc)
          ((![0, a + 2, a + s - 1, L] : Fin 4 → ℕ) j.succ)) := by
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    exact Submodule.sub_mem _
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hsupport j))
      (Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _))
  exact ⟨hl, hr, fun eL eR ↦ ⟨hcenter 0 eL, hcenter 2 eR⟩⟩

/-- Lower bounds for the three reference sums remain lower bounds for the enlarged
regions, by positivity of the added bonds. AKLV, arXiv:1301.1162v1, Section 6.1,
normalization at lines 901–925 and the two exterior truncations after equation (5). -/
theorem aklv_normalization_le_two_block_regions {L q a s : ℕ}
    (hs : 6 ≤ s)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (e : Fin 3 → ℝ)
    (he : ∀ j, (aklvNormalizationHamiltonians a s h j -
      (e j : ℂ) • 1).PosSemidef) :
    ∀ j, (e j : ℂ) • 1 ≤ aklvRegionalHamiltonians (a + 2) (a + s - 1) h j := by
  intro j
  apply (Matrix.le_iff.mpr (he j)).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    fin_cases j <;> simp_all [aklvNormalizationEndpoints] <;> omega
  · intro i _ _
    exact h0 i

open Classical in
/-- The actual source normalization gives a common cutoff for every partial
outer clipping and an exponential two-block residual relative to the original
ground energy. The minima and original ground vector are derived from the raw
nearest-neighbour interactions. AKLV, arXiv:1301.1162v1, Section 6.1, normalization
and the two exterior truncations after equation (5). No spectral-gap conclusion
is asserted here. -/
theorem exists_aklv_normalized_two_block_residual {L q a s : ℕ} (hq : 0 < q)
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let A := aklvNormalizationHamiltonians a s h
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E0 : ℝ),
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star x ⬝ᵥ x = 1 ∧
      (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      (∀ j, 0 ≤ e j) ∧
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E0 : ℂ) • z ∧
      (H - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ η t : ℝ, 0 ≤ η → η + 11 ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t
        ∃ hB : ∀ T, (B T).IsHermitian,
          B ∅ = H ∧ ∀ T : Finset (Fin 2),
            let G := Submodule.spectralSpanLE
              (hB T).eigenvectorBasis (hB T).eigenvalues (E0 + η)
            ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
              (H - B Finset.univ)).domRestrict G)‖ ≤
                (64 * Real.exp (3 / 4)) * Real.exp (-(t - η) / 8) := by
  intro A
  obtain ⟨e, x, z, E0, hx, hxe, he, he0, hz, hzE, hE, hE0, hE6⟩ :=
    exists_aklv_energy_normalization hq hs ha h hsupp h0 h1
  refine ⟨e, x, z, E0, hx, hxe, he, he0, hz, hzE, hE, hE0, hE6, ?_⟩
  intro η t hη ht B
  have hhe := aklv_normalization_le_two_block_regions hs h h0 e he
  obtain ⟨hB, hcenter, hres⟩ := norm_aklv_two_block_truncation_low_le
    (by omega : a + 2 ≤ a + s - 1) (by omega : a + s - 1 ≤ L)
    h hsupp h0 h1 e (E0 + η) t (by linarith) (by linarith) hhe
  refine ⟨hB, hcenter, ?_⟩
  intro T G
  have hresT := hres T
  rw [hcenter] at hresT
  refine hresT.trans ?_
  calc
    64 * Real.exp (-(t - (E0 + η)) / 8) ≤
        64 * Real.exp (3 / 4 + (-(t - η) / 8)) := by
      gcongr
      linarith
    _ = (64 * Real.exp (3 / 4)) * Real.exp (-(t - η) / 8) := by
      rw [Real.exp_add]
      ring

end TNLean.MPS.AreaLaw
