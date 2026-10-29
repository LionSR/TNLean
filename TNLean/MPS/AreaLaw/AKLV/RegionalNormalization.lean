/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedNormalizedGroundSpace
import TNLean.MPS.AreaLaw.AKLV.NormalizedChain
import QICLean.Analysis.GroundEnergyBounds
import Mathlib.Order.Interval.Finset.Nat

/-!
# The three regional minima in AKLV normalization

The original positive unit bonds determine three separated cores. Subtracting
exactly their minimum eigenvalues makes the cores positive and leaves six
positive unit boundary bonds. The core ground cutoffs give an actual common
zero vector; neither regional positivity nor a common vector is an input.

**Local fix:** The middle core is shifted by its total minimum, equivalently
by that minimum divided by the number of middle-core bonds on each bond.
The printed denominator has one bond too few; see
`docs/paper-gaps/aklv13_robustness_constants.tex`.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, normalization preceding
Theorem 6.1.
-/

open Matrix QuantumCircuit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- The bonds strictly inside the three regional cores. The six bonds
adjacent to the two cuts are left unchanged. AKLV, Section 6.1. -/
def normalizationCoreBonds {L : ℕ} (a b : Fin (L - 1)) : Fin 3 → Finset (Fin (L - 1))
  | 0 => Finset.univ.filter fun i => i.val + 1 < a.val
  | 1 => Finset.univ.filter fun i => a.val + 1 < i.val ∧ i.val + 1 < b.val
  | 2 => Finset.univ.filter fun i => b.val + 1 < i.val

/-- The site intervals carrying the three separated cores of AKLV,
Section 6.1. Each omitted boundary bond separates adjacent intervals. -/
def normalizationCoreSites {L : ℕ} (a b : Fin (L - 1)) : Fin 3 → Finset (Fin L)
  | 0 => interval L 0 a.val
  | 1 => interval L (a.val + 2) b.val
  | 2 => interval L (b.val + 2) L

/-- The actual regional minimum shifts are obtained from the spectrum,
and their three shifted cores have a common unit zero vector.
Source: AKLV, Section 6.1, normalization preceding Theorem 6.1. -/
theorem exists_regional_minimum_shifts {L q : ℕ} [NeZero q]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ => q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (a b : Fin (L - 1)) (hab : a.val + 2 < b.val) :
    ∃ z : Fin 3 → ℝ,
      (∀ j, ((∑ i ∈ normalizationCoreBonds a b j, h i) - (z j : ℂ) • 1).PosSemidef) ∧
      ∃ v : (Fin L → Fin q) → ℂ, star v ⬝ᵥ v = 1 ∧
        ∀ j, ((∑ i ∈ normalizationCoreBonds a b j, h i) - (z j : ℂ) • 1) *ᵥ v = 0 := by
  classical
  let C (j : Fin 3) := ∑ i ∈ normalizationCoreBonds a b j, h i
  have hC (j : Fin 3) : (C j).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ => h0 i)).isHermitian
  let z (j : Fin 3) := minEigenvalue (hC j)
  have hsC (j : Fin 3) : C j ∈ supportedOperators q (normalizationCoreSites a b j : Set _) := by
    apply (supportedOperators q (normalizationCoreSites a b j : Set _)).sum_mem
    intro i hi
    apply supportedOperators_mono (S := (interval L i.val (i.val + 2) : Set _))
      (S' := (normalizationCoreSites a b j : Set _)) _
      (mem_supportedOperators_of_isSupportedOn (hs i))
    intro x hx
    fin_cases j <;>
      simp only [normalizationCoreBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hi <;>
      simp only [normalizationCoreSites, Finset.mem_coe, mem_interval] at hx ⊢ <;> omega
  have hd (j k : Fin 3) (hjk : j ≠ k) :
      Disjoint (normalizationCoreSites a b j : Set _) (normalizationCoreSites a b k : Set _) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    fin_cases j <;> fin_cases k <;>
      simp_all [normalizationCoreSites, mem_interval] <;> omega
  obtain ⟨v, hv, hAv, hBv, hCv⟩ := exists_normalized_common_ground_of_disjoint
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
    (hC 0) (hC 1) (hC 2) (hsC 0) (hsC 1) (hsC 2)
  refine ⟨z, fun j => sub_minEigenvalue_smul_one_posSemidef (hC j), v, hv, ?_⟩
  intro j
  fin_cases j
  · exact hAv
  · exact hBv
  · exact hCv

/-- Exactly the bonds outside the three regional cores remain as the
boundary interaction in AKLV, Section 6.1. -/
def normalizationBoundaryBonds {L : ℕ} (a b : Fin (L - 1)) : Finset (Fin (L - 1)) :=
  Finset.univ \ ((normalizationCoreBonds a b 0 ∪ normalizationCoreBonds a b 1) ∪
    normalizationCoreBonds a b 2)

/-- There are at most six untouched boundary bonds. The estimate includes
short exteriors; no boundary term is padded or assumed to vanish.
Source: AKLV, Section 6.1, the six positive unit boundary terms. -/
theorem normalizationBoundaryBonds_card_le_six {L : ℕ}
    (a b : Fin (L - 1)) (hab : a.val + 2 < b.val) :
    (normalizationBoundaryBonds a b).card ≤ 6 := by
  classical
  have hsub : (normalizationBoundaryBonds a b).image Fin.val ⊆
      Finset.Icc (a.val - 1) (a.val + 1) ∪ Finset.Icc (b.val - 1) (b.val + 1) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    simp only [normalizationBoundaryBonds, normalizationCoreBonds, Finset.mem_sdiff,
      Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and] at hi
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  calc
    (normalizationBoundaryBonds a b).card =
        ((normalizationBoundaryBonds a b).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.Icc (a.val - 1) (a.val + 1) ∪ Finset.Icc (b.val - 1) (b.val + 1)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (a.val - 1) (a.val + 1)).card +
        (Finset.Icc (b.val - 1) (b.val + 1)).card := Finset.card_union_le _ _
    _ ≤ 6 := by simp only [Nat.card_Icc]; omega

/-- The original chain splits into the three cores and the untouched
boundary interaction. Source: AKLV, Section 6.1. -/
theorem normalizationCoreBonds_sum {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (a b : Fin (L - 1)) (hab : a.val + 2 < b.val) :
    (∑ j : Fin 3, ∑ i ∈ normalizationCoreBonds a b j, h i) +
      (∑ i ∈ normalizationBoundaryBonds a b, h i) = ∑ i, h i := by
  classical
  have hp (i : Fin (L - 1)) :
      (if i ∈ normalizationCoreBonds a b 0 then h i else 0) +
      (if i ∈ normalizationCoreBonds a b 1 then h i else 0) +
      (if i ∈ normalizationCoreBonds a b 2 then h i else 0) +
      (if i ∈ normalizationBoundaryBonds a b then h i else 0) = h i := by
    simp only [normalizationCoreBonds, normalizationBoundaryBonds, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_union]
    split_ifs <;> simp_all <;> omega
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
  simpa only [Fin.sum_univ_three, Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using hh

/-- Enlarging a positive shifted core by original positive bonds preserves
positivity. Auxiliary to the three blocks of AKLV, Section 6.1. -/
private theorem shifted_sum_posSemidef_of_subset {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) {S T : Finset (Fin (L - 1))} (hST : S ⊆ T) (z : ℝ)
    (hS : ((∑ i ∈ S, h i) - (z : ℂ) • 1).PosSemidef) :
    ((∑ i ∈ T, h i) - (z : ℂ) • 1).PosSemidef := by
  have hp : (∑ i ∈ T \ S, h i).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ => h0 i)
  have hs := Finset.sum_sdiff hST (f := h)
  have heq : (∑ i ∈ T, h i) - (z : ℂ) • 1 =
      ((∑ i ∈ S, h i) - (z : ℂ) • 1) + ∑ i ∈ T \ S, h i := by
    rw [← hs]
    abel
  rw [heq]
  exact hS.add hp

/-- The actual core shifts make all three clipped blocks positive.
The one, two, and one untouched bonds inside these blocks remain positive;
the other two untouched bonds are the removed cut bonds.
Source: AKLV, Section 6.1 and the decomposition in Section 6.3. -/
theorem normalizedCutBlocks_posSemidef_of_core_shifts {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (a b : Fin (L - 1)) (hab : a.val + 2 < b.val)
    (z : Fin 3 → ℝ)
    (hz : ∀ j, ((∑ i ∈ normalizationCoreBonds a b j, h i) - (z j : ℂ) • 1).PosSemidef) :
    (leftCutBlock h a (z 0)).PosSemidef ∧
      (middleCutBlock h a b (z 1)).PosSemidef ∧
      (rightCutBlock h b (z 2)).PosSemidef := by
  classical
  refine ⟨shifted_sum_posSemidef_of_subset h h0 ?_ (z 0) (hz 0),
    shifted_sum_posSemidef_of_subset h h0 ?_ (z 1) (hz 1),
    shifted_sum_posSemidef_of_subset h h0 ?_ (z 2) (hz 2)⟩ <;>
    intro i hi <;>
    simp only [normalizationCoreBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢ <;>
    omega

/-- Normalizing the original chain at the actual regional minima derives
all three positive clipped blocks and the ground energy bound \(0\le e\le6\).
The only spectral inputs describe the original chain ground vector and
its ground lower bound. No shifted positivity or energy bound is assumed.
Source: AKLV, Section 6.1, normalization preceding Theorem 6.1. -/
theorem exists_normalized_chain_data {L q : ℕ} [NeZero q]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ => q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val + 2 < b.val)
    (E : ℝ) (Ω : (Fin L → Fin q) → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (heig : (∑ i, h i) *ᵥ Ω = (E : ℂ) • Ω)
    (hlow : ((∑ i, h i) - (E : ℂ) • 1).PosSemidef) :
    ∃ z : Fin 3 → ℝ,
      (leftCutBlock h a (z 0)).PosSemidef ∧
      (middleCutBlock h a b (z 1)).PosSemidef ∧
      (rightCutBlock h b (z 2)).PosSemidef ∧
      0 ≤ E - ∑ j, z j ∧ E - ∑ j, z j ≤ 6 := by
  classical
  obtain ⟨z, hz, v, hv, hzero⟩ := exists_regional_minimum_shifts h hs h0 a b hab
  let C := ∑ j : Fin 3, ((∑ i ∈ normalizationCoreBonds a b j, h i) - (z j : ℂ) • 1)
  let B := ∑ i ∈ normalizationBoundaryBonds a b, h i
  let e := E - ∑ j, z j
  have hC : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun j _ => (hz j).nonneg)
  have hCv : C *ᵥ v = 0 := by simp only [C, Matrix.sum_mulVec, hzero, Finset.sum_const_zero]
  have hdecomp : C + B = (∑ i, h i) - ((∑ j, z j : ℝ) : ℂ) • 1 := by
    have hh := normalizationCoreBonds_sum h a b hab
    simp only [C, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum]
    dsimp only [B]
    rw [sub_add_eq_add_sub, hh]
  obtain ⟨hB, hBcap⟩ := Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms
    (normalizationBoundaryBonds a b) h (fun i _ => h0 i) (fun i _ => h1 i)
  have hBcap' : B ≤ ((normalizationBoundaryBonds a b).card : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    simpa only [B, RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_natCast]
      using hBcap
  have hB6 : B ≤ (6 : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    refine hBcap'.trans ?_
    rw [← sub_nonneg]
    apply Matrix.nonneg_iff_posSemidef.mpr
    rw [← sub_smul]
    have hc : (0 : ℝ) ≤ 6 - (normalizationBoundaryBonds a b).card := by
      exact sub_nonneg.mpr (by exact_mod_cast normalizationBoundaryBonds_card_le_six a b hab)
    simpa only [Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_natCast] using
      (Matrix.PosSemidef.one (n := Fin L → Fin q) (R := ℂ)).smul
        (Complex.zero_le_real.mpr hc)
  have heig' : (C + B) *ᵥ Ω = (e : ℂ) • Ω := by
    rw [hdecomp, sub_mulVec, smul_mulVec, one_mulVec, heig]
    simp only [e, Complex.ofReal_sub, sub_smul]
  have hlow' : (C + B - (e : ℂ) • 1).PosSemidef := by
    have heq : C + B - (e : ℂ) • 1 = (∑ i, h i) - (E : ℂ) • 1 := by
      rw [hdecomp]
      simp only [e, Complex.ofReal_sub, sub_smul]
      abel
    rw [heq]
    exact hlow
  obtain ⟨he0, he6⟩ := Matrix.groundEnergy_bounds_of_positive_boundary_and_zero_test
    C B 6 e hC hB hB6 v Ω hCv hv heig' hΩ hlow'
  obtain ⟨hX, hN, hY⟩ := normalizedCutBlocks_posSemidef_of_core_shifts h h0 a b hab z hz
  exact ⟨z, hX, hN, hY, he0, he6⟩

end TNLean.MPS.AreaLaw.AKLV
