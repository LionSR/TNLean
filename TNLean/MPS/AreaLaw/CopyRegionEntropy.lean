/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyProduct
import TNLean.MPS.AreaLaw.Basic
import QICLean.Entropy.RegionSplit
import QICLean.Entropy.MovementEtaRegional
import QICLean.Entropy.OrderedEntropyAlgebra

/-!
# Regional entropy of consecutive block products

A region contained in one copy has the same reduced state as the corresponding
region of that copy. Subadditivity then bounds the entropy of a contiguous
region by the contributions of its at most two partially intersected copies.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 421–479.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw

variable {K L q : ℕ}

/-- Embed a region of one copy into its literal chain sites. -/
def copyRegion (i : Fin K) (R : Finset (Fin L)) : Finset (Fin (K * L)) :=
  Finset.univ.filter fun s ↦ (finProdFinEquiv.symm s).1 = i ∧
    (finProdFinEquiv.symm s).2 ∈ R

/-- Membership in a copy region identifies both the block and the local site. -/
private theorem mem_copyRegion (i j : Fin K) (k : Fin L) (R : Finset (Fin L)) :
    finProdFinEquiv (j, k) ∈ copyRegion i R ↔ j = i ∧ k ∈ R := by
  simp only [copyRegion, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.symm_apply_apply]

/-- Restriction identifies the configurations of an embedded copy region. -/
def copyRegionConfigurationEquiv (i : Fin K) (R : Finset (Fin L)) :
    Entropy.RegionConfig (fun _ : Fin (K * L) ↦ q) (copyRegion i R) ≃
      Entropy.RegionConfig (fun _ : Fin L ↦ q) R where
  toFun σ j := σ ⟨finProdFinEquiv (i, j.1), (mem_copyRegion i i j.1 R).mpr ⟨rfl, j.2⟩⟩
  invFun τ s := τ ⟨(finProdFinEquiv.symm s.1).2,
    (Finset.mem_filter.mp s.2).2.2⟩
  left_inv σ := by
    funext s
    apply congrArg σ
    apply Subtype.ext
    have hi := (Finset.mem_filter.mp s.2).2.1
    change finProdFinEquiv (i, (finProdFinEquiv.symm s.1).2) = s.1
    exact (congrArg finProdFinEquiv (show finProdFinEquiv.symm s.1 =
      (i, (finProdFinEquiv.symm s.1).2) from Prod.ext hi rfl)).symm.trans
        (finProdFinEquiv.apply_symm_apply s.1)
  right_inv τ := by
    funext j
    apply congrArg τ
    apply Subtype.ext
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, j.1))

/-- Split a chain into the selected local region, its local complement, and all
other copies. -/
private def copyRegionSplit (i : Fin K) (R : Finset (Fin L)) :
    (Fin (K * L) → Fin q) ≃
      Entropy.RegionConfig (fun _ : Fin L ↦ q) R ×
        (((j : {j : Fin L // j ∉ R}) → Fin q) ×
          ({j : Fin K // j ≠ i} → Fin L → Fin q)) :=
  ((copyConfigurationEquiv K L q).trans (Equiv.piSplitAt i (fun _ ↦ Fin L → Fin q))).trans
    (((Entropy.cutEquiv (fun _ : Fin L ↦ q) R).prodCongr (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _))

/-- The explicit three-part coordinates split precisely along the embedded region. -/
private theorem isRegionSplit_copyRegion (i : Fin K) (R : Finset (Fin L)) :
    Entropy.IsRegionSplit (copyRegion i R) (copyRegionConfigurationEquiv (q := q) i R)
      (copyRegionSplit i R) := by
  refine ⟨fun _ ↦ rfl, ?_⟩
  intro σ τ
  constructor
  · intro h s hs
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective s
    by_cases hji : j = i
    · subst j
      have hk : k ∉ R := fun hk ↦ hs ((mem_copyRegion i i k R).mpr ⟨rfl, hk⟩)
      exact congrFun (congrArg Prod.fst h) ⟨k, hk⟩
    · exact congrFun (congrFun (congrArg Prod.snd h) ⟨j, hji⟩) k
  · intro h
    apply Prod.ext
    · funext k
      exact h (finProdFinEquiv (i, k.1))
        (fun hm ↦ k.2 ((mem_copyRegion i i k.1 R).mp hm).2)
    · funext j k
      exact h (finProdFinEquiv (j.1, k))
        (fun hm ↦ j.2 ((mem_copyRegion i j.1 k R).mp hm).1)

/-- In the region split, the product coefficient separates the selected copy
from the product of all other copies. -/
private theorem copyProduct_copyRegionSplit_symm
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) (i : Fin K) (R : Finset (Fin L))
    (a : Entropy.RegionConfig (fun _ : Fin L ↦ q) R)
    (b : (j : {j : Fin L // j ∉ R}) → Fin q)
    (c : {j : Fin K // j ≠ i} → Fin L → Fin q) :
    copyProduct η ((copyRegionSplit i R).symm (a, (b, c))) =
      η i ((Entropy.cutEquiv (fun _ : Fin L ↦ q) R).symm (a, b)) *
        EuclideanSpace.piTensor (fun j : {j : Fin K // j ≠ i} ↦ η j.1) c := by
  classical
  let σ := (copyRegionSplit (q := q) i R).symm (a, (b, c))
  have hc := (copyRegionSplit (q := q) i R).apply_symm_apply (a, (b, c))
  have hlocal : copyConfigurationEquiv K L q σ i =
      (Entropy.cutEquiv (fun _ : Fin L ↦ q) R).symm (a, b) := by
    apply (Entropy.cutEquiv (fun _ : Fin L ↦ q) R).injective
    rw [Equiv.apply_symm_apply]
    have hca := congrArg Prod.fst hc
    have hcb := congrArg (fun z ↦ z.2.1) hc
    exact Prod.ext hca hcb
  have hother : (fun j : {j : Fin K // j ≠ i} ↦ copyConfigurationEquiv K L q σ j.1) = c :=
    congrArg (fun z ↦ z.2.2) hc
  change (∏ j, η j (copyConfigurationEquiv K L q σ j)) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, hlocal]
  congr 1
  change (∏ j : {j : Fin K // j ≠ i}, η j.1 (copyConfigurationEquiv K L q σ j.1)) = _
  exact congrArg (EuclideanSpace.piTensor (fun j : {j : Fin K // j ≠ i} ↦ η j.1)) hother

/-- The reduced state of an embedded region of one copy is that copy's reduced
state, after the explicit configuration identification. -/
theorem regionState_copyProduct (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q))
    (hη : ∀ j, ‖η j‖ = 1) (i : Fin K) (R : Finset (Fin L)) :
    (Entropy.regionState (copyRegion i R) (copyProduct η)).submatrix
      (copyRegionConfigurationEquiv (q := q) i R).symm
      (copyRegionConfigurationEquiv (q := q) i R).symm =
        Entropy.regionState R (η i) := by
  classical
  let ν := EuclideanSpace.piTensor (fun j : {j : Fin K // j ≠ i} ↦ η j.1)
  have hn : ‖ν‖ = 1 := by simp [ν, EuclideanSpace.norm_piTensor, hη]
  have hs : ∑ c, ν c * star (ν c) = 1 := by
    change inner ℂ ν ν = 1
    rw [inner_self_eq_norm_sq_to_K, hn]
    norm_num
  have hsplit := (isRegionSplit_copyRegion (q := q) i R).partialTraceRight_vecMulVec
    (fun σ ↦ copyProduct η σ)
  rw [← hsplit]
  ext a a'
  simp only [Matrix.partialTraceRight_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Function.comp_apply, Fintype.sum_prod_type, copyProduct_copyRegionSplit_symm]
  let ω := Entropy.cutVector R (η i)
  change (∑ b, ∑ c, (ω (a, b) * ν c) * star (ω (a', b) * ν c)) =
    ∑ b, ω (a, b) * star (ω (a', b))
  calc
    _ = (∑ b, ω (a, b) * star (ω (a', b))) * (∑ c, ν c * star (ν c)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      simp only [star_mul]
      ring
    _ = _ := by rw [hs, mul_one]

/-- Embedding a region in one factor of a normalized block product preserves
its entropy. The identity includes empty and full local regions. -/
theorem regionEntropy_copyProduct (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q))
    (hη : ∀ j, ‖η j‖ = 1) (i : Fin K) (R : Finset (Fin L)) :
    Entropy.regionEntropy (copyRegion i R) (copyProduct η) =
      Entropy.regionEntropy R (η i) := by
  unfold Entropy.regionEntropy
  rw [← vonNeumannEntropy_submatrix_equiv (copyRegionConfigurationEquiv (q := q) i R).symm
    (Entropy.regionState (copyRegion i R) (copyProduct η))
    (Entropy.regionState_isHermitian (copyRegion i R) (copyProduct η))]
  exact vonNeumannEntropy_congr (regionState_copyProduct η hη i R) _ _

/-- Regional subadditivity over disjoint copies, with each term identified with
its actual single-copy marginal. -/
theorem regionEntropy_copyRegions_le_sum
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) (hη : ∀ j, ‖η j‖ = 1)
    (R : Fin K → Finset (Fin L)) :
    Entropy.regionEntropy (Finset.univ.biUnion fun i ↦ copyRegion i (R i)) (copyProduct η) ≤
      ∑ i, Entropy.regionEntropy (R i) (η i) := by
  classical
  have hn : ‖copyProduct η‖ = 1 := by simp [norm_copyProduct, hη]
  have hempty : Entropy.regionEntropy ∅ (copyProduct η) = 0 := by
    rw [Entropy.regionEntropy_eq_entropy, FiniteProduct.entropy_empty _ _ hn]
  have hsub (A B : Finset (Fin (K * L))) (hAB : Disjoint A B) :
      Entropy.regionEntropy (A ∪ B) (copyProduct η) ≤
        Entropy.regionEntropy A (copyProduct η) + Entropy.regionEntropy B (copyProduct η) := by
    simp only [Entropy.regionEntropy_eq_entropy]
    exact FiniteProduct.entropy_union_le _ _ hn A B hAB
  have hdis : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (fun i ↦ copyRegion i (R i)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro s hi hj
    exact hij ((Finset.mem_filter.mp hi).2.1.symm.trans (Finset.mem_filter.mp hj).2.1)
  have h := Entropy.OrderedSetFunction.union_biUnion_le_sum
    (fun A ↦ Entropy.regionEntropy A (copyProduct η)) hsub ∅
    (fun i ↦ copyRegion i (R i)) Finset.univ (by simp) hdis
  simpa only [Finset.empty_union, hempty, zero_add, regionEntropy_copyProduct η hη] using h

/-- The sites of block i retained by the half-open interval [a,b). -/
private def copyIntervalRegion (L a b : ℕ) {K : ℕ} (i : Fin K) : Finset (Fin L) :=
  Finset.univ.filter fun j ↦ a ≤ L * i.val + j.val ∧ L * i.val + j.val < b

/-- A partially retained block contains one of the interval endpoints. -/
private theorem partialCopy_index {K L a b : ℕ} (i : Fin K)
    (hne : copyIntervalRegion L a b i ≠ ∅) (hfull : copyIntervalRegion L a b i ≠ Finset.univ) :
    i.val = a / L ∨ i.val = b / L := by
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hj' : a ≤ L * i.val + j.val ∧ L * i.val + j.val < b :=
    (Finset.mem_filter.mp hj).2
  have hk : ∃ k : Fin L, k ∉ copyIntervalRegion L a b i := by
    by_contra h
    push Not at h
    exact hfull (Finset.eq_univ_of_forall h)
  obtain ⟨k, hk⟩ := hk
  have hL : 0 < L := Nat.zero_lt_of_lt j.isLt
  have hk' : ¬ (a ≤ L * i.val + k.val ∧ L * i.val + k.val < b) := by
    simpa [copyIntervalRegion] using hk
  rcases not_and_or.mp hk' with hkleft | hkright
  · left
    symm
    apply (Nat.div_eq_iff hL).2
    constructor
    · nlinarith
    · have hupper : a < i.val * L + L := by nlinarith [j.isLt]
      omega
  · right
    symm
    apply (Nat.div_eq_iff hL).2
    constructor
    · nlinarith
    · have hupper : b < i.val * L + L := by nlinarith [k.isLt]
      omega

/-- A contiguous interval partially intersects at most two blocks. -/
private theorem card_partialCopies_le_two (K L a b : ℕ) :
    (Finset.univ.filter fun i : Fin K ↦
      copyIntervalRegion L a b i ≠ ∅ ∧ copyIntervalRegion L a b i ≠ Finset.univ).card ≤ 2 := by
  let S : Finset (Fin K) := Finset.univ.filter fun i ↦
    copyIntervalRegion L a b i ≠ ∅ ∧ copyIntervalRegion L a b i ≠ Finset.univ
  change S.card ≤ 2
  calc
    S.card = (S.image Fin.val).card :=
      (Finset.card_image_of_injective S Fin.val_injective).symm
    _ ≤ ({a / L, b / L} : Finset ℕ).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      have hi' := (Finset.mem_filter.mp hi).2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using partialCopy_index i hi'.1 hi'.2
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

/-- The local intersections with an interval partition that interval. -/
private theorem biUnion_copyIntervalRegion (K L a b : ℕ) :
    Finset.univ.biUnion (fun i : Fin K ↦ copyRegion i (copyIntervalRegion L a b i)) =
      interval (K * L) a b := by
  classical
  ext s
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective s
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_copyRegion, exists_eq_left',
    mem_interval]
  change j ∈ copyIntervalRegion L a b i ↔
    a ≤ j.val + L * i.val ∧ j.val + L * i.val < b
  simp [copyIntervalRegion, Nat.add_comm]

/-- A uniform regional entropy bound for one unit block gives twice that bound
for every contiguous region of its literal tensor power.
Source: arXiv:0705.0292v2, lines 421–479. Only the two partially intersected
copies contribute; no factorization of reduced states is assumed. -/
theorem regionEntropy_interval_copyProduct_le
    {η : EuclideanSpace ℂ (Fin L → Fin q)} (hη : ‖η‖ = 1) {B : ℝ}
    (hB : ∀ R : Finset (Fin L), Entropy.regionEntropy R η ≤ B) (K a b : ℕ) :
    Entropy.regionEntropy (interval (K * L) a b)
      (copyProduct (fun _ : Fin K ↦ η)) ≤ 2 * B := by
  classical
  have hzero : Entropy.regionEntropy ∅ η = 0 := by
    rw [Entropy.regionEntropy_eq_entropy, FiniteProduct.entropy_empty _ _ hη]
  have hfull : Entropy.regionEntropy Finset.univ η = 0 := by
    rw [Entropy.regionEntropy_eq_entropy, FiniteProduct.entropy_univ _ _ hη]
  have hB0 : 0 ≤ B := by simpa only [hzero] using hB ∅
  let R := copyIntervalRegion L a b (K := K)
  let S : Finset (Fin K) := Finset.univ.filter fun i ↦ R i ≠ ∅ ∧ R i ≠ Finset.univ
  have hout (i : Fin K) (hi : i ∉ S) : Entropy.regionEntropy (R i) η = 0 := by
    by_cases he : R i = ∅
    · rw [he, hzero]
    · have hf : R i = Finset.univ := by
        by_contra hf
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, he, hf⟩)
      rw [hf, hfull]
  have hsum : (∑ i, Entropy.regionEntropy (R i) η) =
      ∑ i ∈ S, Entropy.regionEntropy (R i) η :=
    (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi ↦ hout i hi)).symm
  have hcard : S.card ≤ 2 := card_partialCopies_le_two K L a b
  calc
    _ ≤ ∑ i, Entropy.regionEntropy (R i) η := by
      simpa only [R, biUnion_copyIntervalRegion] using
        regionEntropy_copyRegions_le_sum (fun _ : Fin K ↦ η) (fun _ ↦ hη) R
    _ = ∑ i ∈ S, Entropy.regionEntropy (R i) η := hsum
    _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum fun i _ ↦ hB (R i)
    _ = (S.card : ℝ) * B := by simp
    _ ≤ 2 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB0

end TNLean.MPS.AreaLaw
