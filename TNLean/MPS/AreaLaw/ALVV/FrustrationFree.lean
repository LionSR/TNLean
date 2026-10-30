/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DetectabilityLemma
import QICLean.Analysis.WeightedPositiveKernel

/-!
# The frustration-free regional replacement

ALVV, arXiv:1602.08828v2, Definition 5.10 and Theorem 5.14 replace the even and odd
terms in a region by the complements of their ground-space projections, retaining
all exterior terms. The generic detectability inequalities are imported from QICLean.
The algebraic kernel statements below allow arbitrary commuting selected layers and retain
the full ground space. The printed rank conclusion of Theorem 5.14 is not asserted:
`docs/paper-gaps/alvv16_ff_rank.tex` gives an exact counterexample to its printed bound
for interior regions.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

namespace TNLean.MPS.AreaLaw.ALVV

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A product of commuting complementary projections fixes precisely their common kernel.
This identifies the regional ground spaces in ALVV, Definition 5.10. -/
theorem complementProd_apply_eq_self_iff {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (hc : ∀ i j, Commute (h i) (h j))
    (n : ℕ) (x : E) :
    complementProd h n x = x ↔ ∀ i < n, h i x = 0 := by
  constructor
  · intro hfix i hi
    have hz := norm_apply_complementProd_le hh x hi
    simp only [hc, not_true_eq_false, and_false, Finset.filter_false, Finset.sum_empty] at hz
    rw [hfix] at hz
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
  · intro hx
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [complementProd_succ_apply, ih (fun i hi ↦ hx i (by omega)), hx n (by omega),
        sub_zero]

/-- Mask a family by a set of indices. Zero factors preserve the complementary product.
ALVV, Definition 5.10. -/
noncomputable def restrictedTerm (h : ℕ → E →L[𝕜] E) (s : Finset ℕ)
    (i : ℕ) : E →L[𝕜] E := if i ∈ s then h i else 0

/-- A masked projection is still a projection. -/
theorem isStarProjection_restrictedTerm {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (s : Finset ℕ) (i : ℕ) :
    IsStarProjection (restrictedTerm h s i) := by
  classical
  unfold restrictedTerm
  split
  · exact hh i
  · exact IsStarProjection.zero _

omit [CompleteSpace E] in
/-- Commutation is inherited by masking a commuting subfamily. -/
theorem commute_restrictedTerm {h : ℕ → E →L[𝕜] E} (s : Finset ℕ)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (h i) (h j)) (i j : ℕ) :
    Commute (restrictedTerm h s i) (restrictedTerm h s j) := by
  classical
  unfold restrictedTerm
  split <;> split
  · exact hc i ‹_› j ‹_›
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

/-- The regional even or odd ground-space projection, with factors in increasing order
of action. ALVV, Definition 5.10. -/
noncomputable def regionalProjection (h : ℕ → E →L[𝕜] E) (s : Finset ℕ)
    (m : ℕ) : E →L[𝕜] E := complementProd (restrictedTerm h s) m

/-- Each parity layer of the regional replacement is an orthogonal projection.
ALVV, Definition 5.10. -/
theorem isStarProjection_regionalProjection {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (s : Finset ℕ)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (h i) (h j)) (m : ℕ) :
    IsStarProjection (regionalProjection h s m) :=
  isStarProjection_complementProd (isStarProjection_restrictedTerm hh s)
    (commute_restrictedTerm s hc) m

/-- Vanishing of a layer complement means that every term in that layer vanishes.
ALVV, Theorem 5.14(1). -/
theorem sub_regionalProjection_apply_eq_zero_iff {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (s : Finset ℕ)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (h i) (h j)) (m : ℕ) (x : E) :
    (1 - regionalProjection h s m) x = 0 ↔ ∀ i < m, i ∈ s → h i x = 0 := by
  classical
  change x - regionalProjection h s m x = 0 ↔ _
  rw [sub_eq_zero, eq_comm]
  rw [regionalProjection, complementProd_apply_eq_self_iff
    (isStarProjection_restrictedTerm hh s) (commute_restrictedTerm s hc)]
  simp only [restrictedTerm]
  constructor
  · intro hx i hi hs
    simpa only [hs, ↓reduceIte] using hx i hi
  · intro hx i hi
    split_ifs with hs
    · exact hx i hi hs
    · rfl

/-- ALVV's regional replacement, with all exterior terms retained.
The disjoint sets `even` and `odd` select the regional parity layers. -/
noncomputable def regionalReplacement (h : ℕ → E →L[𝕜] E)
    (even odd : Finset ℕ) (m : ℕ) : E →L[𝕜] E :=
  (∑ i ∈ Finset.range m, restrictedTerm h (Finset.range m \ (even ∪ odd)) i) +
    (1 - regionalProjection h even m) + (1 - regionalProjection h odd m)

private theorem sum_apply_eq_zero_iff {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (m : ℕ) (x : E) :
    (∑ i ∈ Finset.range m, h i) x = 0 ↔ ∀ i < m, h i x = 0 := by
  have hp (i : Fin m) : (h i).toLinearMap.IsPositive :=
    (ContinuousLinearMap.IsPositive.of_isStarProjection (hh i)).toLinearMap
  have ht := WeightedPositiveKernel.apply_sum_eq_zero_iff hp x
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, Fin.forall_iff] at ht
  rw [show (∑ i : Fin m, h i x) = ∑ i ∈ Finset.range m, h i x from
    Fin.sum_univ_eq_sum_range (fun i ↦ h i x) m] at ht
  simpa only [sum_apply] using ht

omit [CompleteSpace E] in
private theorem add_apply_eq_zero_iff {A B : E →L[𝕜] E}
    (hA : A.IsPositive) (hB : B.IsPositive) (x : E) :
    (A + B) x = 0 ↔ A x = 0 ∧ B x = 0 := by
  let P : Fin 2 → E →ₗ[𝕜] E := ![A.toLinearMap, B.toLinearMap]
  have hp : ∀ i, (P i).IsPositive := by
    intro i
    fin_cases i
    · exact hA.toLinearMap
    · exact hB.toLinearMap
  simpa [P, Fin.sum_univ_two, Fin.forall_fin_two] using
    WeightedPositiveKernel.apply_sum_eq_zero_iff hp x

/-- Exact common-kernel characterization of the regional replacement, including exterior
terms. ALVV, Theorem 5.14(1). Neither uniqueness nor a spectral gap is needed. -/
theorem regionalReplacement_apply_eq_zero_iff {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (even odd : Finset ℕ)
    (he : ∀ i ∈ even, ∀ j ∈ even, Commute (h i) (h j))
    (ho : ∀ i ∈ odd, ∀ j ∈ odd, Commute (h i) (h j)) (m : ℕ) (x : E) :
    regionalReplacement h even odd m x = 0 ↔ ∀ i < m, h i x = 0 := by
  classical
  have heP := (isStarProjection_regionalProjection hh even he m).one_sub
  have hoP := (isStarProjection_regionalProjection hh odd ho m).one_sub
  have hout := isStarProjection_restrictedTerm hh (Finset.range m \ (even ∪ odd))
  have hpos := ContinuousLinearMap.isPositive_sum (Finset.range m)
    (fun i _ ↦ ContinuousLinearMap.IsPositive.of_isStarProjection (hout i))
  unfold regionalReplacement
  rw [add_apply_eq_zero_iff
      (hpos.add (ContinuousLinearMap.IsPositive.of_isStarProjection heP))
      (ContinuousLinearMap.IsPositive.of_isStarProjection hoP),
    add_apply_eq_zero_iff hpos (ContinuousLinearMap.IsPositive.of_isStarProjection heP),
    sum_apply_eq_zero_iff hout,
    sub_regionalProjection_apply_eq_zero_iff hh even he,
    sub_regionalProjection_apply_eq_zero_iff hh odd ho]
  simp only [restrictedTerm]
  constructor
  · rintro ⟨⟨hout, he⟩, ho⟩ i hi
    by_cases hie : i ∈ even
    · exact he i hi hie
    by_cases hio : i ∈ odd
    · exact ho i hi hio
    simpa [hi, hie, hio] using hout i hi
  · intro hx
    refine ⟨⟨?_, fun i hi _ ↦ hx i hi⟩, fun i hi _ ↦ hx i hi⟩
    intro i hi
    split_ifs <;> simp [hx i hi]

/-- The replacement has the full original kernel, including degenerate ground spaces.
ALVV, Theorem 5.14(1). -/
theorem ker_regionalReplacement {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (even odd : Finset ℕ)
    (he : ∀ i ∈ even, ∀ j ∈ even, Commute (h i) (h j))
    (ho : ∀ i ∈ odd, ∀ j ∈ odd, Commute (h i) (h j)) (m : ℕ) :
    LinearMap.ker (regionalReplacement h even odd m).toLinearMap =
      LinearMap.ker (∑ i ∈ Finset.range m, h i).toLinearMap := by
  ext x
  exact (regionalReplacement_apply_eq_zero_iff hh even odd he ho m x).trans
    (sum_apply_eq_zero_iff hh m x).symm

/-- Every original zero-energy vector is annihilated by both regional layer terms and
all retained exterior terms. ALVV, Theorem 5.14(1). -/
theorem regionalReplacement_frustrationFree {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (even odd : Finset ℕ)
    (he : ∀ i ∈ even, ∀ j ∈ even, Commute (h i) (h j))
    (ho : ∀ i ∈ odd, ∀ j ∈ odd, Commute (h i) (h j))
    (m : ℕ) {x : E} (hx : ∀ i < m, h i x = 0) :
    (1 - regionalProjection h even m) x = 0 ∧
    (1 - regionalProjection h odd m) x = 0 ∧
    ∀ i < m, i ∉ even ∪ odd → h i x = 0 :=
  ⟨(sub_regionalProjection_apply_eq_zero_iff hh even he m x).mpr
    (fun i hi _ ↦ hx i hi),
   (sub_regionalProjection_apply_eq_zero_iff hh odd ho m x).mpr
    (fun i hi _ ↦ hx i hi), fun i hi _ ↦ hx i hi⟩

/-- The regional replacement is positive. ALVV, Theorem 5.14(1). -/
theorem isPositive_regionalReplacement {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (even odd : Finset ℕ)
    (he : ∀ i ∈ even, ∀ j ∈ even, Commute (h i) (h j))
    (ho : ∀ i ∈ odd, ∀ j ∈ odd, Commute (h i) (h j)) (m : ℕ) :
    (regionalReplacement h even odd m).IsPositive :=
  ((ContinuousLinearMap.isPositive_sum (Finset.range m) fun i _ ↦
      ContinuousLinearMap.IsPositive.of_isStarProjection
        (isStarProjection_restrictedTerm hh _ i)).add
    (ContinuousLinearMap.IsPositive.of_isStarProjection
      (isStarProjection_regionalProjection hh even he m).one_sub)).add
    (ContinuousLinearMap.IsPositive.of_isStarProjection
      (isStarProjection_regionalProjection hh odd ho m).one_sub)

omit [CompleteSpace E] in
/-- Collapsing one commuting parity layer preserves its full complementary product.
This factorization underlies the detectability-operator identity in ALVV, Theorem 5.14. -/
theorem regionalProjection_mul_complement {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, Commute (h i) (h j)) (s : Finset ℕ) (m : ℕ) :
    regionalProjection h s m * regionalProjection h (Finset.range m \ s) m =
      complementProd h m := by
  classical
  have hmask : ∀ i j, Commute (restrictedTerm h s i)
      (restrictedTerm h (Finset.range m \ s) j) := by
    intro i j
    unfold restrictedTerm
    split <;> split
    · exact hc i j
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  have hprod (k : ℕ) (hk : k ≤ m) :
      complementProd (restrictedTerm h s) k *
        complementProd (restrictedTerm h (Finset.range m \ s)) k = complementProd h k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [complementProd_succ, complementProd_succ, mul_assoc]
      have hcomm : Commute (complementProd (restrictedTerm h s) k)
          (1 - restrictedTerm h (Finset.range m \ s) k) :=
        (Commute.one_right _).sub_right
          (commute_complementProd (fun j _ ↦ (hmask j k).symm)).symm
      rw [← mul_assoc _ (1 - restrictedTerm h (Finset.range m \ s) k),
        hcomm.eq, mul_assoc, ← mul_assoc (1 - restrictedTerm h s k), ih (by omega)]
      have hfactor : (1 - restrictedTerm h s k) *
          (1 - restrictedTerm h (Finset.range m \ s) k) = 1 - h k := by
        by_cases hs : k ∈ s <;> simp [restrictedTerm, hs, show k < m by omega]
      rw [hfactor, complementProd_succ]
  exact hprod m le_rfl

end TNLean.MPS.AreaLaw.ALVV
