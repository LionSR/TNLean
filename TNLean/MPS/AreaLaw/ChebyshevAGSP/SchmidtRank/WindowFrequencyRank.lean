/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.OperatorSchmidtPartition
import QICLean.Algebra.Word.OneMarkerFullCounts
import QICLean.Algebra.Word.LowFrequencyWordPartition
import Mathlib.Algebra.BigOperators.Fin
import QICLean.ManyBody.Entropy.RegionEntropy
import Mathlib.Data.Nat.Sqrt
import QICLean.Algebra.Combinatorics.BinomialFrequencySum
import Mathlib.Algebra.Polynomial.AlgebraMap
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.Tensor.VaryingBond.OpenMPS
import QICLean.Algebra.OperatorSchmidt.WeightedFrequencySchmidtRank
import QICLean.ManyBody.Sites.OperatorSchmidtRank
import Mathlib.LinearAlgebra.Matrix.Reindex

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

## Transport of an AKLV frequency estimate to another chain cut

The same operator is compared at two actual prefix cuts. Moving the cut by `d` sites
costs at most `q ^ (2 * d)` in operator Schmidt rank. Applied to the actual window
coefficient family, this gives its rank at the central cut without selecting a new
operator or assuming a representation there.

**Local fix (count):** The inherited fixed-frequency estimate uses the corrected
commuting-gap binomial coefficient recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 651--654.
The low-frequency partition and the final optimized polynomial estimate are separate.

## The original full-frequency family at a target cut

The fixed-frequency rank estimate applies to the actual original window alphabet,
without assuming that a selected coefficient family has an optional-letter presentation.
The latter presentation follows by renaming words and inserting the distinguished count.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 626--662.
**Local fix (count):** The corrected commuting-gap count is documented in
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

## The actual low-frequency decomposition at the central AKLV cut

The actual full-frequency coefficients are partitioned by a minimum-frequency middle
interaction and its occurrence count. Each resulting operator is estimated using the
fixed-frequency bound and transported to the central cut. The same selected operator
is retained throughout; no suitable marker or coefficient-rank estimate is assumed.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--662.
**Local fix (count):** The commuting-gap binomial coefficient uses the correction at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
The subsequent binomial estimates and optimization are separate results.

## Regrouping an AKLV window around the same central cut

A consecutive subwindow of the actual nearest-neighbour interactions is retained.
The omitted interactions are summed into the corresponding exterior operators;
the Hamiltonian is unchanged and the required exterior supports follow from those
of the original terms. No supplied regrouping or new operator family is assumed.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 586--603 and 658--663.

## A uniform polynomial rank estimate for a bounded AKLV window

The actual power decomposition is bounded uniformly over all degrees up to a prescribed
cutoff. Expansion into powers then gives the same estimate for arbitrary complex
polynomials, with one additional factor for the number of degrees.

**Local fix (count):** The commuting-gap coefficient uses the correction at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 598--663.
The restriction on the window width is explicit here; the unrestricted central-cut
statement follows by regrouping the actual interactions into a shorter window.

It also contains the following results.

* `TNLean.MPS.AreaLaw.operatorSchmidtRank_one_marker_of_chain_supports_le`: the one-marker frequency
  rank estimate from actual chain supports.
-/

section OneMarkerRank

/-!
## The one-marker frequency rank estimate from actual chain supports

One distinguished operator crosses a chosen cut on an adjacent pair. Every ordinary
operator is supported on one side. The left and right tensor factors are derived from
these supports, and the actual ordered-word coefficient family obeys the corrected
interpolation and commuting-gap rank bound. No tensor decomposition or coefficient-rank
estimate is supplied as a hypothesis.

**Local fix (count):** The exponent-tuple factor retains the additional `+1` recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), source lines 626--662.
This is the fixed-frequency estimate at its distinguished cut. Partition into low
frequencies, summation over distinguished cuts and optimization remain separate steps.
-/

open ManyBody (interval mem_interval)

open Matrix
open scoped BigOperators Kronecker

namespace TNLean.MPS.AreaLaw

open Classical in
/-- The actual weighted one-marker word coefficients satisfy the AKLV rank estimate
when the ordinary terms are physically one-sided and the marker crosses one adjacent
pair. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 626--662. -/
theorem operatorSchmidtRank_one_marker_of_chain_supports_le
    {L q cut : ℕ} {ι : Type*} [Fintype ι] (hq : 1 ≤ q)
    (hcut0 : 0 < cut) (hcutL : cut < L)
    (H : ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (X : ι → Finset (Fin L)) (hH : ∀ a, ManyBody.IsSupportedOn (H a) (X a))
    (hside : ∀ a, X a ⊆ interval L 0 cut ∨ Disjoint (X a) (interval L 0 cut))
    (T : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hT : ManyBody.IsSupportedOn T (interval L (cut - 1) (cut + 1))) (t k : ℕ) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) t
    ∀ weight : E → ℂ, operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut)
        (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient H T t k α.val)) ≤
      E.card * ((t + 2 * k + 1).choose (2 * k + 1) * q ^ (2 * k)) := by
  classical
  let : NeZero q := ⟨by omega⟩
  intro E weight
  let : DecidableEq ((v : {v : Fin L // v ∈ interval L 0 cut}) → Fin q) :=
    Classical.decEq _
  let : DecidableEq ((v : {v : Fin L // v ∉ interval L 0 cut}) → Fin q) :=
    Classical.decEq _
  let e := ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 cut)
  let σ₀ : Fin L → Fin q := fun _ ↦ 0
  have hfactors (a : ι) :
      ∃ (A : Matrix ((v : {v : Fin L // v ∈ interval L 0 cut}) → Fin q)
          ((v : {v : Fin L // v ∈ interval L 0 cut}) → Fin q) ℂ)
        (B : Matrix ((v : {v : Fin L // v ∉ interval L 0 cut}) → Fin q)
          ((v : {v : Fin L // v ∉ interval L 0 cut}) → Fin q) ℂ),
        ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) (H a) =
          A ⊗ₖ 1 + 1 ⊗ₖ B := by
    have hone := (hside a).elim
      (fun hs ↦ (hH a).isOneSided_of_subset hs (e σ₀).2)
      (fun hs ↦ (hH a).isOneSided_of_disjoint hs (e σ₀).1)
    rcases hone with ⟨A, hA⟩ | ⟨B, hB⟩
    · refine ⟨A, 0, ?_⟩
      ext p q
      have h := congrArg (fun M ↦ M p q) hA
      simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply,
        Matrix.zero_apply, mul_zero, add_zero] at h ⊢
      split_ifs at h ⊢ <;> exact h
    · refine ⟨0, B, ?_⟩
      ext p q
      have h := congrArg (fun M ↦ M p q) hB
      simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply,
        Matrix.zero_apply, zero_mul, zero_add] at h ⊢
      split_ifs at h ⊢ <;> exact h
  choose HL HR hlocal using hfactors
  let x : Fin L := ⟨cut - 1, by omega⟩
  have hsites : interval L (cut - 1) (cut + 1) ∩ interval L 0 cut = {x} := by
    ext v
    simp only [Finset.mem_inter, mem_interval, Finset.mem_singleton,
      Fin.ext_iff, x]
    omega
  have hTrank : operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) T) ≤ q ^ 2 := by
    simpa only [hsites, Finset.prod_singleton] using
      (hT.operatorSchmidtRank_cutOperator_le (A := interval L 0 cut))
  let φ := Matrix.reindexAlgEquiv ℂ ℂ e
  have hmap (α : E) :
      φ (WordMultiplicity.oneMarkerCoefficient H T t k α.val) =
        WordMultiplicity.oneMarkerCoefficient
          (fun a ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) (H a))
          (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) T) t k α.val :=
    WordMultiplicity.map_oneMarkerCoefficient φ.toRingHom H T t k α.val
  have heq : ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut)
      (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient H T t k α.val) =
      ∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient
        (fun a ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) (H a))
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) T) t k α.val := by
    change φ (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient H T t k α.val) = _
    simp only [map_sum, map_smul, hmap]
  rw [heq]
  simpa only [← pow_mul] using
    Matrix.operatorSchmidtRank_sum_smul_one_marker_counts_le
      (fun a ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) (H a))
      HL HR hlocal
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) T) hTrank t k weight

end TNLean.MPS.AreaLaw

end OneMarkerRank

section WindowFrequencyRank

section

open ManyBody (interval mem_interval)

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
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L)) (u : Fin s) (t k : ℕ) :
    let I := {j : Fin s ⊕ Fin 2 // j ≠ Sum.inl u}
    let E := @Finset.piAntidiag I ℕ (Classical.decEq I) _ _ _ Finset.univ t
    let ordinary := fun j : I ↦ aklvWindowFamily H HL HR j.val
    ∀ weight : E → ℂ, operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 (a + u.val + 1))
        (∑ α : E, weight α •
          WordMultiplicity.oneMarkerCoefficient ordinary (H u) t k α.val)) ≤
      (t + s).choose s * ((t + 2 * k + 1).choose (2 * k + 1) * q ^ (2 * k)) := by
  intro I E ordinary weight
  let : DecidableEq I := Classical.decEq I
  let X : Fin s ⊕ Fin 2 → Finset (Fin L) :=
    Sum.elim (fun j ↦ interval L (a + j.val) (a + j.val + 2))
      ![interval L 0 (a + 1), interval L (a + s) L]
  have hAll (j : Fin s ⊕ Fin 2) : ManyBody.IsSupportedOn (aklvWindowFamily H HL HR j) (X j) := by
    cases j with
    | inl j => exact hH j
    | inr j => fin_cases j <;> assumption
  have hside (j : I) : X j.val ⊆ interval L 0 (a + u.val + 1) ∨
      Disjoint (X j.val) (interval L 0 (a + u.val + 1)) := by
    obtain ⟨j, hne⟩ := j
    cases j with
    | inl j =>
      have hju : j ≠ u := fun h ↦ hne (congrArg Sum.inl h)
      rcases lt_or_gt_of_ne hju with hlt | hgt
      · left
        intro v hv
        change v ∈ interval L (a + j.val) (a + j.val + 2) at hv
        rw [mem_interval] at hv
        rw [mem_interval]
        have hj := Fin.lt_def.mp hlt
        omega
      · right
        apply Finset.disjoint_left.mpr
        intro v hv hcut
        change v ∈ interval L (a + j.val) (a + j.val + 2) at hv
        rw [mem_interval] at hv
        rw [mem_interval] at hcut
        have hj := Fin.lt_def.mp hgt
        omega
    | inr j =>
      fin_cases j
      · left
        intro v hv
        change v ∈ interval L 0 (a + 1) at hv
        rw [mem_interval] at hv
        rw [mem_interval]
        omega
      · right
        apply Finset.disjoint_left.mpr
        intro v hv hcut
        change v ∈ interval L (a + s) L at hv
        rw [mem_interval] at hv
        rw [mem_interval] at hcut
        omega
  have hT : ManyBody.IsSupportedOn (H u)
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

end

section

open ManyBody (interval mem_interval)

open Matrix
open scoped BigOperators symmDiff

namespace TNLean.MPS.AreaLaw

/-- Moving a prefix cut costs at most the square of the Hilbert-space dimension of the
changed sites. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 651--654. -/
theorem operatorSchmidtRank_cutOperator_le_pow_dist_mul {L q : ℕ} (hq : 1 ≤ q)
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (i j : ℕ) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 j) K) ≤
      q ^ (2 * Nat.dist i j) *
        operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 i) K) := by
  have hcard : ((interval L 0 i) ∆ (interval L 0 j)).card ≤ Nat.dist i j := by
    simpa only [Nat.dist_self, Nat.zero_add] using
      (ManyBody.card_interval_symmDiff_le_dist (L := L) 0 i 0 j)
  exact (Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le
    q (interval L 0 i) (interval L 0 j) K).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq (Nat.mul_le_mul_left 2 hcard)))

open Classical in
/-- The fixed-frequency window estimate at any target cut, for the same actual weighted
operator. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 651--662. -/
theorem operatorSchmidtRank_aklv_window_one_marker_target_le {L q a s : ℕ}
    (hq : 1 ≤ q) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L)) (u : Fin s) (t k target : ℕ) :
    let I := {j : Fin s ⊕ Fin 2 // j ≠ Sum.inl u}
    let E := @Finset.piAntidiag I ℕ (Classical.decEq I) _ _ _ Finset.univ t
    let ordinary := fun j : I ↦ aklvWindowFamily H HL HR j.val
    ∀ weight : E → ℂ, operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 target)
        (∑ α : E, weight α •
          WordMultiplicity.oneMarkerCoefficient ordinary (H u) t k α.val)) ≤
      (t + s).choose s * (t + 2 * k + 1).choose (2 * k + 1) *
        q ^ (2 * k + 2 * Nat.dist (a + u.val + 1) target) := by
  intro I E ordinary weight
  have hrank := operatorSchmidtRank_aklv_window_one_marker_le
    hq hspace H hH HL HR hL hR u t k weight
  have hmove := operatorSchmidtRank_cutOperator_le_pow_dist_mul hq
    (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient ordinary (H u) t k α.val)
    (a + u.val + 1) target
  refine (hmove.trans (Nat.mul_le_mul_left _ hrank)).trans_eq ?_
  rw [pow_add]
  ac_rfl

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

open Classical in
/-- An arbitrary weighted slice of the original full-frequency coefficients obeys the
window estimate at any target cut. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--662. -/
theorem operatorSchmidtRank_aklv_full_frequency_slice_target_le {L q a s : ℕ}
    (hq : 1 ≤ q) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L))
    (u : Fin s) (m k target : ℕ) :
    let A := Fin s ⊕ Fin 2
    let F := (@Finset.piAntidiag A ℕ (Classical.decEq A) _ _ _ Finset.univ (m + k)).filter
      (fun β ↦ β (Sum.inl u) = k)
    ∀ weight : (A → ℕ) → ℂ, operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 target)
        (∑ β ∈ F, weight β •
          WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) (m + k) β)) ≤
      (m + s).choose s * (m + 2 * k + 1).choose (2 * k + 1) *
        q ^ (2 * k + 2 * Nat.dist (a + u.val + 1) target) := by
  intro A F weight
  have heq := WordMultiplicity.sum_smul_wordCoefficient_marker_eq
    (aklvWindowFamily H HL HR) (Sum.inl u) m k weight
  change (∑ β ∈ F, weight β •
      WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) (m + k) β) = _ at heq
  rw [heq]
  exact operatorSchmidtRank_aklv_window_one_marker_target_le hq hspace H hH HL HR hL hR
    u m k target (fun α ↦ weight (WordMultiplicity.insertMarkerFrequency (Sum.inl u) k α.val))

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

open Classical in
/-- A power of the actual window Hamiltonian is a sum of low-frequency pieces with
explicit rank bounds at the central cut. AKLV, arXiv:1301.1162v1, Lemma 4.2,
lines 604--662. The source interaction index is `u.val + 1`. -/
theorem exists_aklv_low_frequency_power_decomposition {L q a s : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L)) (ell : ℕ) :
    ∃ Q : Fin s × Fin (ell / s + 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (HL + (∑ j, H j) + HR) ^ ell = ∑ b, Q b ∧
      ∀ b, operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 (a + s / 2)) (Q b)) ≤
        (ell - b.2.val + s).choose s * (ell + b.2.val + 1).choose (2 * b.2.val + 1) *
          q ^ (2 * b.2.val + 2 * Nat.dist (b.1.val + 1) (s / 2)) := by
  let A := Fin s ⊕ Fin 2
  let : DecidableEq A := Classical.decEq A
  let emb : Fin s ↪ A := ⟨Sum.inl, Sum.inl_injective⟩
  let S : Finset A := Finset.univ.map emb
  have hS : S.Nonempty := ⟨Sum.inl ⟨0, hs⟩,
    Finset.mem_map.mpr ⟨⟨0, hs⟩, Finset.mem_univ _, rfl⟩⟩
  have hScard : S.card = s := by simp only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  obtain ⟨pick, _, hpartition⟩ :=
    Fintype.exists_one_window_word_coefficient_partition_of_le
      (R := Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) S hS
  let E := @Finset.piAntidiag A ℕ (Classical.decEq A) _ _ _ Finset.univ ell
  let selected (β : A → ℕ) : A := pick (fun u : S ↦ β u)
  let label (β : A → ℕ) : A × ℕ := (selected β, β (selected β))
  let piece (b : A × ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    ∑ β ∈ E with label β = b,
      WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) ell β
  let bin (u : Fin s) (k : ℕ) := piece (Sum.inl u, k)
  let Q (b : Fin s × Fin (ell / s + 1)) := bin b.1 b.2.val
  refine ⟨Q, ?_, ?_⟩
  · have hpart := hpartition (aklvWindowFamily H HL HR) ell ell (le_refl ell)
    change (∑ j, aklvWindowFamily H HL HR j) ^ ell =
      ∑ b ∈ S.product (Finset.range (ell / S.card + 1)), piece b at hpart
    rw [sum_aklvWindowFamily, hScard] at hpart
    refine hpart.trans ?_
    calc
      _ = ∑ u ∈ S, ∑ k ∈ Finset.range (ell / s + 1), piece (u, k) :=
        Finset.sum_product S (Finset.range (ell / s + 1)) piece
      _ = _ := by
        simp only [S, Finset.sum_map, Function.Embedding.coeFn_mk, emb]
        simp only [Q, bin, Fintype.sum_prod_type, Finset.sum_range]
  · intro b
    have hk : b.2.val ≤ ell :=
      (Nat.le_of_lt_succ b.2.isLt).trans (Nat.div_le_self ell s)
    have hdegree : ell - b.2.val + b.2.val = ell := Nat.sub_add_cancel hk
    let weight (β : A → ℕ) : ℂ := if selected β = Sum.inl b.1 then 1 else 0
    have hbin : Q b =
        ∑ β ∈ E.filter (fun β ↦ β (Sum.inl b.1) = b.2.val),
          weight β • WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) ell β := by
      simp only [Q, bin, piece, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro β _
      by_cases hsel : selected β = Sum.inl b.1
      · simp only [label, hsel, Prod.mk.injEq, true_and, weight, ite_true, one_smul]
      · have hlabel : label β ≠ (Sum.inl b.1, b.2.val) :=
          fun h ↦ hsel (congrArg Prod.fst h)
        simp only [hlabel, ite_false, weight, hsel, zero_smul]
        split_ifs <;> rfl
    have hrank := operatorSchmidtRank_aklv_full_frequency_slice_target_le
      hq hspace H hH HL HR hL hR b.1 (ell - b.2.val) b.2.val (a + s / 2) weight
    change operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 (a + s / 2))
        (∑ β ∈ (@Finset.piAntidiag A ℕ (Classical.decEq A) _ _ _ Finset.univ
          (ell - b.2.val + b.2.val)).filter (fun β ↦ β (Sum.inl b.1) = b.2.val),
          weight β • WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR)
            (ell - b.2.val + b.2.val) β)) ≤ _ at hrank
    rw [hdegree, ← hbin] at hrank
    have hchoose : ell - b.2.val + 2 * b.2.val + 1 = ell + b.2.val + 1 := by omega
    simpa only [hchoose, Nat.add_assoc, Nat.dist_add_add_left] using hrank

/-- The resulting explicit finite-sum rank bound for a power of the physical window
Hamiltonian. AKLV, arXiv:1301.1162v1, Lemma 4.2, before the binomial estimates and
choice of the window width. -/
theorem operatorSchmidtRank_aklv_power_le_sum {L q a s : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L)) (ell : ℕ) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (interval L 0 (a + s / 2)) ((HL + (∑ j, H j) + HR) ^ ell)) ≤
      ∑ b : Fin s × Fin (ell / s + 1),
        (ell - b.2.val + s).choose s * (ell + b.2.val + 1).choose (2 * b.2.val + 1) *
          q ^ (2 * b.2.val + 2 * Nat.dist (b.1.val + 1) (s / 2)) := by
  obtain ⟨Q, hQ, hrank⟩ := exists_aklv_low_frequency_power_decomposition
    hq hs hspace H hH HL HR hL hR ell
  rw [hQ]
  have hcut : ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 (a + s / 2))
      (∑ b, Q b) = ∑ b, ManyBody.cutOperator (X := fun _ ↦ Fin q)
        (interval L 0 (a + s / 2)) (Q b) := by
    ext x y
    simp only [ManyBody.cutOperator, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [hcut]
  exact (operatorSchmidtRank_sum_le Finset.univ _).trans
    (Finset.sum_le_sum fun b _ ↦ hrank b)

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval interval_mono mem_interval)

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- Retaining consecutive middle interactions and summing the omitted terms into the
exterior operators preserves the actual Hamiltonian and physical supports.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 586--603 and 658--663. -/
theorem exists_aklv_subwindow_regrouping {L q a s b m : ℕ} (hsub : b + m ≤ s)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L)) :
    let H' : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ H ⟨b + j.val, by omega⟩
    ∃ HL' HR' : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      ManyBody.IsSupportedOn HL' (interval L 0 (a + b + 1)) ∧
      ManyBody.IsSupportedOn HR' (interval L (a + b + m) L) ∧
      (∀ j, ManyBody.IsSupportedOn (H' j)
        (interval L (a + b + j.val) (a + b + j.val + 2))) ∧
      HL + (∑ j, H j) + HR = HL' + (∑ j, H' j) + HR' := by
  classical
  intro H'
  let left : Finset (Fin s ⊕ Fin 2) := Finset.univ.filter
    (Sum.elim (fun j ↦ j.val < b) (fun t ↦ t.val = 0))
  let right : Finset (Fin s ⊕ Fin 2) := Finset.univ.filter
    (Sum.elim (fun j ↦ b + m ≤ j.val) (fun t ↦ t.val = 1))
  let HL' := ∑ t ∈ left, aklvWindowFamily H HL HR t
  let HR' := ∑ t ∈ right, aklvWindowFamily H HL HR t
  have hleft : ManyBody.IsSupportedOn HL' (interval L 0 (a + b + 1)) := by
    change _ ∈ ManyBody.supportedOperators _ _
    apply sum_mem
    intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    cases t with
    | inl j =>
      apply (hH j).mono
      intro v hv
      rw [mem_interval] at hv ⊢
      change j.val < b at hp
      omega
    | inr t =>
      fin_cases t
      · exact hL.mono (interval_mono (by omega) (by omega))
      · simp only [Sum.elim_inr] at hp
        contradiction
  have hright : ManyBody.IsSupportedOn HR' (interval L (a + b + m) L) := by
    change _ ∈ ManyBody.supportedOperators _ _
    apply sum_mem
    intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    cases t with
    | inl j =>
      apply (hH j).mono
      intro v hv
      rw [mem_interval] at hv ⊢
      change b + m ≤ j.val at hp
      omega
    | inr t =>
      fin_cases t
      · simp only [Sum.elim_inr] at hp
        contradiction
      · exact hR.mono (interval_mono (by omega) le_rfl)
  have hHL' : HL' = HL + ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ j.val < b), H j := by
    simp only [Finset.sum_filter, Fin.val_eq_zero_iff, Fin.isValue, aklvWindowFamily,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two, ↓reduceIte,
      cons_val_zero, one_ne_zero, add_zero, add_comm, add_right_inj, HL', left]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · exact ite_eq_left hj
    · exact ite_eq_right hj
  have hHR' : HR' = HR + ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b + m ≤ j.val), H j := by
    simp only [Finset.sum_filter, aklvWindowFamily, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      zero_ne_one, ↓reduceIte, Nat.mod_succ, cons_val_one, cons_val_fin_one, add_comm,
      add_zero, add_right_inj, HR', right]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · exact ite_eq_left hj
    · exact ite_eq_right hj
  have hmiddle : (∑ j, H' j) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b ≤ j.val ∧ j.val < b + m), H j := by
    refine Finset.sum_bij (fun j _ ↦ (⟨b + j.val, by omega⟩ : Fin s)) ?_ ?_ ?_ ?_
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro i _ j _ hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      change b + i.val = b + j.val at hval
      omega
    · intro j hj
      have hp := (Finset.mem_filter.mp hj).2
      refine ⟨⟨j.val - b, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      change b + (j.val - b) = j.val
      omega
    · intro j _
      rfl
  have hsplit : (∑ j, H j) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ j.val < b), H j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b ≤ j.val ∧ j.val < b + m), H j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b + m ≤ j.val), H j) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all <;> omega
  refine ⟨HL', HR', hleft, hright, ?_, ?_⟩
  · intro j
    simpa only [H', Nat.add_assoc] using hH ⟨b + j.val, by omega⟩
  · rw [hHL', hHR', hmiddle, hsplit]
    abel

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- A polynomial of degree at most `ell` obeys a uniform explicit rank bound when the
physical middle window has width at most `ell + 1`. This is the bounded-window step
in AKLV, arXiv:1301.1162v1, Lemma 4.2, before shorter-window regrouping. -/
theorem operatorSchmidtRank_aklv_polynomial_of_width_le {L q a s ell : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hwidth : s ≤ ell + 1) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, ManyBody.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : ManyBody.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : ManyBody.IsSupportedOn HR (interval L (a + s) L))
    (P : Polynomial ℂ) (hP : P.natDegree ≤ ell) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (interval L 0 (a + s / 2))
      (Polynomial.aeval (HL + (∑ j, H j) + HR) P)) ≤
      (q * (ell + 1)) ^ (3 * s + 6 * (ell / s) + 5) := by
  let G := HL + (∑ j, H j) + HR
  let B := q * (ell + 1)
  let e := 3 * s + 6 * (ell / s) + 4
  have hbase : ell + 1 ≤ B := by dsimp [B]; nlinarith
  have hpower (r : ℕ) (hr : r ≤ ell) :
      operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
        (interval L 0 (a + s / 2)) (G ^ r)) ≤ B ^ e :=
    (operatorSchmidtRank_aklv_power_le_sum hq hs hspace H hH HL HR hL hR r).trans
      (Nat.aklv_frequency_sum_le hq hwidth hr)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ
    (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 (a + s / 2)))
  change operatorSchmidtRank (φ (Polynomial.aeval G P)) ≤ _
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP) G]
  simp only [map_sum, map_smul]
  calc
    _ ≤ ∑ r ∈ Finset.range (ell + 1),
        operatorSchmidtRank (P.coeff r • φ (G ^ r)) :=
      operatorSchmidtRank_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range (ell + 1), B ^ e :=
      Finset.sum_le_sum fun r hr ↦ (operatorSchmidtRank_smul_le _ _).trans
        (hpower r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)))
    _ = (ell + 1) * B ^ e := by simp
    _ ≤ B * B ^ e := Nat.mul_le_mul_right _ hbase
    _ = _ := by rw [← pow_succ']

end TNLean.MPS.AreaLaw

end

end WindowFrequencyRank
