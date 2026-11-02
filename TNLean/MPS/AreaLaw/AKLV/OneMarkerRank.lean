/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.OpenMPS
import QICLean.Algebra.OneMarkerWeightedSchmidtRank
import QICLean.Entropy.SupportedOperatorSchmidtRank
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The one-marker frequency rank estimate from actual chain supports

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
    (X : ι → Finset (Fin L)) (hH : ∀ a, Entropy.IsSupportedOn (H a) (X a))
    (hside : ∀ a, X a ⊆ leftBlock L cut ∨ Disjoint (X a) (leftBlock L cut))
    (T : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hT : Entropy.IsSupportedOn T (interval L (cut - 1) (cut + 1))) (t k : ℕ) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) t
    ∀ weight : E → ℂ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut)
        (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient H T t k α.val)) ≤
      E.card * ((t + 2 * k + 1).choose (2 * k + 1) * q ^ (2 * k)) := by
  classical
  let : NeZero q := ⟨by omega⟩
  intro E weight
  let : DecidableEq ((v : {v : Fin L // v ∈ leftBlock L cut}) → Fin q) :=
    Classical.decEq _
  let : DecidableEq ((v : {v : Fin L // v ∉ leftBlock L cut}) → Fin q) :=
    Classical.decEq _
  let e := Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L cut)
  let σ₀ : Fin L → Fin q := fun _ ↦ 0
  have hfactors (a : ι) :
      ∃ (A : Matrix ((v : {v : Fin L // v ∈ leftBlock L cut}) → Fin q)
          ((v : {v : Fin L // v ∈ leftBlock L cut}) → Fin q) ℂ)
        (B : Matrix ((v : {v : Fin L // v ∉ leftBlock L cut}) → Fin q)
          ((v : {v : Fin L // v ∉ leftBlock L cut}) → Fin q) ℂ),
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (H a) =
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
  have hsites : interval L (cut - 1) (cut + 1) ∩ leftBlock L cut = {x} := by
    ext v
    simp only [Finset.mem_inter, mem_interval, mem_leftBlock, Finset.mem_singleton,
      Fin.ext_iff, x]
    omega
  have hTrank : operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) T) ≤ q ^ 2 := by
    simpa only [hsites, Finset.prod_singleton] using
      (hT.operatorSchmidtRank_cutOperator_le (A := leftBlock L cut))
  let φ := Matrix.reindexAlgEquiv ℂ ℂ e
  have hmap (α : E) :
      φ (WordMultiplicity.oneMarkerCoefficient H T t k α.val) =
        WordMultiplicity.oneMarkerCoefficient
          (fun a ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (H a))
          (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) T) t k α.val :=
    WordMultiplicity.map_oneMarkerCoefficient φ.toRingHom H T t k α.val
  have heq : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut)
      (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient H T t k α.val) =
      ∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient
        (fun a ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (H a))
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) T) t k α.val := by
    change φ (∑ α : E, weight α • WordMultiplicity.oneMarkerCoefficient H T t k α.val) = _
    simp only [map_sum, map_smul, hmap]
  rw [heq]
  simpa only [← pow_mul] using
    Matrix.operatorSchmidtRank_sum_smul_one_marker_counts_le
      (fun a ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (H a))
      HL HR hlocal
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) T) hTrank t k weight

end TNLean.MPS.AreaLaw
