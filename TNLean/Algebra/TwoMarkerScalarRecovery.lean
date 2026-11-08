/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FiniteMonomialInterpolation
import QICLean.Algebra.TwoMarkerWordCoefficients
import QICLean.Algebra.WordCoefficient
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import QICLean.Algebra.IntegerGridInterpolation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.EquivFin

/-!
# Common scalar recovery of two marked word coefficients

A fixed finite family of complex samples recovers every weighted frequency
slice of an ordered word expansion through a common degree cutoff.
The sample points precede the two frequencies and the scalar mask; the
recovery coefficients precede the operator family and every allowed degree.
The two selected operators remain unweighted.

For two windows and three bulk labels, the ordinary monomial box has exactly
four times the window half-width plus one coordinates. Its cardinality gives
one common finite sample index type for every selected pair. Samples for
different selected pairs need not coincide. No independence of the operator
coefficients is required, and noncommutative products retain their order.

**Local fix (interpolation):** The recovery theorem uses spanning
interpolation; evaluated operator families need not be bases. This is the
finite scalar recovery supplied by QICLean. The source distinction is
recorded at:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf

## References

Supporting interpolation algebra for AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 626–644, and ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333.
-/

open scoped BigOperators

noncomputable section

namespace MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The labels other than the two distinguished letters. -/
def twoMarkerOrdinaryLabels (u v : I) : Finset I :=
  ((Finset.univ : Finset I).erase u).erase v

/-- Retain precisely the ordinary counts, setting both distinguished counts to zero. -/
private noncomputable def twoMarkerResidual (u v : I) (ν : I → ℕ) : I →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun a ↦ if a ∈ twoMarkerOrdinaryLabels u v then ν a else 0)

/-- An ordinary finite-box configuration determines an exponent supported on those labels. -/
private noncomputable def twoMarkerBoxExponent (u v : I) (K : ℕ)
    (p : ↥(twoMarkerOrdinaryLabels u v) → Fin (K + 1)) : I →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun a ↦ if h : a ∈ twoMarkerOrdinaryLabels u v then (p ⟨a, h⟩).val else 0)

/-- The ordinary exponents from zero through K, represented as full-alphabet monomials. -/
private noncomputable def twoMarkerMonomialBox (u v : I) (K : ℕ) : Finset (I →₀ ℕ) := by
  classical
  exact Finset.univ.image (twoMarkerBoxExponent u v K)

/-- Restore the prescribed counts at the two distinguished labels. -/
private def twoMarkerRestore (u v : I) (i j : ℕ) (β : I →₀ ℕ) : I → ℕ :=
  fun a ↦ if a = u then i else if a = v then j else β a

/-- Every ordinary count bounded by K gives an exponent in the same fixed box. -/
private theorem twoMarkerResidual_mem_box (u v : I) (K : ℕ) (ν : I → ℕ)
    (hν : ∀ a ∈ twoMarkerOrdinaryLabels u v, ν a ≤ K) :
    twoMarkerResidual u v ν ∈ twoMarkerMonomialBox u v K := by
  classical
  let p : ↥(twoMarkerOrdinaryLabels u v) → Fin (K + 1) :=
    fun a ↦ ⟨ν a.val, Nat.lt_succ_of_le (hν a.val a.property)⟩
  change twoMarkerResidual u v ν ∈ Finset.univ.image (twoMarkerBoxExponent u v K)
  refine Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩
  ext a
  by_cases ha : a ∈ twoMarkerOrdinaryLabels u v <;>
    simp [twoMarkerBoxExponent, twoMarkerResidual, ha, p]

/-- Every exponent in the box vanishes away from the ordinary labels. -/
private theorem twoMarkerMonomialBox_apply_eq_zero (u v : I) (K : ℕ)
    (β : I →₀ ℕ) (hβ : β ∈ twoMarkerMonomialBox u v K)
    (a : I) (ha : a ∉ twoMarkerOrdinaryLabels u v) : β a = 0 := by
  classical
  change β ∈ Finset.univ.image (twoMarkerBoxExponent u v K) at hβ
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hβ
  simp [twoMarkerBoxExponent, ha]

/-- Restoring a full count function on its prescribed distinguished-frequency slice is exact. -/
private theorem twoMarkerRestore_residual (u v : I) (i j : ℕ) (ν : I → ℕ)
    (hu : ν u = i) (hv : ν v = j) :
    twoMarkerRestore u v i j (twoMarkerResidual u v ν) = ν := by
  funext a
  by_cases hau : a = u
  · subst a
    simp [twoMarkerRestore, hu]
  by_cases hav : a = v
  · subst a
    simp [twoMarkerRestore, hau, hv]
  have ha : a ∈ twoMarkerOrdinaryLabels u v := by
    simp [twoMarkerOrdinaryLabels, hau, hav]
  simp [twoMarkerRestore, twoMarkerResidual, hau, hav, ha]

/-- Restoring any prescribed distinguished counts leaves the ordinary box exponent unchanged. -/
private theorem twoMarkerResidual_restore_of_mem_box (u v : I) (K i j : ℕ)
    (β : I →₀ ℕ) (hβ : β ∈ twoMarkerMonomialBox u v K) :
    twoMarkerResidual u v (twoMarkerRestore u v i j β) = β := by
  classical
  ext a
  by_cases ha : a ∈ twoMarkerOrdinaryLabels u v
  · have hau : a ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    have hav : a ≠ v := (Finset.mem_erase.mp ha).1
    simp [twoMarkerResidual, twoMarkerRestore, ha, hau, hav]
  · have hzero := twoMarkerMonomialBox_apply_eq_zero u v K β hβ a ha
    simp [twoMarkerResidual, ha, hzero]

/-- The ordinary monomial evaluates to the product of the corresponding scalar powers.
This is the residual-monomial identity used in the existing weighted-frequency proof. -/
private theorem eval_monomial_twoMarkerResidual (u v : I) (ν : I → ℕ) (z : I → ℂ) :
    eval z (monomial (twoMarkerResidual u v ν) (1 : ℂ)) =
      ∏ a ∈ twoMarkerOrdinaryLabels u v, z a ^ ν a := by
  classical
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  change (∏ a, z a ^ (if a ∈ twoMarkerOrdinaryLabels u v then ν a else 0)) = _
  calc
    _ = ∏ a, if a ∈ twoMarkerOrdinaryLabels u v then z a ^ ν a else 1 := by
      refine Finset.prod_congr rfl fun a _ha ↦ ?_
      by_cases ha : a ∈ twoMarkerOrdinaryLabels u v <;> simp [ha]
    _ = _ := Finset.prod_ite_mem_eq (twoMarkerOrdinaryLabels u v) (fun a ↦ z a ^ ν a)

end MvPolynomial

namespace MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Each ordinary finite-box coordinate is recovered by evaluating its encoded exponent. -/
private theorem twoMarkerBoxExponent_injective (u v : I) (K : ℕ) :
    Function.Injective (twoMarkerBoxExponent u v K) := by
  intro p q hpq
  funext a
  apply Fin.ext
  have h := congrArg (fun β : I →₀ ℕ ↦ β a.val) hpq
  simpa [twoMarkerBoxExponent, a.property] using h

/-- The fixed box contains exactly one exponent for each ordinary bounded-count vector. -/
private theorem card_twoMarkerMonomialBox (u v : I) (K : ℕ) :
    (twoMarkerMonomialBox u v K).card = (K + 1) ^ (twoMarkerOrdinaryLabels u v).card := by
  classical
  calc
    (twoMarkerMonomialBox u v K).card =
        (Finset.univ : Finset (↥(twoMarkerOrdinaryLabels u v) → Fin (K + 1))).card :=
      Finset.card_image_of_injective _ (twoMarkerBoxExponent_injective u v K)
    _ = (K + 1) ^ (twoMarkerOrdinaryLabels u v).card := by
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- Removing two distinct labels leaves exactly two fewer ordinary coordinates. -/
private theorem card_twoMarkerOrdinaryLabels_add_two (u v : I) (huv : u ≠ v) :
    (twoMarkerOrdinaryLabels u v).card + 2 = Fintype.card I := by
  have hv : v ∈ (Finset.univ : Finset I).erase u := by simp [huv.symm]
  have hlast : (twoMarkerOrdinaryLabels u v).card + 1 =
      ((Finset.univ : Finset I).erase u).card := Finset.card_erase_add_one hv
  calc
    (twoMarkerOrdinaryLabels u v).card + 2 =
        ((twoMarkerOrdinaryLabels u v).card + 1) + 1 := (Nat.add_assoc _ 1 1).symm
    _ = ((Finset.univ : Finset I).erase u).card + 1 := congrArg (fun m : ℕ ↦ m + 1) hlast
    _ = Fintype.card I := by
      simpa only [Finset.card_univ] using
        (Finset.card_erase_add_one (s := (Finset.univ : Finset I))
          (a := u) (Finset.mem_univ u))

end MvPolynomial

namespace MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Evaluating an encoded box exponent at the prescribed integer point is the
corresponding product-grid matrix entry. Cutoff zero, an empty ordinary set,
and coincident distinguished labels are included. Supporting AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 626–644, and ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem eval_twoMarkerBoxExponent_integerGrid (u v : I) (K : ℕ)
    (g alpha : ↥(twoMarkerOrdinaryLabels u v) → Fin (K + 1)) :
    let z : I → ℂ := fun a ↦ if h : a ∈ twoMarkerOrdinaryLabels u v
      then FiniteScalarInterpolation.integerNode K (g ⟨a, h⟩) else 0
    eval z (monomial (twoMarkerBoxExponent u v K alpha) (1 : ℂ)) =
      FiniteScalarInterpolation.integerEvaluationGrid
        ↥(twoMarkerOrdinaryLabels u v) K g alpha := by
  let O := twoMarkerOrdinaryLabels u v
  let z : I → ℂ := fun a ↦ if h : a ∈ O
    then FiniteScalarInterpolation.integerNode K (g ⟨a, h⟩) else 0
  change eval z (monomial (twoMarkerBoxExponent u v K alpha) (1 : ℂ)) =
    FiniteScalarInterpolation.integerEvaluationGrid ↥O K g alpha
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  calc
    (∏ a : I, z a ^ (twoMarkerBoxExponent u v K alpha) a) =
        ∏ a ∈ O, z a ^ (twoMarkerBoxExponent u v K alpha) a := by
      symm
      apply Finset.prod_subset (Finset.subset_univ O)
      intro a _ha haO
      change a ∉ twoMarkerOrdinaryLabels u v at haO
      simp [twoMarkerBoxExponent, haO]
    _ = ∏ a : ↥O, z a.val ^ (twoMarkerBoxExponent u v K alpha) a.val :=
      (Finset.prod_coe_sort O (fun a : I ↦ z a ^ (twoMarkerBoxExponent u v K alpha) a)).symm
    _ = FiniteScalarInterpolation.integerEvaluationGrid ↥O K g alpha := by
      apply Finset.prod_congr rfl
      intro a _ha
      simp [z, twoMarkerBoxExponent, a.property]

end MvPolynomial

namespace MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

open Classical in
/-- The prescribed integer product grid gives scalar recovery on the existing
ordinary monomial box. The sample points and recovery weights depend only on
the alphabet, distinguished labels and cutoff. This includes cutoff zero,
an empty ordinary set and coincident distinguished labels. Supporting AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 626–644, and ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exists_twoMarker_integerGrid_scalar_recovery (u v : I) (K : ℕ) :
    let O := twoMarkerOrdinaryLabels u v
    let S := twoMarkerMonomialBox u v K
    ∃ (eBox : (↥O → Fin (K + 1)) ≃ ↥S) (qGrid : (↥O → Fin (K + 1)) ≃ Fin S.card),
      (∀ alpha : ↥O → Fin (K + 1), (eBox alpha).val = twoMarkerBoxExponent u v K alpha) ∧
      let z : Fin S.card → I → ℂ := fun s a ↦ if h : a ∈ O
        then FiniteScalarInterpolation.integerNode K (qGrid.symm s ⟨a, h⟩) else 0
      let c : ↥S → Fin S.card → ℂ := fun alpha s ↦
        FiniteScalarInterpolation.integerRecoveryGrid ↥O K
          (eBox.symm alpha) (qGrid.symm s)
      ∀ alpha beta : ↥S,
        (∑ s : Fin S.card, c alpha s * eval (z s) (monomial beta.val (1 : ℂ))) =
          if alpha = beta then 1 else 0 := by
  classical
  let O := twoMarkerOrdinaryLabels u v
  let G := ↥O → Fin (K + 1)
  let S := twoMarkerMonomialBox u v K
  have hrange (beta : I →₀ ℕ) :
      beta ∈ Set.range (twoMarkerBoxExponent u v K) ↔ beta ∈ S := by
    simp only [S, twoMarkerMonomialBox, Set.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
  let eBox : G ≃ ↥S :=
    (Equiv.ofInjective (twoMarkerBoxExponent u v K)
      (twoMarkerBoxExponent_injective u v K)).trans
        (Equiv.subtypeEquivRight hrange)
  have heBox (alpha : G) :
      (eBox alpha).val = twoMarkerBoxExponent u v K alpha := rfl
  have hcard : Fintype.card G = S.card := by
    calc
      Fintype.card G = (K + 1) ^ O.card := by
        simp only [G, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      _ = S.card := (card_twoMarkerMonomialBox u v K).symm
  let qGrid : G ≃ Fin S.card := (Fintype.equivFin G).trans (finCongr hcard)
  refine ⟨eBox, qGrid, heBox, ?_⟩
  let z : Fin S.card → I → ℂ := fun s a ↦ if h : a ∈ O
    then FiniteScalarInterpolation.integerNode K (qGrid.symm s ⟨a, h⟩) else 0
  let c : ↥S → Fin S.card → ℂ := fun alpha s ↦
    FiniteScalarInterpolation.integerRecoveryGrid ↥O K
      (eBox.symm alpha) (qGrid.symm s)
  change ∀ alpha beta : ↥S,
    (∑ s : Fin S.card, c alpha s * eval (z s) (monomial beta.val (1 : ℂ))) =
      if alpha = beta then 1 else 0
  intro alpha beta
  have hbeta : twoMarkerBoxExponent u v K (eBox.symm beta) = beta.val :=
    (heBox (eBox.symm beta)).symm.trans
      (congrArg Subtype.val (eBox.apply_symm_apply beta))
  have heval (g : G) :
      eval (fun a ↦ if h : a ∈ O
        then FiniteScalarInterpolation.integerNode K (g ⟨a, h⟩) else 0)
        (monomial beta.val (1 : ℂ)) =
      FiniteScalarInterpolation.integerEvaluationGrid ↥O K g (eBox.symm beta) := by
    rw [← hbeta]
    exact eval_twoMarkerBoxExponent_integerGrid u v K g (eBox.symm beta)
  have hgrid :
      (∑ g : G, FiniteScalarInterpolation.integerRecoveryGrid ↥O K
        (eBox.symm alpha) g *
        FiniteScalarInterpolation.integerEvaluationGrid ↥O K g (eBox.symm beta)) =
      if alpha = beta then 1 else 0 := by
    have h := congrArg (fun A : Matrix G G ℂ ↦ A (eBox.symm alpha) (eBox.symm beta))
      (FiniteScalarInterpolation.integerRecoveryGrid_mul_integerEvaluationGrid ↥O K)
    have hEq : (fun a b : ↥O ↦ Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq ↥O) := Subsingleton.elim _ _
    rw [hEq] at h
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    by_cases hab : alpha = beta
    · subst beta
      simpa only [ite_eq_left rfl] using h
    · have hne : eBox.symm alpha ≠ eBox.symm beta :=
        fun hsame ↦ hab (eBox.symm.injective hsame)
      simpa only [ite_eq_right hne, ite_eq_right hab] using h
  calc
    (∑ s : Fin S.card, c alpha s * eval (z s) (monomial beta.val (1 : ℂ))) =
        ∑ g : G, FiniteScalarInterpolation.integerRecoveryGrid ↥O K
          (eBox.symm alpha) g *
          eval (fun a ↦ if h : a ∈ O
            then FiniteScalarInterpolation.integerNode K (g ⟨a, h⟩) else 0)
            (monomial beta.val (1 : ℂ)) :=
      qGrid.symm.sum_comp (fun g : G ↦
        FiniteScalarInterpolation.integerRecoveryGrid ↥O K (eBox.symm alpha) g *
          eval (fun a ↦ if h : a ∈ O
            then FiniteScalarInterpolation.integerNode K (g ⟨a, h⟩) else 0)
            (monomial beta.val (1 : ℂ)))
    _ = ∑ g : G, FiniteScalarInterpolation.integerRecoveryGrid ↥O K
        (eBox.symm alpha) g *
        FiniteScalarInterpolation.integerEvaluationGrid ↥O K g (eBox.symm beta) := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact congrArg (fun w : ℂ ↦
        FiniteScalarInterpolation.integerRecoveryGrid ↥O K (eBox.symm alpha) g * w)
        (heval g)
    _ = if alpha = beta then 1 else 0 := hgrid

end MvPolynomial

namespace MvPolynomial

/-- A fixed distinguished-frequency slice is the ordinary monomial box with
zero coefficients outside that slice. This is a finite-sum identity for an
arbitrary additive coefficient function, independent of ordered words.
Supporting finite interpolation in AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 626–644, and ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem sum_twoMarker_slice_eq_box_zero_extension
    {I M : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid M]
    (u v : I) (K r i j : ℕ) (hr : r ≤ K) (F : (I → ℕ) → M) :
    let T := (Finset.piAntidiag (Finset.univ : Finset I) r).filter
      (fun ν ↦ ν u = i ∧ ν v = j)
    (∑ ν ∈ T, F ν) =
      ∑ β : ↥(twoMarkerMonomialBox u v K),
        if twoMarkerRestore u v i j (β : I →₀ ℕ) ∈ T
        then F (twoMarkerRestore u v i j (β : I →₀ ℕ)) else 0 := by
  classical
  let T := (Finset.piAntidiag (Finset.univ : Finset I) r).filter
    (fun ν ↦ ν u = i ∧ ν v = j)
  let B := twoMarkerMonomialBox u v K
  let B' := B.filter (fun β ↦ twoMarkerRestore u v i j β ∈ T)
  change (∑ ν ∈ T, F ν) =
    ∑ β : ↥B, if twoMarkerRestore u v i j (β : I →₀ ℕ) ∈ T
      then F (twoMarkerRestore u v i j (β : I →₀ ℕ)) else 0
  have hbox (ν : I → ℕ) (hν : ν ∈ T) : twoMarkerResidual u v ν ∈ B := by
    apply twoMarkerResidual_mem_box u v K ν
    intro a _ha
    have hsum : (∑ b : I, ν b) = r :=
      (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hν).1).1
    have hle : ν a ≤ ∑ b : I, ν b :=
      Finset.single_le_sum (fun b _ ↦ Nat.zero_le (ν b)) (Finset.mem_univ a)
    exact (hle.trans hsum.le).trans hr
  have hrestore (ν : I → ℕ) (hν : ν ∈ T) :
      twoMarkerRestore u v i j (twoMarkerResidual u v ν) = ν :=
    twoMarkerRestore_residual u v i j ν
      (Finset.mem_filter.mp hν).2.1 (Finset.mem_filter.mp hν).2.2
  have hsum : (∑ ν ∈ T, F ν) =
      ∑ β ∈ B', F (twoMarkerRestore u v i j β) := by
    refine Finset.sum_bij' (fun ν _ ↦ twoMarkerResidual u v ν)
      (fun β _ ↦ twoMarkerRestore u v i j β) ?_ ?_ ?_ ?_ ?_
    · intro ν hν
      refine Finset.mem_filter.mpr ⟨hbox ν hν, ?_⟩
      simpa only [hrestore ν hν] using hν
    · intro β hβ
      exact (Finset.mem_filter.mp hβ).2
    · intro ν hν
      exact hrestore ν hν
    · intro β hβ
      exact twoMarkerResidual_restore_of_mem_box u v K i j β
        (Finset.mem_filter.mp hβ).1
    · intro ν hν
      rw [hrestore ν hν]
  calc
    (∑ ν ∈ T, F ν) = ∑ β ∈ B', F (twoMarkerRestore u v i j β) := hsum
    _ = ∑ β : ↥B, if twoMarkerRestore u v i j (β : I →₀ ℕ) ∈ T
        then F (twoMarkerRestore u v i j (β : I →₀ ℕ)) else 0 := by
      dsimp only [B']
      rw [Finset.sum_filter]
      exact (Finset.sum_coe_sort B (fun β : I →₀ ℕ ↦
        if twoMarkerRestore u v i j β ∈ T
        then F (twoMarkerRestore u v i j β) else 0)).symm

/-- One set of scalar samples recovers every masked distinguished-frequency
slice at every degree up to a common cutoff. The samples precede both
frequencies and every mask; the recovery weights precede all coefficient
functions and all degrees. This is finite scalar recovery, not an ordered-word,
MPO, rank, or algorithmic assertion. Supporting AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 626–644, and ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. -/
private theorem exists_uniform_twoMarker_masked_slice_recovery
    {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
    (u v : I) (K : ℕ) :
    ∃ z : Fin (twoMarkerMonomialBox u v K).card → (I → ℂ),
      ∀ i j : ℕ, ∀ μ : (I → ℕ) → ℂ,
        ∃ gamma : Fin (twoMarkerMonomialBox u v K).card → ℂ,
          ∀ C : (I → ℕ) → M, ∀ r : ℕ, r ≤ K →
            (∑ ν ∈ (Finset.piAntidiag (Finset.univ : Finset I) r).filter
                (fun ν ↦ ν u = i ∧ ν v = j), μ ν • C ν) =
              ∑ s : Fin (twoMarkerMonomialBox u v K).card, gamma s •
                (∑ ν ∈ (Finset.piAntidiag (Finset.univ : Finset I) r).filter
                    (fun ν ↦ ν u = i ∧ ν v = j),
                  (∏ a ∈ twoMarkerOrdinaryLabels u v, z s a ^ ν a) • C ν) := by
  classical
  let O := twoMarkerOrdinaryLabels u v
  let B := twoMarkerMonomialBox u v K
  obtain ⟨eBox, qGrid, _heBox, hscalar⟩ :=
    exists_twoMarker_integerGrid_scalar_recovery u v K
  let z : Fin B.card → I → ℂ := fun s a ↦ if h : a ∈ O
    then FiniteScalarInterpolation.integerNode K (qGrid.symm s ⟨a, h⟩) else 0
  let c : ↥B → Fin B.card → ℂ := fun alpha s ↦
    FiniteScalarInterpolation.integerRecoveryGrid ↥O K
      (eBox.symm alpha) (qGrid.symm s)
  refine ⟨z, ?_⟩
  intro i j μ
  let gamma : Fin B.card → ℂ := fun s ↦
    ∑ β : ↥B, μ (twoMarkerRestore u v i j β) * c β s
  refine ⟨gamma, ?_⟩
  intro C r hr
  let T := (Finset.piAntidiag (Finset.univ : Finset I) r).filter
    (fun ν ↦ ν u = i ∧ ν v = j)
  let f : ↥B → M := fun β ↦
    if twoMarkerRestore u v i j (β : I →₀ ℕ) ∈ T
    then C (twoMarkerRestore u v i j (β : I →₀ ℕ)) else 0
  have hmask : (∑ ν ∈ T, μ ν • C ν) =
      ∑ β : ↥B, μ (twoMarkerRestore u v i j β) • f β := by
    have h := sum_twoMarker_slice_eq_box_zero_extension u v K r i j hr
      (fun ν ↦ μ ν • C ν)
    simpa only [f, smul_ite, smul_zero] using h
  have heval (w : I → ℂ) :
      (∑ β : ↥B, eval w (monomial (β : I →₀ ℕ) (1 : ℂ)) • f β) =
        ∑ ν ∈ T, (∏ a ∈ twoMarkerOrdinaryLabels u v, w a ^ ν a) • C ν := by
    symm
    calc
      (∑ ν ∈ T, (∏ a ∈ twoMarkerOrdinaryLabels u v, w a ^ ν a) • C ν) =
          ∑ ν ∈ T, eval w (monomial (twoMarkerResidual u v ν) (1 : ℂ)) • C ν := by
        simp_rw [eval_monomial_twoMarkerResidual]
      _ = ∑ β : ↥B,
          if twoMarkerRestore u v i j (β : I →₀ ℕ) ∈ T
          then eval w (monomial
            (twoMarkerResidual u v (twoMarkerRestore u v i j (β : I →₀ ℕ)))
            (1 : ℂ)) • C (twoMarkerRestore u v i j (β : I →₀ ℕ)) else 0 :=
        sum_twoMarker_slice_eq_box_zero_extension u v K r i j hr
          (fun ν ↦ eval w (monomial (twoMarkerResidual u v ν) (1 : ℂ)) • C ν)
      _ = ∑ β : ↥B, eval w (monomial (β : I →₀ ℕ) (1 : ℂ)) • f β := by
        apply Finset.sum_congr rfl
        intro β _hβ
        rw [twoMarkerResidual_restore_of_mem_box u v K i j β β.property]
        simp only [f, smul_ite, smul_zero]
  change (∑ ν ∈ T, μ ν • C ν) =
    ∑ s : Fin B.card, gamma s •
      (∑ ν ∈ T, (∏ a ∈ twoMarkerOrdinaryLabels u v, z s a ^ ν a) • C ν)
  calc
    (∑ ν ∈ T, μ ν • C ν) =
        ∑ β : ↥B, μ (twoMarkerRestore u v i j β) • f β := hmask
    _ = ∑ s : Fin B.card, gamma s •
        (∑ β : ↥B, eval (z s) (monomial (β : I →₀ ℕ) (1 : ℂ)) • f β) := by
      exact weighted_monomial_evaluation_recovery_smul B z c
        (fun alpha beta ↦ by
          have h := hscalar alpha beta
          by_cases hab : alpha = beta
          · simpa only [ite_eq_left hab] using h
          · simpa only [ite_eq_right hab] using h)
        (fun β : ↥B ↦ μ (twoMarkerRestore u v i j β)) f
    _ = ∑ s : Fin B.card, gamma s •
        (∑ ν ∈ T, (∏ a ∈ twoMarkerOrdinaryLabels u v, z s a ^ ν a) • C ν) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [heval (z s)]

end MvPolynomial

namespace Polynomial

open Classical in
/-- A fixed set of scalar samples recovers every weighted full-frequency
slice from the actual two distinguished polynomial coefficients. The
selected operator terms are unweighted. Samples precede both frequencies
and every scalar weight, while recovery coefficients precede the operator
family and every degree up to the cutoff. No products of operators are
reordered. This combines finite monomial recovery with the counted-word
identity used in ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exists_twoMarker_wordCoefficient_recovery
    {I R : Type*} [Fintype I] [DecidableEq I] [Ring R] [Algebra ℂ R]
    (u v : I) (huv : u ≠ v) (K : ℕ) :
    ∃ z : Fin (MvPolynomial.twoMarkerMonomialBox u v K).card → (I → ℂ),
      ∀ i j : ℕ, ∀ μ : (I → ℕ) → ℂ,
        ∃ gamma : Fin (MvPolynomial.twoMarkerMonomialBox u v K).card → ℂ,
          ∀ H : I → R, ∀ r : ℕ, r ≤ K →
            (∑ ν ∈ (Finset.piAntidiag (Finset.univ : Finset I) r).filter
                (fun ν ↦ ν u = i ∧ ν v = j),
              μ ν • WordMultiplicity.wordCoefficient H r ν) =
              ∑ s : Fin (MvPolynomial.twoMarkerMonomialBox u v K).card, gamma s •
                (let D : R := ∑ a ∈ MvPolynomial.twoMarkerOrdinaryLabels u v,
                    z s a • H a;
                  let F : Polynomial (Polynomial R) :=
                    C (C D + C (H v) * X) + C (C (H u)) * X;
                  ((F ^ r).coeff i).coeff j) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq I) (Classical.decEq I)
  obtain ⟨z, hz⟩ := MvPolynomial.exists_uniform_twoMarker_masked_slice_recovery
    (M := R) u v K
  refine ⟨z, ?_⟩
  intro i j μ
  obtain ⟨gamma, hgamma⟩ := hz i j μ
  refine ⟨gamma, ?_⟩
  intro H r hr
  have h := hgamma (WordMultiplicity.wordCoefficient H r) r hr
  have hcoeff (s : Fin (MvPolynomial.twoMarkerMonomialBox u v K).card) :
      (∑ ν ∈ (Finset.piAntidiag (Finset.univ : Finset I) r).filter
          (fun ν ↦ ν u = i ∧ ν v = j),
        (∏ a ∈ MvPolynomial.twoMarkerOrdinaryLabels u v, z s a ^ ν a) •
          WordMultiplicity.wordCoefficient H r ν) =
        (let D : R := ∑ a ∈ MvPolynomial.twoMarkerOrdinaryLabels u v,
            z s a • H a;
          let F : Polynomial (Polynomial R) :=
            C (C D + C (H v) * X) + C (C (H u)) * X;
          ((F ^ r).coeff i).coeff j) := by
    symm
    simpa only [MvPolynomial.twoMarkerOrdinaryLabels, WordMultiplicity.wordCoefficient] using
      coeff_coeff_pow_two_markers_eq_sum_full_counts H u v huv (z s) r i j
  simpa only [hcoeff] using h

end Polynomial

namespace MvPolynomial

open Classical in
/-- Removing the selected left and right labels leaves four times ell plus one labels. -/
private theorem card_twoMarkerOrdinaryLabels_twoWindow {ell : ℕ} (p s : Fin (2 * ell)) :
    (twoMarkerOrdinaryLabels
      (I := (Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3)
      (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inr s))).card = 4 * ell + 1 := by
  have h := card_twoMarkerOrdinaryLabels_add_two
    (I := (Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3)
    (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inr s)) (by simp)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

open Classical in
/-- The actual ordinary monomial box has the same cardinality for every selected pair. -/
private theorem card_twoMarkerMonomialBox_twoWindow {ell : ℕ} (p s : Fin (2 * ell))
    (K : ℕ) :
    (twoMarkerMonomialBox
      (I := (Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3)
      (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inr s)) K).card = (K + 1) ^ (4 * ell + 1) := by
  rw [card_twoMarkerMonomialBox, card_twoMarkerOrdinaryLabels_twoWindow]

end MvPolynomial

namespace Polynomial

open Classical in
/-- For every selected left and right label, the scalar recovery samples have
the same finite index type. The exact box cardinality gives the reindexing;
no additional samples are introduced. Points for different selected pairs
need not agree. Selected operators remain unweighted, and the recovery
weights precede the operator family and every degree up to the cutoff.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem exists_twoWindow_wordCoefficient_recovery
    {ell : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (p s : Fin (2 * ell)) (K : ℕ) :
    let I := (Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3
    let u : I := Sum.inl (Sum.inl p)
    let v : I := Sum.inl (Sum.inr s)
    ∃ z : Fin ((K + 1) ^ (4 * ell + 1)) → (I → ℂ),
      ∀ i j : ℕ, ∀ μ : (I → ℕ) → ℂ,
        ∃ gamma : Fin ((K + 1) ^ (4 * ell + 1)) → ℂ,
          ∀ H : I → R, ∀ r : ℕ, r ≤ K →
            (∑ ν ∈ (Finset.piAntidiag (Finset.univ : Finset I) r).filter
                (fun ν ↦ ν u = i ∧ ν v = j),
              μ ν • WordMultiplicity.wordCoefficient H r ν) =
              ∑ t : Fin ((K + 1) ^ (4 * ell + 1)), gamma t •
                (let D : R := ∑ a ∈ MvPolynomial.twoMarkerOrdinaryLabels u v,
                    z t a • H a;
                  let F : Polynomial (Polynomial R) :=
                    C (C D + C (H v) * X) + C (C (H u)) * X;
                  ((F ^ r).coeff i).coeff j) := by
  classical
  intro I u v
  have huv : u ≠ v := by
    intro h
    have h' : (Sum.inl p : Fin (2 * ell) ⊕ Fin (2 * ell)) = Sum.inr s := Sum.inl.inj h
    cases h'
  obtain ⟨z, hz⟩ := exists_twoMarker_wordCoefficient_recovery (R := R) u v huv K
  have hcard : (MvPolynomial.twoMarkerMonomialBox u v K).card =
      (K + 1) ^ (4 * ell + 1) :=
    MvPolynomial.card_twoMarkerMonomialBox_twoWindow p s K
  let e : Fin (MvPolynomial.twoMarkerMonomialBox u v K).card ≃
      Fin ((K + 1) ^ (4 * ell + 1)) := finCongr hcard
  refine ⟨fun t ↦ z (e.symm t), ?_⟩
  intro i j μ
  obtain ⟨gamma, hgamma⟩ := hz i j μ
  refine ⟨fun t ↦ gamma (e.symm t), ?_⟩
  intro H r hr
  have hsum := e.symm.sum_comp
    (fun t : Fin (MvPolynomial.twoMarkerMonomialBox u v K).card ↦ gamma t •
      (let D : R := ∑ a ∈ MvPolynomial.twoMarkerOrdinaryLabels u v, z t a • H a;
        let F : Polynomial (Polynomial R) :=
          C (C D + C (H v) * X) + C (C (H u)) * X;
        ((F ^ r).coeff i).coeff j))
  exact (hgamma H r hr).trans hsum.symm

end Polynomial

end
