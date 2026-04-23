/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Card
import TNLean.Channel.ChoiJamiolkowski

/-!
# Kraus-cardinality and Choi-rank bounds

This file packages the basic channel-side infrastructure needed for future
minimal-Kraus arguments.

## Main definitions

* `Channel.HasKrausCard E r` — `E` has an exact `r`-operator Kraus representation.
* `Channel.HasKrausRankLE E r` — `E` has some Kraus representation with at most
  `r` operators.
* `Channel.choiRank E` — the rank of the Choi matrix of `E`.

## Main results

* `Channel.hasKrausCard_mono` — zero-padding enlarges a Kraus family.
* `Channel.choiMatrix_eq_sum_vecMulVec_of_kraus` — the Choi matrix of a Kraus
  map is a sum of rank-one outer products.
* `Channel.choiRank_le_of_hasKrausCard` — any `r`-operator Kraus family gives
  the upper bound `choiRank E ≤ r`.
* `Channel.choiRank_le_of_hasKrausRankLE` — the same upper bound for bounded
  Kraus-rank witnesses.

## Design note

This file does **not** yet prove the converse direction
`HasKrausRankLE E (choiRank E)`. That is the genuine minimal-Kraus / Choi-rank
identity still needed for Theorem 4.1 reverse.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset BigOperators

namespace Channel

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A linear map `E : M_D(ℂ) → M_D(ℂ)` has an exact `r`-operator Kraus
representation. -/
def HasKrausCard (E : Mat →ₗ[ℂ] Mat) (r : ℕ) : Prop :=
  ∃ K : Fin r → Mat, ∀ X, E X = ∑ i : Fin r, K i * X * (K i)ᴴ

/-- A linear map `E : M_D(ℂ) → M_D(ℂ)` admits a Kraus representation with at
most `r` operators. -/
def HasKrausRankLE (E : Mat →ₗ[ℂ] Mat) (r : ℕ) : Prop :=
  ∃ s : ℕ, s ≤ r ∧ HasKrausCard E s

/-- The Choi rank of a linear map is the rank of its Choi matrix. -/
noncomputable def choiRank (E : Mat →ₗ[ℂ] Mat) : ℕ :=
  (ChoiJamiolkowski.choiMatrix E).rank

/-- A sum indexed by `Fin r` can be padded by zeros to a larger `Fin s`. -/
private lemma sum_pad_zeros {r s : ℕ} {β : Type*} [AddCommMonoid β]
    (f : Fin r → β) (hCard : r ≤ s) :
    ∑ j : Fin r, f j =
      ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
  symm
  have hsub :
      ∑ α ∈ Finset.univ.filter (fun α : Fin s => α.val < r),
          (if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0) =
        ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro α _ hα
    have : ¬ α.val < r := by
      simpa using hα
    simp [dif_neg this]
  rw [← hsub]
  symm
  apply Finset.sum_nbij (fun j : Fin r => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hCard⟩ : Fin s))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j₁ _ j₂ _ hj
    exact Fin.ext (Fin.mk.inj hj)
  · intro α hα
    have hα' := (Finset.mem_filter.mp (Finset.mem_coe.mp hα)).2
    exact ⟨⟨α.val, hα'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
  · intro j _
    simp [Fin.eta]

/-- If `E` has `r` Kraus operators and `r ≤ s`, then it also has `s` Kraus
operators obtained by zero-padding. -/
theorem hasKrausCard_mono {E : Mat →ₗ[ℂ] Mat} {r s : ℕ}
    (hE : HasKrausCard E r) (hCard : r ≤ s) :
    HasKrausCard E s := by
  classical
  rcases hE with ⟨K, hK⟩
  refine ⟨fun α => if hlt : α.val < r then K ⟨α.val, hlt⟩ else 0, ?_⟩
  intro X
  rw [hK X, sum_pad_zeros (f := fun j => K j * X * (K j)ᴴ) hCard]
  refine Finset.sum_congr rfl ?_
  intro α _
  simp only
  split_ifs with hlt
  · rfl
  · simp

/-- Any exact Kraus-cardinality witness yields a bounded one. -/
theorem hasKrausRankLE_of_hasKrausCard {E : Mat →ₗ[ℂ] Mat} {r : ℕ}
    (hE : HasKrausCard E r) : HasKrausRankLE E r :=
  ⟨r, le_rfl, hE⟩

section RankBounds

variable {n : Type*} [Fintype n]

/-- A sum of `r` rank-one outer products has rank at most `r`. -/
theorem rank_le_card_of_eq_sum_vecMulVec {r : ℕ}
    (M : Matrix n n ℂ) (v : Fin r → n → ℂ)
    (hM : M = ∑ i, Matrix.vecMulVec (v i) (star (v i))) :
    M.rank ≤ r := by
  classical
  rw [hM, Matrix.rank_eq_finrank_span_cols]
  have hcols :
      Submodule.span ℂ
          (Set.range (fun j : n => (∑ i, Matrix.vecMulVec (v i) (star (v i))).col j)) ≤
        Submodule.span ℂ (Set.range v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hcol :
        (∑ i, Matrix.vecMulVec (v i) (star (v i))).col j =
          ∑ i, star (v i j) • v i := by
      ext x
      simp [Matrix.col_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]
    simpa [hcol] using
      (Submodule.sum_mem (Submodule.span ℂ (Set.range v)) fun i _ =>
        Submodule.smul_mem _ _ <| Submodule.subset_span ⟨i, rfl⟩)
  have hfinrank := Submodule.finrank_mono hcols
  have hspan_card :
      Module.finrank ℂ ↥(Submodule.span ℂ (Set.range v)) ≤ (Set.range v).toFinset.card := by
    simpa using (finrank_span_le_card (R := ℂ) (s := Set.range v))
  have hrange_finset : (Set.range v).toFinset = Finset.univ.image v := by
    ext x
    simp
  have hcard_range : (Set.range v).toFinset.card ≤ r := by
    rw [hrange_finset]
    exact (Finset.card_image_le).trans_eq (by simp)
  exact hfinrank.trans (hspan_card.trans hcard_range)

end RankBounds

/-- `K * (c * c̄ · E_{i,j}) * K†` is the rank-one matrix formed from the
`i`-th and `j`-th columns of `K`, scaled by `c`. This duplicates the tiny
file-local helper used inside `ChoiJamiolkowski.lean` so the Choi-rank bounds
here can stay self-contained. -/
private theorem mul_single_mul_conjTranspose_eq_vecMulVec
    (K : Mat) (c : ℂ) (i₂ j₂ : Fin D) :
    K * Matrix.single i₂ j₂ (c * star c) * Kᴴ =
      Matrix.vecMulVec (fun i₁ : Fin D => c * K i₁ i₂)
        (fun j₁ : Fin D => star (c * K j₁ j₂)) := by
  rw [show Matrix.single i₂ j₂ (c * star c) =
      (c * star c) • Matrix.vecMulVec (Pi.single i₂ (1 : ℂ)) (Pi.single j₂ 1) by
    rw [← Matrix.single_eq_single_vecMulVec_single i₂ j₂]
    simp]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  ext i₁ j₁
  simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Matrix.col, Matrix.row]
  ring_nf

/-- The Choi matrix of a Kraus map is a sum of rank-one outer products. -/
theorem choiMatrix_eq_sum_vecMulVec_of_kraus {r : ℕ}
    (K : Fin r → Mat) (E : Mat →ₗ[ℂ] Mat)
    (hE : ∀ X, E X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    ChoiJamiolkowski.choiMatrix E =
      ∑ j : Fin r,
        Matrix.vecMulVec (fun p : Fin D × Fin D => ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * K j p.1 p.2)
          (star (fun p : Fin D × Fin D => ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * K j p.1 p.2)) := by
  classical
  let c : ℂ := (1 : ℂ) / ((D : ℝ).sqrt : ℂ)
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [ChoiJamiolkowski.choiMatrix_apply, hE,
    ChoiJamiolkowski.omegaSlice_eq_single (D := D) i₂ j₂,
    Matrix.sum_apply i₁ j₁, Matrix.sum_apply (i₁, i₂) (j₁, j₂)]
  change ∑ x : Fin r,
      (K x * Matrix.single i₂ j₂ (c * star c) * (K x)ᴴ) i₁ j₁ =
    ∑ x : Fin r,
      Matrix.vecMulVec (fun p : Fin D × Fin D => c * K x p.1 p.2)
        (star (fun p : Fin D × Fin D => c * K x p.1 p.2)) (i₁, i₂) (j₁, j₂)
  refine Finset.sum_congr rfl ?_
  intro x _
  simpa [Matrix.vecMulVec_apply] using
    congrArg (fun M => M i₁ j₁)
      (mul_single_mul_conjTranspose_eq_vecMulVec (K := K x) (c := c) i₂ j₂)

/-- Any `r`-operator Kraus representation bounds the Choi rank by `r`. -/
theorem choiRank_le_of_hasKrausCard {E : Mat →ₗ[ℂ] Mat} {r : ℕ}
    (hE : HasKrausCard E r) :
    choiRank E ≤ r := by
  rcases hE with ⟨K, hK⟩
  unfold choiRank
  exact rank_le_card_of_eq_sum_vecMulVec _ _
    (choiMatrix_eq_sum_vecMulVec_of_kraus K E hK)

/-- A bounded Kraus-rank witness also bounds the Choi rank. -/
theorem choiRank_le_of_hasKrausRankLE {E : Mat →ₗ[ℂ] Mat} {r : ℕ}
    (hE : HasKrausRankLE E r) :
    choiRank E ≤ r := by
  rcases hE with ⟨s, hs, hE⟩
  exact (choiRank_le_of_hasKrausCard hE).trans hs

end Channel
