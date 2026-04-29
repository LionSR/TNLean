/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Card
import TNLean.Algebra.MatrixSpectralDecomp
import TNLean.Channel.ChoiJamiolkowski

/-!
# Kraus-cardinality and Choi-rank correspondence

This file packages the quantum-channel infrastructure relating Kraus families
to the rank of the Choi matrix.

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
* `Channel.hasKrausCard_choiRank_of_cp` — a completely positive map has a Kraus
  family with exactly `choiRank E` operators.
* `Channel.hasKrausRankLE_choiRank_of_cp` /
  `Channel.hasKrausRankLE_choiRank_of_cptp` — the bounded converse witnesses.

## Design note

The converse direction is proved by diagonalizing the positive semidefinite Choi
matrix, discarding the terms with zero eigenvalue, and reconstructing Kraus
operators from the remaining rank-one terms.
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
      (Matrix.mul_single_mul_conjTranspose_eq_vecMulVec
        (K := K x) (c := c) i₂ j₂)

/-- A Choi-matrix decomposition into rank-one outer products yields a Kraus
family indexed by the same finite type. -/
private theorem hasKrausCard_of_choiMatrix_eq_sum_vecMulVec [NeZero D]
    {ι : Type*} [Fintype ι] {E : Mat →ₗ[ℂ] Mat}
    (v : ι → (Fin D × Fin D) → ℂ)
    (hchoi : ChoiJamiolkowski.choiMatrix E =
      ∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) :
    HasKrausCard E (Fintype.card ι) := by
  classical
  obtain ⟨K, hK⟩ :=
    ChoiJamiolkowski.exists_kraus_of_choiMatrix_eq_sum_vecMulVec
      (T := E) (ι := ι) v hchoi
  refine ⟨fun α => K ((Fintype.equivFin ι).symm α), ?_⟩
  intro X
  calc
    E X = ∑ m : ι, K m * X * (K m)ᴴ := hK X
    _ = ∑ α : Fin (Fintype.card ι),
          K ((Fintype.equivFin ι).symm α) * X * (K ((Fintype.equivFin ι).symm α))ᴴ := by
            refine Fintype.sum_equiv (Fintype.equivFin ι) _ _ ?_
            intro m
            simp

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

/-- A completely positive map admits a Kraus representation whose cardinality is
exactly the rank of its Choi matrix. -/
theorem hasKrausCard_choiRank_of_cp {E : Mat →ₗ[ℂ] Mat}
    (hE : IsCPMap E) :
    HasKrausCard E (choiRank E) := by
  classical
  by_cases hD : D = 0
  · -- When `D = 0` the ambient matrix algebra is a subsingleton, so `E = 0`
    -- and the Kraus family indexed by `Fin 0` is a trivial witness.
    subst hD
    have hzero : ∀ X : Matrix (Fin 0) (Fin 0) ℂ, X = 0 := fun X => by
      ext i _; exact i.elim0
    have h0 : HasKrausCard E 0 :=
      ⟨Fin.elim0, fun X => by rw [hzero X, map_zero]; simp⟩
    have hrank : choiRank E = 0 :=
      Nat.le_zero.mp (choiRank_le_of_hasKrausCard h0)
    rw [hrank]; exact h0
  · haveI : NeZero D := ⟨hD⟩
    have hτpsd : (ChoiJamiolkowski.choiMatrix E).PosSemidef :=
      (ChoiJamiolkowski.cp_iff_choi_posSemidef (T := E)).mp hE
    let hτ : (ChoiJamiolkowski.choiMatrix E).IsHermitian := hτpsd.1
    let v : {j : Fin D × Fin D // hτ.eigenvalues j ≠ 0} → (Fin D × Fin D) → ℂ :=
      fun i p => ((Real.sqrt (hτ.eigenvalues i.1) : ℂ)) * hτ.eigenvectorUnitary p i.1
    have hchoi' : ChoiJamiolkowski.choiMatrix E =
        ∑ i : {j : Fin D × Fin D // hτ.eigenvalues j ≠ 0},
          Matrix.vecMulVec (v i) (fun p => star (v i p)) := by
      simpa [hτ, v] using
        Matrix.PosSemidef.eq_sum_vecMulVec_nonzero_eigs
          (A := ChoiJamiolkowski.choiMatrix E) hτpsd
    have hchoi : ChoiJamiolkowski.choiMatrix E =
        ∑ i : {j : Fin D × Fin D // hτ.eigenvalues j ≠ 0},
          Matrix.vecMulVec (v i) (star (v i)) := by
      simpa using hchoi'
    have hcard : Fintype.card {j : Fin D × Fin D // hτ.eigenvalues j ≠ 0} = choiRank E := by
      unfold choiRank
      simpa [hτ] using (hτ.rank_eq_card_non_zero_eigs).symm
    have hK : HasKrausCard E (Fintype.card {j : Fin D × Fin D // hτ.eigenvalues j ≠ 0}) :=
      hasKrausCard_of_choiMatrix_eq_sum_vecMulVec
        (E := E) (ι := {j : Fin D × Fin D // hτ.eigenvalues j ≠ 0}) v hchoi
    rwa [hcard] at hK

/-- In particular, a completely positive map has Kraus rank at most its Choi
rank. -/
theorem hasKrausRankLE_choiRank_of_cp {E : Mat →ₗ[ℂ] Mat}
    (hE : IsCPMap E) :
    HasKrausRankLE E (choiRank E) :=
  hasKrausRankLE_of_hasKrausCard (hasKrausCard_choiRank_of_cp hE)

/-- A CPTP map has Kraus rank at most its Choi rank. -/
theorem hasKrausRankLE_choiRank_of_cptp {E : Mat →ₗ[ℂ] Mat}
    (hE : IsChannel E) :
    HasKrausRankLE E (choiRank E) :=
  hasKrausRankLE_choiRank_of_cp hE.cp

end Channel
