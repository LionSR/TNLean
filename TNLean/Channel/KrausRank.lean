/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Card
import TNLean.Algebra.FinSum
import TNLean.Algebra.MatrixSpectralDecomp
import TNLean.Channel.ChoiRectangular

/-!
# Kraus-cardinality and Choi-rank correspondence

This file states the channel-side formalization relating Kraus families to the
rank of the Choi matrix.

The results are stated for rectangular Kraus operators
`Kⱼ : Matrix (Fin d') (Fin d) ℂ`, i.e. for maps `T : M_d(ℂ) → M_{d'}(ℂ)`
between matrix algebras of possibly different dimensions, using the
rectangular Choi matrix `ChoiRectangular.choiMatrix`; the square development
is the specialization `d = d'` (where `ChoiRectangular.choiMatrix` is
definitionally `ChoiJamiolkowski.choiMatrix`).

## Main definitions

* `Channel.HasKrausCard T r` — `T` has an exact `r`-operator Kraus representation.
* `Channel.HasKrausRankLE T r` — `T` has some Kraus representation with at most
  `r` operators.
* `Channel.choiRank T` — the rank of the Choi matrix of `T`.

## Main results

* `Channel.hasKrausCard_mono` — zero-padding enlarges a Kraus family.
* `Channel.choiMatrix_eq_sum_vecMulVec_of_kraus` — the Choi matrix of a Kraus
  map is a sum of rank-one outer products.
* `Channel.choiRank_le_of_hasKrausCard` — any `r`-operator Kraus family gives
  the upper bound `choiRank T ≤ r`.
* `Channel.choiRank_le_of_hasKrausRankLE` — the same upper bound for bounded
  Kraus-rank witnesses.
* `Channel.hasKrausCard_choiRank_of_cp` — a completely positive map has a Kraus
  family with exactly `choiRank T` operators.
* `Channel.hasKrausRankLE_choiRank_of_cp` /
  `Channel.hasKrausRankLE_choiRank_of_cptp` — the bounded converse witnesses.

## Design note

The converse direction is proved by diagonalizing the positive semidefinite Choi
matrix, discarding the zero-eigenvalue summands, and reconstructing Kraus
operators from the remaining rank-one terms.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset BigOperators

namespace Channel

variable {d d' : ℕ}

/-- A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` has an exact `r`-operator Kraus
representation `T(X) = ∑ⱼ Kⱼ X Kⱼ†` with
`Kⱼ : Matrix (Fin d') (Fin d) ℂ` (Wolf, Theorem 2.1, Equation (2.8)). -/
def HasKrausCard
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) (r : ℕ) :
    Prop :=
  ∃ K : Fin r → Matrix (Fin d') (Fin d) ℂ,
    ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ

/-- A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` admits a Kraus representation with
at most `r` operators. -/
def HasKrausRankLE
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) (r : ℕ) :
    Prop :=
  ∃ s : ℕ, s ≤ r ∧ HasKrausCard T s

/-- The **Kraus rank** (Choi rank) of a linear map between matrix algebras is
the rank of its Choi matrix (Wolf, Theorem 2.1, footnote: `r = rank(τ)`, to
be distinguished from the rank of `T` as a linear map). At `d = d'` this is
definitionally the rank of the square Choi matrix
`ChoiJamiolkowski.choiMatrix`. -/
noncomputable def choiRank
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) : ℕ :=
  (ChoiRectangular.choiMatrix T).rank

/-- If `T` has `r` Kraus operators and `r ≤ s`, then it also has `s` Kraus
operators obtained by zero-padding (Wolf, Theorem 2.1 item 4: "the smaller
set is padded with zeros"). -/
theorem hasKrausCard_mono
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} {r s : ℕ}
    (hT : HasKrausCard T r) (hCard : r ≤ s) :
    HasKrausCard T s := by
  classical
  rcases hT with ⟨K, hK⟩
  refine ⟨fun α => if hlt : α.val < r then K ⟨α.val, hlt⟩ else 0, ?_⟩
  intro X
  rw [hK X, Fin.sum_castLE_extend_zero (f := fun j => K j * X * (K j)ᴴ) hCard]
  refine Finset.sum_congr rfl ?_
  intro α _
  simp only
  split_ifs with hlt
  · rfl
  · simp

/-- Any exact Kraus-cardinality witness yields a bounded one. -/
theorem hasKrausRankLE_of_hasKrausCard
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} {r : ℕ}
    (hT : HasKrausCard T r) : HasKrausRankLE T r :=
  ⟨r, le_rfl, hT⟩

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

/-- The Choi matrix of a Kraus map is a sum of rank-one outer products
(Wolf, Theorem 2.1, proof, Equation (2.9):
`τ = ∑ⱼ |ψⱼ⟩⟨ψⱼ|` with `|ψⱼ⟩ = (Kⱼ ⊗ 𝟙)|Ω⟩`). -/
theorem choiMatrix_eq_sum_vecMulVec_of_kraus {r : ℕ}
    (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    ChoiRectangular.choiMatrix T =
      ∑ j : Fin r,
        Matrix.vecMulVec
          (fun p : Fin d' × Fin d => ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) * K j p.1 p.2)
          (star fun p : Fin d' × Fin d => ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) * K j p.1 p.2) := by
  classical
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [ChoiRectangular.choiMatrix_apply, hT,
    ChoiJamiolkowski.omegaSlice_eq_single (D := d) i₂ j₂,
    Matrix.sum_apply i₁ j₁, Matrix.sum_apply (i₁, i₂) (j₁, j₂)]
  change ∑ x : Fin r,
      (K x * Matrix.single i₂ j₂ (c * star c) * (K x)ᴴ) i₁ j₁ =
    ∑ x : Fin r,
      Matrix.vecMulVec (fun p : Fin d' × Fin d => c * K x p.1 p.2)
        (star (fun p : Fin d' × Fin d => c * K x p.1 p.2)) (i₁, i₂) (j₁, j₂)
  refine Finset.sum_congr rfl ?_
  intro x _
  simpa [Matrix.vecMulVec_apply] using
    congrArg (fun M => M i₁ j₁)
      (Matrix.mul_single_mul_conjTranspose_eq_vecMulVec
        (K := K x) (c := c) i₂ j₂)

/-- A Choi-matrix decomposition into rank-one outer products yields a Kraus
family indexed by the same finite type. -/
private theorem hasKrausCard_of_choiMatrix_eq_sum_vecMulVec [NeZero d]
    {ι : Type*} [Fintype ι]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (v : ι → (Fin d' × Fin d) → ℂ)
    (hchoi : ChoiRectangular.choiMatrix T =
      ∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) :
    HasKrausCard T (Fintype.card ι) := by
  classical
  obtain ⟨K, hK⟩ :=
    ChoiRectangular.exists_kraus_of_choiMatrix_eq_sum_vecMulVec
      (T := T) (ι := ι) v hchoi
  refine ⟨fun α => K ((Fintype.equivFin ι).symm α), ?_⟩
  intro X
  calc
    T X = ∑ m : ι, K m * X * (K m)ᴴ := hK X
    _ = ∑ α : Fin (Fintype.card ι),
          K ((Fintype.equivFin ι).symm α) * X * (K ((Fintype.equivFin ι).symm α))ᴴ := by
            refine Fintype.sum_equiv (Fintype.equivFin ι) _ _ ?_
            intro m
            simp

/-- Any `r`-operator Kraus representation bounds the Kraus rank by `r`
(Wolf, Theorem 2.1, proof: `r ≥ rank(τ)`). -/
theorem choiRank_le_of_hasKrausCard
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} {r : ℕ}
    (hT : HasKrausCard T r) :
    choiRank T ≤ r := by
  rcases hT with ⟨K, hK⟩
  exact rank_le_card_of_eq_sum_vecMulVec _ _
    (choiMatrix_eq_sum_vecMulVec_of_kraus K T hK)

/-- A bounded Kraus-rank witness also bounds the Choi rank. -/
theorem choiRank_le_of_hasKrausRankLE
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} {r : ℕ}
    (hT : HasKrausRankLE T r) :
    choiRank T ≤ r := by
  rcases hT with ⟨s, hs, hT⟩
  exact (choiRank_le_of_hasKrausCard hT).trans hs

/-- A completely positive map admits a Kraus representation whose cardinality is
exactly the rank of its Choi matrix (Wolf, Theorem 2.1, proof: "equality can be
achieved", using the spectral decomposition of `τ ≥ 0`). -/
theorem hasKrausCard_choiRank_of_cp
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    HasKrausCard T (choiRank T) := by
  classical
  by_cases hd : d = 0
  · -- When `d = 0` the input matrix algebra is a subsingleton, so `T` vanishes
    -- on every input and the Kraus family indexed by `Fin 0` is a trivial
    -- witness.
    subst hd
    have hzero : ∀ X : Matrix (Fin 0) (Fin 0) ℂ, X = 0 := fun X => by
      ext i _; exact i.elim0
    have h0 : HasKrausCard T 0 :=
      ⟨Fin.elim0, fun X => by rw [hzero X, map_zero]; simp⟩
    have hrank : choiRank T = 0 :=
      Nat.le_zero.mp (choiRank_le_of_hasKrausCard h0)
    rw [hrank]; exact h0
  · haveI : NeZero d := ⟨hd⟩
    have hτpsd : (ChoiRectangular.choiMatrix T).PosSemidef :=
      (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (T := T)).mp hT
    let hτ : (ChoiRectangular.choiMatrix T).IsHermitian := hτpsd.1
    let v : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} → (Fin d' × Fin d) → ℂ :=
      fun i p => ((Real.sqrt (hτ.eigenvalues i.1) : ℂ)) * hτ.eigenvectorUnitary p i.1
    have hchoi' : ChoiRectangular.choiMatrix T =
        ∑ i : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
          Matrix.vecMulVec (v i) (fun p => star (v i p)) := by
      simpa [hτ, v] using
        Matrix.PosSemidef.eq_sum_vecMulVec_nonzero_eigs
          (A := ChoiRectangular.choiMatrix T) hτpsd
    have hchoi : ChoiRectangular.choiMatrix T =
        ∑ i : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
          Matrix.vecMulVec (v i) (star (v i)) := by
      refine hchoi'.trans ?_
      apply Finset.sum_congr rfl
      intro i _
      congr 1
    have hcard : Fintype.card {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} =
        choiRank T := by
      unfold choiRank
      simpa [hτ] using (hτ.rank_eq_card_non_zero_eigs).symm
    have hK : HasKrausCard T
        (Fintype.card {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0}) :=
      hasKrausCard_of_choiMatrix_eq_sum_vecMulVec
        (T := T) (ι := {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0}) v hchoi
    rwa [hcard] at hK

/-- In particular, a completely positive map has Kraus rank at most its Choi
rank. -/
theorem hasKrausRankLE_choiRank_of_cp
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    HasKrausRankLE T (choiRank T) :=
  hasKrausRankLE_of_hasKrausCard (hasKrausCard_choiRank_of_cp hT)

/-- A CPTP map has Kraus rank at most its Choi rank. -/
theorem hasKrausRankLE_choiRank_of_cptp {D : ℕ}
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE : IsChannel E) :
    HasKrausRankLE E (choiRank E) :=
  hasKrausRankLE_choiRank_of_cp hE.cp

end Channel
