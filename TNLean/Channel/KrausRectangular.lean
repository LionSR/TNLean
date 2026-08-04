/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.ChoiRectangular
import TNLean.Channel.KrausRank
import TNLean.Channel.KrausRepresentation
import TNLean.Algebra.MatrixGramUnitary
import TNLean.Algebra.FinSum

/-!
# Rectangular Kraus representation theorem

This file proves the rectangular (different-dimension) form of Wolf Chapter 2,
Theorem 2.1 (Kraus representation), `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 229–273: for a linear map `T : M_d(ℂ) → M_{d'}(ℂ)`,

* **existence**: `T` is completely positive iff it admits a Kraus
  representation `T(A) = Σⱼ Kⱼ A Kⱼ†` with `Kⱼ : d' × d` (this is the
  complete-positivity clause `ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef`);
* **normalization** (`kraus_tp_iff_sum_conjTranspose_mul`,
  `kraus_unital_iff_sum_mul_conjTranspose`): `T` is trace preserving iff
  `Σⱼ Kⱼ†Kⱼ = 𝟙`, and unital iff `Σⱼ KⱼKⱼ† = 𝟙`;
* **Kraus rank** (`choiRank_isLeast_hasKrausCard_of_isKrausCP`,
  `choiRank_le_mul`): the minimal number of Kraus operators is
  `r = rank(τ) ≤ d·d'`, where `τ` is the Choi matrix;
* **orthogonality** (`exists_kraus_orthogonal_of_isKrausCP`): there is a
  representation with `r = rank(τ)` Hilbert–Schmidt orthogonal Kraus
  operators (`tr[Kᵢ†Kⱼ] ∝ δᵢⱼ`);
* **freedom** (`kraus_isometry_freedom_iff`, `kraus_unitary_freedom_iff`):
  two Kraus families represent the same map iff they are related by a unitary
  after padding the smaller family with zeros (isometric form), or by a
  unitary of the same size (unitary form).

## Main definitions

* `ChoiRectangular.HasKrausCard T r` — `T` has an exact `r`-operator
  rectangular Kraus representation.
* `ChoiRectangular.HasKrausRankLE T r` — `T` has a rectangular Kraus
  representation with at most `r` operators.
* `ChoiRectangular.choiRank T` — the rank of the rectangular Choi matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2,
  Theorem 2.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

namespace ChoiRectangular

variable {d d' : ℕ}

/-! ### Kraus cardinality and the Choi rank -/

/-- A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` has an exact `r`-operator
rectangular Kraus representation `T(X) = Σⱼ Kⱼ X Kⱼ†` with
`Kⱼ : Matrix (Fin d') (Fin d) ℂ` (Wolf, Theorem 2.1, Equation (2.8)). -/
def HasKrausCard
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) (r : ℕ) :
    Prop :=
  ∃ K : Fin r → Matrix (Fin d') (Fin d) ℂ,
    ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ

/-- A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` admits a rectangular Kraus
representation with at most `r` operators. -/
def HasKrausRankLE
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) (r : ℕ) :
    Prop :=
  ∃ s : ℕ, s ≤ r ∧ HasKrausCard T s

/-- The **Kraus rank** (Choi rank) of a linear map between matrix algebras is
the rank of its Choi matrix (Wolf, Theorem 2.1, footnote: `r = rank(τ)`, to
be distinguished from the rank of `T` as a linear map). -/
noncomputable def choiRank
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) : ℕ :=
  (choiMatrix T).rank

/-- If `T` has `r` Kraus operators and `r ≤ s`, then it also has `s` Kraus
operators obtained by zero-padding (Wolf, Theorem 2.1 item 4: "the smaller
set is padded with zeros"). -/
theorem hasKrausCard_mono {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d') (Fin d') ℂ} {r s : ℕ}
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

/-- The rectangular Choi matrix of a Kraus map is a sum of rank-one outer
products (Wolf, Theorem 2.1, proof, Equation (2.9):
`τ = Σⱼ |ψⱼ⟩⟨ψⱼ|` with `|ψⱼ⟩ = (Kⱼ ⊗ 𝟙)|Ω⟩`). -/
theorem choiMatrix_eq_sum_vecMulVec_of_kraus {r : ℕ}
    (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    choiMatrix T =
      ∑ j : Fin r,
        Matrix.vecMulVec
          (fun p : Fin d' × Fin d => ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) * K j p.1 p.2)
          (star (fun p : Fin d' × Fin d => ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) * K j p.1 p.2)) := by
  classical
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [choiMatrix_apply, hT,
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
      (Matrix.mul_single_mul_conjTranspose_eq_vecMulVec (K := K x) (c := c) i₂ j₂)

/-- Any `r`-operator rectangular Kraus representation bounds the Kraus rank
by `r` (Wolf, Theorem 2.1, proof: `r ≥ rank(τ)`). -/
theorem choiRank_le_of_hasKrausCard {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d') (Fin d') ℂ} {r : ℕ}
    (hT : HasKrausCard T r) :
    choiRank T ≤ r := by
  rcases hT with ⟨K, hK⟩
  exact Channel.rank_le_card_of_eq_sum_vecMulVec _ _
    (choiMatrix_eq_sum_vecMulVec_of_kraus K T hK)

/-- The Kraus rank is at most `d · d'` (Wolf, Theorem 2.1 item 2:
`r = rank(τ) ≤ dd'`). -/
theorem choiRank_le_mul
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiRank T ≤ d * d' := by
  have h := Matrix.rank_le_card_width (choiMatrix T)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  exact h.trans (Nat.mul_comm d' d).le

/-- A completely positive map admits a rectangular Kraus representation whose
cardinality is exactly the rank of its Choi matrix (Wolf, Theorem 2.1, proof:
"equality can be achieved", using the spectral decomposition of `τ ≥ 0`). -/
theorem hasKrausCard_choiRank_of_isKrausCP [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    HasKrausCard T (choiRank T) := by
  classical
  have hτpsd : (choiMatrix T).PosSemidef :=
    (isKrausCP_iff_choiMatrix_posSemidef (T := T)).mp hT
  let hτ : (choiMatrix T).IsHermitian := hτpsd.1
  let v : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} → (Fin d' × Fin d) → ℂ :=
    fun i p => ((Real.sqrt (hτ.eigenvalues i.1) : ℂ)) * hτ.eigenvectorUnitary p i.1
  have hchoi' : choiMatrix T =
      ∑ i : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
        Matrix.vecMulVec (v i) (fun p => star (v i p)) := by
    simpa [hτ, v] using
      Matrix.PosSemidef.eq_sum_vecMulVec_nonzero_eigs (A := choiMatrix T) hτpsd
  have hchoi : choiMatrix T =
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
  obtain ⟨K, hK⟩ := exists_kraus_of_choiMatrix_eq_sum_vecMulVec (T := T)
    (ι := {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0}) v hchoi
  have hK' : HasKrausCard T
      (Fintype.card {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0}) := by
    refine ⟨fun α => K ((Fintype.equivFin _).symm α), ?_⟩
    intro X
    calc
      T X = ∑ m : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
          K m * X * (K m)ᴴ := hK X
      _ = ∑ α : Fin (Fintype.card {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0}),
            K ((Fintype.equivFin _).symm α) * X *
              (K ((Fintype.equivFin _).symm α))ᴴ := by
              refine Fintype.sum_equiv (Fintype.equivFin _) _ _ ?_
              intro m
              simp
  rwa [hcard] at hK'

/-- **Kraus rank** (Wolf, Theorem 2.1 item 2): the minimal number of
rectangular Kraus operators of a completely positive map is the rank of its
Choi matrix, `r = rank(τ)`. -/
theorem choiRank_isLeast_hasKrausCard_of_isKrausCP [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    IsLeast {r : ℕ | HasKrausCard T r} (choiRank T) :=
  ⟨hasKrausCard_choiRank_of_isKrausCP hT,
   fun _r hr => choiRank_le_of_hasKrausCard hr⟩

/-- **Orthogonal minimal Kraus family** (Wolf, Theorem 2.1 item 3): every
completely positive map admits a representation with `r = rank(τ)`
Hilbert–Schmidt orthogonal Kraus operators, `tr[Kᵢ†Kⱼ] ∝ δᵢⱼ`; the
off-diagonal traces vanish and the diagonal traces are nonzero. -/
theorem exists_kraus_orthogonal_of_isKrausCP [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    ∃ K : Fin (choiRank T) → Matrix (Fin d') (Fin d) ℂ,
      (∀ X, T X = ∑ i : Fin (choiRank T), K i * X * (K i)ᴴ) ∧
      (∀ i j : Fin (choiRank T), i ≠ j → ((K i)ᴴ * K j).trace = 0) ∧
      (∀ i : Fin (choiRank T), ((K i)ᴴ * K i).trace ≠ 0) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hτpsd : (choiMatrix T).PosSemidef :=
    (isKrausCP_iff_choiMatrix_posSemidef (T := T)).mp hT
  let hτ : (choiMatrix T).IsHermitian := hτpsd.1
  let v : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} → (Fin d' × Fin d) → ℂ :=
    fun i p => ((Real.sqrt (hτ.eigenvalues i.1) : ℂ)) * hτ.eigenvectorUnitary p i.1
  have hchoi' : choiMatrix T =
      ∑ i : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
        Matrix.vecMulVec (v i) (fun p => star (v i p)) := by
    simpa [hτ, v] using
      Matrix.PosSemidef.eq_sum_vecMulVec_nonzero_eigs (A := choiMatrix T) hτpsd
  have hchoi : choiMatrix T =
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
  -- The Kraus family reconstructed from the spectral decomposition of `τ`.
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hstarc : star c = c := by simp [c]
  have hcc : c * star c = 1 / (d : ℂ) := by
    simpa [c, hstarc] using omegaCoeff_eq_inv (d := d) hdpos
  have hcne : c ≠ 0 := by
    dsimp [c]
    have hsqrt : (((d : ℝ).sqrt : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.2 (by exact_mod_cast hdpos)
    simp [hsqrt]
  let Ks : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} →
      Matrix (Fin d') (Fin d) ℂ :=
    krausOfChoiDecomp (d := d) v
  have hKs : ∀ X, T X = ∑ m : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
      Ks m * X * (Ks m)ᴴ :=
    krausOfChoiDecomp_spec (T := T) v hchoi
  -- The eigenvector columns are orthonormal.
  have hon : ∀ m n : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
      ∑ p : Fin d' × Fin d,
        star (hτ.eigenvectorUnitary p m.1) * hτ.eigenvectorUnitary p n.1 =
          if n = m then 1 else 0 := by
    intro m n
    have hu : (hτ.eigenvectorUnitary :
        Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ)ᴴ *
          (hτ.eigenvectorUnitary :
            Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        Matrix.UnitaryGroup.star_mul_self hτ.eigenvectorUnitary
    have h := congrFun (congrFun hu m.1) n.1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    rw [h]
    simp [Subtype.ext_iff, eq_comm]
  -- The Hilbert–Schmidt Gram matrix of the reconstructed family.
  have hgram : ∀ m n : {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0},
      ((Ks m)ᴴ * Ks n).trace =
        (d : ℂ) * ((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) *
          ((Real.sqrt (hτ.eigenvalues n.1) : ℂ)) * (if n = m then 1 else 0) := by
    intro m n
    have h1 : ((Ks m)ᴴ * Ks n).trace =
        ∑ p : Fin d' × Fin d, star (Ks m p.1 p.2) * Ks n p.1 p.2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
      exact (Fintype.sum_prod_type
        (fun p : Fin d' × Fin d => star (Ks m p.1 p.2) * Ks n p.1 p.2)).symm
    have h2 : ∀ p : Fin d' × Fin d,
        star (Ks m p.1 p.2) * Ks n p.1 p.2 =
          (1 / (c * star c)) *
            (((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) *
              ((Real.sqrt (hτ.eigenvalues n.1) : ℂ))) *
              (star (hτ.eigenvectorUnitary p m.1) *
                hτ.eigenvectorUnitary p n.1) := by
      intro p
      have hsqrtm : star ((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) =
          ((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) := by
        simp
      change star (v m p / c) * (v n p / c) = _
      rw [star_div₀, hstarc, star_mul, hsqrtm]
      simp only [v]
      rw [div_eq_mul_inv, div_eq_mul_inv, one_div, mul_inv]
      ring
    calc
      ((Ks m)ᴴ * Ks n).trace
          = ∑ p : Fin d' × Fin d, star (Ks m p.1 p.2) * Ks n p.1 p.2 := h1
      _ = ∑ p : Fin d' × Fin d,
            (1 / (c * star c)) *
              (((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) *
                ((Real.sqrt (hτ.eigenvalues n.1) : ℂ))) *
                (star (hτ.eigenvectorUnitary p m.1) *
                  hτ.eigenvectorUnitary p n.1) :=
            Finset.sum_congr rfl fun p _ => h2 p
      _ = (1 / (c * star c)) *
            (((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) *
              ((Real.sqrt (hτ.eigenvalues n.1) : ℂ))) *
              (∑ p : Fin d' × Fin d, star (hτ.eigenvectorUnitary p m.1) *
                hτ.eigenvectorUnitary p n.1) := by
            rw [Finset.mul_sum]
      _ = (1 / (c * star c)) *
            (((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) *
              ((Real.sqrt (hτ.eigenvalues n.1) : ℂ))) * (if n = m then 1 else 0) := by
            rw [hon m n]
      _ = (d : ℂ) * ((Real.sqrt (hτ.eigenvalues m.1) : ℂ)) *
            ((Real.sqrt (hτ.eigenvalues n.1) : ℂ)) * (if n = m then 1 else 0) := by
            rw [hcc, one_div_one_div]
            ring
  -- Reindex the subtype-indexed family to `Fin (choiRank T)`.
  let e : Fin (choiRank T) ≃ {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} :=
    (finCongr hcard).symm.trans (Fintype.equivFin _).symm
  refine ⟨fun α => Ks (e α), ?_, ?_, ?_⟩
  · intro X
    rw [hKs X]
    exact (e.sum_comp (fun m => Ks m * X * (Ks m)ᴴ)).symm
  · intro i j hij
    have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hg := hgram (e i) (e j)
    rw [if_neg (show e j ≠ e i from fun h => hne h.symm), mul_zero] at hg
    exact hg
  · intro i
    have hg := hgram (e i) (e i)
    rw [if_pos rfl, mul_one] at hg
    rw [hg, mul_assoc]
    have hlam : (Real.sqrt (hτ.eigenvalues (e i).1) : ℂ) *
        (Real.sqrt (hτ.eigenvalues (e i).1) : ℂ) =
          ((hτ.eigenvalues (e i).1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hτpsd.eigenvalues_nonneg _)]
    rw [hlam]
    exact mul_ne_zero hdne (Complex.ofReal_ne_zero.mpr (e i).2)

/-! ### Normalization conditions (Wolf, Theorem 2.1 item 1) -/

/-- **Trace-preserving normalization, necessary direction** (Wolf, Theorem
2.1 item 1): if the rectangular Kraus map `T(X) = Σⱼ Kⱼ X Kⱼ†` preserves the
trace, then `Σⱼ Kⱼ†Kⱼ = 𝟙`. -/
theorem kraus_sum_conjTranspose_mul_of_tracePreserving
    {r : ℕ} (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (htp : ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :
    ∑ i : Fin r, (K i)ᴴ * K i = 1 := by
  apply (Matrix.ext_iff_trace_mul_right).2
  intro N
  rw [Matrix.one_mul]
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [show ∀ i : Fin r,
    ((K i)ᴴ * K i * N).trace = (K i * N * (K i)ᴴ).trace from
    fun i => by rw [Matrix.mul_assoc ((K i)ᴴ), Matrix.trace_mul_comm, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum]
  conv_lhs => rw [← hK N]
  rw [htp N]

/-- **Trace-preserving normalization** (Wolf, Theorem 2.1 item 1): the
rectangular Kraus map `T(X) = Σⱼ Kⱼ X Kⱼ†` is trace preserving if and only
if `Σⱼ Kⱼ†Kⱼ = 𝟙`. -/
theorem kraus_tp_iff_sum_conjTranspose_mul
    {r : ℕ} (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) ↔
      ∑ i : Fin r, (K i)ᴴ * K i = 1 := by
  constructor
  · exact kraus_sum_conjTranspose_mul_of_tracePreserving K T hK
  · intro h X
    rw [hK X]
    exact kraus_tp_of_sum_conjTranspose_mul K h X

/-- **Unital normalization** (Wolf, Theorem 2.1 item 1): the rectangular
Kraus map `T(X) = Σⱼ Kⱼ X Kⱼ†` is unital if and only if `Σⱼ KⱼKⱼ† = 𝟙`. -/
theorem kraus_unital_iff_sum_mul_conjTranspose
    {r : ℕ} (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    T 1 = 1 ↔ ∑ i : Fin r, K i * (K i)ᴴ = 1 := by
  rw [hK 1]
  simp [Matrix.mul_one]

/-! ### Unitary freedom (Wolf, Theorem 2.1 item 4) -/

/-- If two rectangular Kraus families define the same map, they also define
the same Heisenberg dual: `Σ Bα† Y Bα = Σ Aj† Y Aj` for all `Y`. This is the
uniqueness of the trace-pairing adjoint. -/
theorem kraus_dual_eq_of_map_eq
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin d') (Fin d) ℂ)
    (A : Fin r₂ → Matrix (Fin d') (Fin d) ℂ)
    (h : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∀ Y : Matrix (Fin d') (Fin d') ℂ,
      ∑ α : Fin r₁, (B α)ᴴ * Y * B α =
      ∑ j : Fin r₂, (A j)ᴴ * Y * A j := by
  intro Y
  apply (Matrix.ext_iff_trace_mul_right).2
  intro X
  simp_rw [Finset.sum_mul, Matrix.trace_sum]
  have trace_cycle : ∀ K : Matrix (Fin d') (Fin d) ℂ,
      trace (Kᴴ * Y * K * X) = trace (K * X * Kᴴ * Y) := fun K => by
    rw [Matrix.mul_assoc (Kᴴ * Y) K X, Matrix.trace_mul_comm,
        ← Matrix.mul_assoc (K * X) Kᴴ Y]
  simp_rw [trace_cycle]
  rw [← Matrix.trace_sum, ← Matrix.trace_sum,
      ← Finset.sum_mul, ← Finset.sum_mul]
  rw [h X]

/-- Map equality implies equal Stinespring Gramians:
`Σ Bα†Bα = Σ Aj†Aj`. -/
theorem kraus_conjTranspose_mul_eq_of_map_eq
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin d') (Fin d) ℂ)
    (A : Fin r₂ → Matrix (Fin d') (Fin d) ℂ)
    (h : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∑ α : Fin r₁, (B α)ᴴ * B α =
    ∑ j : Fin r₂, (A j)ᴴ * A j := by
  have hdual := kraus_dual_eq_of_map_eq B A h
  simpa [Matrix.mul_one] using hdual 1

/-- **Isometric mixing, sufficient direction** (Wolf, Theorem 2.1 item 4):
if `W` is an isometry (`W†W = 𝟙`) and `Kⱼ = Σₗ Wⱼₗ K'ₗ`, then `{Kⱼ}` and
`{K'ₗ}` define the same rectangular Kraus map. -/
theorem kraus_same_map_of_isometry_combination
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (K : ι₁ → Matrix (Fin d') (Fin d) ℂ)
    (K' : ι₂ → Matrix (Fin d') (Fin d) ℂ)
    (W : Matrix ι₁ ι₂ ℂ)
    (hW : Wᴴ * W = 1)
    (hK : ∀ j, K j = ∑ l, W j l • K' l) :
    ∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ j, K j * X * (K j)ᴴ =
      ∑ l, K' l * X * (K' l)ᴴ := by
  intro X
  have hW_entry : ∀ l l' : ι₂,
      ∑ j : ι₁, (starRingEnd ℂ) (W j l) * W j l' = if l = l' then 1 else 0 := by
    intro l l'
    have h := congrArg (fun M : Matrix ι₂ ι₂ ℂ => M l l') hW
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    ∑ j, K j * X * (K j)ᴴ
        = ∑ j : ι₁,
            (∑ l, W j l • K' l) * X *
            ((∑ l, W j l • K' l)ᴴ) := by simp only [hK]
    _ = ∑ j : ι₁, ∑ l : ι₂, ∑ l' : ι₂,
          (((starRingEnd ℂ) (W j l')) * W j l) • (K' l * X * (K' l')ᴴ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.sum_mul]
          simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
          rw [Matrix.mul_sum]
          simp_rw [Matrix.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
            starRingEnd_apply]
    _ = ∑ l : ι₂, ∑ l' : ι₂,
          (∑ j : ι₁, ((starRingEnd ℂ) (W j l')) * W j l) • (K' l * X * (K' l')ᴴ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_smul]
    _ = ∑ l : ι₂, ∑ l' : ι₂,
          (if l' = l then 1 else 0) • (K' l * X * (K' l')ᴴ) := by
          simp_rw [hW_entry]; simp
    _ = ∑ l, K' l * X * (K' l)ᴴ := by simp

/-- **Padded isometric freedom, necessary direction** (Wolf, Theorem 2.1
item 4): if two rectangular Kraus families of sizes `r₁` and `r₂` with
`r₂ ≤ r₁` define the same completely positive map, then the larger family is
an isometric linear combination of the smaller one: `Bα = Σⱼ Vαⱼ Aⱼ` with
`V†V = 𝟙`.

The proof follows Wolf via the subsequent "equivalence of ensembles"
proposition: the map equality forces the vectorized Kraus operators
`(Aⱼ)_{ab}` and `(Bα)_{ab}` to have equal Gram matrices, so they are related
by an isometry. -/
theorem kraus_isometry_freedom
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin d') (Fin d) ℂ)
    (A : Fin r₂ → Matrix (Fin d') (Fin d) ℂ)
    (h : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ)
    (hCard : r₂ ≤ r₁) :
    ∃ V : Matrix (Fin r₁) (Fin r₂) ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ α : Fin r₁, B α = ∑ j : Fin r₂, V α j • A j := by
  -- Pad `A` with zeros to size `r₁`.
  let A' : Fin r₁ → Matrix (Fin d') (Fin d) ℂ :=
    fun α => if hlt : α.val < r₂ then A ⟨α.val, hlt⟩ else 0
  have hBA' : ∀ X, ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ α : Fin r₁, A' α * X * (A' α)ᴴ := by
    intro X; rw [h X]
    rw [Fin.sum_castLE_extend_zero (fun j => A j * X * (A j)ᴴ) hCard]
    apply Finset.sum_congr rfl; intro α _
    simp only [A']; split_ifs <;> simp
  have hdual := kraus_dual_eq_of_map_eq B A' hBA'
  -- Equal Gram matrices of the vectorized families.
  let MB : Matrix (Fin r₁) (Fin d' × Fin d) ℂ := fun α x => B α x.1 x.2
  let MA' : Matrix (Fin r₁) (Fin d' × Fin d) ℂ := fun α x => A' α x.1 x.2
  have hGram : MBᴴ * MB = MA'ᴴ * MA' := by
    ext ⟨a, b⟩ ⟨c, e⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, MB, MA']
    have h_entry := congr_fun (congr_fun (hdual (Matrix.single a c 1)) b) e
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.single_apply] at h_entry
    have collapse : ∀ (K : Fin r₁ → Matrix (Fin d') (Fin d) ℂ),
        (∑ α, ∑ x₁, (∑ x₂, star (K α x₂ b) *
          (if a = x₂ ∧ c = x₁ then (1 : ℂ) else 0)) * K α x₁ e) =
        ∑ α, star (K α a b) * K α c e := by
      intro K
      apply Finset.sum_congr rfl; intro α _
      have step₁ : ∀ x₁, (∑ x₂, star (K α x₂ b) *
          (if a = x₂ ∧ c = x₁ then (1 : ℂ) else 0)) * K α x₁ e =
          if c = x₁ then star (K α a b) * K α x₁ e else 0 := by
        intro x₁
        have h_inner : (∑ x₂, star (K α x₂ b) *
            (if a = x₂ ∧ c = x₁ then (1 : ℂ) else 0)) =
            if c = x₁ then star (K α a b) else 0 := by
          rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx])
              (fun h => absurd (Finset.mem_univ _) h)]
          simp
        rw [h_inner]; split_ifs <;> simp
      simp_rw [step₁]; simp [Finset.sum_ite_eq, Finset.mem_univ]
    rw [collapse, collapse] at h_entry
    exact h_entry
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (B := MB) (A := MA') hGram
  have hU_unitary :
      (U : Matrix (Fin r₁) (Fin r₁) ℂ)ᴴ * (U : Matrix (Fin r₁) (Fin r₁) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hU_mat_eq : (U : Matrix (Fin r₁) (Fin r₁) ℂ) * MA' = MB := hU.symm
  refine ⟨fun α j => (U : Matrix (Fin r₁) (Fin r₁) ℂ) α (Fin.castLE hCard j), ?_, ?_⟩
  · ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    have h_uu := congr_fun (congr_fun hU_unitary (Fin.castLE hCard j)) (Fin.castLE hCard k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h_uu
    rw [h_uu]; simp [(Fin.castLE_injective hCard).eq_iff]
  · intro α; ext a b
    have h_entry : (B α) a b =
        ∑ β : Fin r₁, (U : Matrix (Fin r₁) (Fin r₁) ℂ) α β * (A' β) a b := by
      have := congr_fun (congr_fun hU_mat_eq α) (a, b)
      simpa [Matrix.mul_apply, MB, MA'] using this.symm
    rw [h_entry]; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Fin.sum_castLE_extend_zero
      (fun j => (U : Matrix (Fin r₁) (Fin r₁) ℂ) α (Fin.castLE hCard j) *
        (A j) a b) hCard]
    apply Finset.sum_congr rfl; intro β _
    simp only [A']; split_ifs with hlt
    · simp only [Fin.eta, Fin.castLE]
    · simp only [Matrix.zero_apply, mul_zero]

/-- **Padded unitary freedom** (Wolf, Theorem 2.1 item 4): two rectangular
Kraus families define the same completely positive map if and only if, after
padding the smaller family with zero operators, they are related by an
isometric mixing matrix. -/
theorem kraus_isometry_freedom_iff
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : ι₁ → Matrix (Fin d') (Fin d) ℂ)
    (A : ι₂ → Matrix (Fin d') (Fin d) ℂ)
    (hCard : Fintype.card ι₂ ≤ Fintype.card ι₁) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ V : Matrix ι₁ ι₂ ℂ,
        Vᴴ * V = 1 ∧
        ∀ α, B α = ∑ j, V α j • A j := by
  classical
  constructor
  · intro h
    -- Reindex to `Fin` and apply the necessary direction.
    let e₁ : ι₁ ≃ Fin (Fintype.card ι₁) := Fintype.equivFin ι₁
    let e₂ : ι₂ ≃ Fin (Fintype.card ι₂) := Fintype.equivFin ι₂
    let B' : Fin (Fintype.card ι₁) → Matrix (Fin d') (Fin d) ℂ := B ∘ e₁.symm
    let A' : Fin (Fintype.card ι₂) → Matrix (Fin d') (Fin d) ℂ := A ∘ e₂.symm
    have h' : ∀ X : Matrix (Fin d) (Fin d) ℂ,
        ∑ α : Fin (Fintype.card ι₁), B' α * X * (B' α)ᴴ =
        ∑ j : Fin (Fintype.card ι₂), A' j * X * (A' j)ᴴ := by
      intro X
      change ∑ α, B (e₁.symm α) * X * (B (e₁.symm α))ᴴ =
        ∑ j, A (e₂.symm j) * X * (A (e₂.symm j))ᴴ
      rw [e₁.symm.sum_comp (fun i => B i * X * (B i)ᴴ),
          e₂.symm.sum_comp (fun j => A j * X * (A j)ᴴ)]
      exact h X
    obtain ⟨V', hV'_iso, hV'_decomp⟩ := kraus_isometry_freedom B' A' h' hCard
    refine ⟨fun α j => V' (e₁ α) (e₂ j), ?_, ?_⟩
    · ext j k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      rw [show ∑ x : ι₁, star (V' (e₁ x) (e₂ j)) * V' (e₁ x) (e₂ k) =
          ∑ β, star (V' β (e₂ j)) * V' β (e₂ k) from
        e₁.sum_comp (fun β => star (V' β (e₂ j)) * V' β (e₂ k))]
      have h_entry := congr_fun (congr_fun hV'_iso (e₂ j)) (e₂ k)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        e₂.injective.eq_iff] at h_entry
      exact h_entry
    · intro α
      have := hV'_decomp (e₁ α)
      simp only [B', A', Function.comp, Equiv.symm_apply_apply] at this
      rw [this, ← e₂.sum_comp (fun β => V' (e₁ α) β • A (e₂.symm β))]
      simp [Equiv.symm_apply_apply]
  · rintro ⟨V, hV, hBA⟩
    exact kraus_same_map_of_isometry_combination (K := B) (K' := A) (W := V) hV hBA

/-- **Unitary freedom, same-size form** (Wolf, Theorem 2.1 item 4): two
rectangular Kraus families with the same finite index type define the same
completely positive map if and only if they are related by a unitary mixing
matrix. -/
theorem kraus_unitary_freedom_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A : ι → Matrix (Fin d') (Fin d) ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ U : Matrix.unitaryGroup ι ℂ,
        ∀ α, B α = ∑ j, (U : Matrix ι ι ℂ) α j • A j := by
  rw [kraus_isometry_freedom_iff B A le_rfl]
  refine ⟨fun ⟨V, hV, hBA⟩ => ⟨⟨V, Matrix.mem_unitaryGroup_iff'.2 hV⟩, hBA⟩,
          fun ⟨U, hBA⟩ => ⟨(U : Matrix ι ι ℂ), Matrix.mem_unitaryGroup_iff'.mp U.prop, hBA⟩⟩

end ChoiRectangular
