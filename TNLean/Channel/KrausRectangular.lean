/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.ChoiRectangular
import TNLean.Channel.KrausRank
import TNLean.Channel.KrausRepresentation

/-!
# Rectangular Kraus representation theorem

This file collects the genuinely rectangular-specific parts of Wolf Chapter 2,
Theorem 2.1 (Kraus representation), `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 229–273, for a linear map `T : M_d(ℂ) → M_{d'}(ℂ)`:

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
  operators (`tr[Kᵢ†Kⱼ] ∝ δᵢⱼ`).

## Design notes

The dimension-generic Kraus API — `Channel.HasKrausCard`,
`Channel.HasKrausRankLE`, `Channel.choiRank`, the Choi-rank bounds, and the
Kraus-freedom theorems (`kraus_dual_eq_of_map_eq`,
`kraus_conjTranspose_mul_eq_of_map_eq`,
`kraus_same_map_of_isometry_combination`, `kraus_rectangular_freedom`,
`kraus_isometry_freedom_iff`, `kraus_unitary_freedom_iff`) — lives in
`TNLean/Channel/KrausRank.lean`, `TNLean/Channel/KrausRepresentation.lean`,
`TNLean/Channel/KrausFreedom.lean`, and
`TNLean/Channel/KrausUnitaryFreedom.lean`, generalized to rectangular shape;
the present file keeps only the theorems that have no square counterpart.
The square development is the specialization `d = d'` of the generalized API.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2,
  Theorem 2.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

namespace ChoiRectangular

variable {d d' : ℕ}

/-! ### Kraus rank bounds specific to the rectangular Choi matrix -/

/-- The Kraus rank is at most `d · d'` (Wolf, Theorem 2.1 item 2:
`r = rank(τ) ≤ dd'`). -/
theorem choiRank_le_mul
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Channel.choiRank T ≤ d * d' := by
  have h := Matrix.rank_le_card_width (choiMatrix T)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  exact h.trans (Nat.mul_comm d' d).le

/-- **Kraus rank** (Wolf, Theorem 2.1 item 2): the minimal number of
rectangular Kraus operators of a completely positive map is the rank of its
Choi matrix, `r = rank(τ)`. -/
theorem choiRank_isLeast_hasKrausCard_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    IsLeast {r : ℕ | Channel.HasKrausCard T r} (Channel.choiRank T) :=
  ⟨Channel.hasKrausCard_choiRank_of_cp hT,
   fun _r hr => Channel.choiRank_le_of_hasKrausCard hr⟩

/-- **Orthogonal minimal Kraus family** (Wolf, Theorem 2.1 item 3): every
completely positive map admits a representation with `r = rank(τ)`
Hilbert–Schmidt orthogonal Kraus operators, `tr[Kᵢ†Kⱼ] ∝ δᵢⱼ`; the
off-diagonal traces vanish and the diagonal traces are nonzero. -/
theorem exists_kraus_orthogonal_of_isKrausCP [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    ∃ K : Fin (Channel.choiRank T) → Matrix (Fin d') (Fin d) ℂ,
      (∀ X, T X = ∑ i : Fin (Channel.choiRank T), K i * X * (K i)ᴴ) ∧
      (∀ i j : Fin (Channel.choiRank T), i ≠ j → ((K i)ᴴ * K j).trace = 0) ∧
      (∀ i : Fin (Channel.choiRank T), ((K i)ᴴ * K i).trace ≠ 0) := by
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
      Channel.choiRank T := by
    unfold Channel.choiRank
    simpa [hτ] using (hτ.rank_eq_card_non_zero_eigs).symm
  -- The Kraus family reconstructed from the spectral decomposition of `τ`.
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hstarc : star c = c := by simp [c]
  have hcc : c * star c = 1 / (d : ℂ) := by
    simpa [c, hstarc] using ChoiJamiolkowski.omegaCoeff_eq_inv (D := d) hdpos
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
  -- Reindex the subtype-indexed family to `Fin (Channel.choiRank T)`.
  let e : Fin (Channel.choiRank T) ≃ {j : Fin d' × Fin d // hτ.eigenvalues j ≠ 0} :=
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
  · exact kraus_sum_conjTranspose_mul_of_tp K T hK
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

end ChoiRectangular
