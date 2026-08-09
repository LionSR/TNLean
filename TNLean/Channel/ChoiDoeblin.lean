/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.TraceNormContractivity
import TNLean.Channel.ChoiRectangular
import TNLean.Channel.SupportCompletion

/-!
# Choi-dominated Doeblin contraction

If the rectangular Choi matrix of a trace-preserving, Hermiticity-preserving
linear map $T : M_D(\mathbb{C}) \to M_{D'}(\mathbb{C})$ dominates $(\varepsilon/D)(Y \otimes \mathbf{1})$ for some $\varepsilon \ge 0$
and Hermitian $Y$ with $\mathrm{tr}[Y] = 1$, then $T$ satisfies the Doeblin trace-norm
contraction $\|T(\rho_1) - T(\rho_2)\|_1 \le (1 - \varepsilon)\|\rho_1 - \rho_2\|_1$ for all density matrices.

The proof constructs the trace-prepare map $T'(X) = \mathrm{tr}[X]Y$, computes its
rectangular Choi matrix as $(1/D)(Y \otimes \mathbf{1})$, uses the rectangular CP/PSD
equivalence to derive positivity of $T - \varepsilon T'$, and applies the quantum
Doeblin theorem (`Matrix.traceNorm_map_sub_map_le_of_doeblin`).

## Main results

* `Matrix.choiMatrix_tracePrepareMap` — the rectangular Choi matrix
  of the trace-prepare map is $(1/d)(Y \otimes \mathbf{1})$.
* `Matrix.traceNorm_map_sub_map_le_of_choi_domination` — Wolf Eq. (8.86):
  Choi-dominated Doeblin contraction.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour* (July 5, 2012),
Chapter 8, Eq. (8.86);
Notes/WolfNoteTexSource/ch08_distance_measures.tex, lines 971–979.
-/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

/-! ### Choi-dominated Doeblin contraction -/

/-- **Choi matrix of the trace-prepare map** (auxiliary lemma for Eq. (8.86)).

For an arbitrary matrix $Y$ on the output space, the trace-prepare
map $T'(X) = \mathrm{tr}[X]Y$ has Choi matrix $(1/d)(Y \otimes \mathbf{1})$ in the output-factor-first
tensor order of `ChoiRectangular.choiMatrix`.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, line 973. -/
lemma choiMatrix_tracePrepareMap (d d' : ℕ)
    (Y : Matrix (Fin d') (Fin d') ℂ) :
    ChoiRectangular.choiMatrix (tracePrepareMap (α := Fin d) Y) =
      (1 / (d : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  by_cases hd : d = 0
  · subst hd
    ext ⟨a, i⟩ ⟨b, j⟩
    exact Fin.elim0 i
  · haveI : NeZero d := ⟨hd⟩
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    ext ⟨a, i⟩ ⟨b, j⟩
    calc
      ChoiRectangular.choiMatrix (tracePrepareMap (α := Fin d) Y) (a, i) (b, j)
          = (tracePrepareMap (α := Fin d) Y
              (Matrix.bipartiteSlice (Matrix.omegaProj d) i j)) a b := by
        rw [ChoiRectangular.choiMatrix_apply]
      _ = (Matrix.trace (Matrix.bipartiteSlice (Matrix.omegaProj d) i j) • Y) a b := by
        rw [tracePrepareMap_apply]
      _ = Matrix.trace (Matrix.bipartiteSlice (Matrix.omegaProj d) i j) * Y a b := by
        rw [Matrix.smul_apply, smul_eq_mul]
      _ = Matrix.trace ((1 / (d : ℂ)) • Matrix.single i j (1 : ℂ)) * Y a b := by
        have h := ChoiJamiolkowski.omegaSlice_eq_single (D := d) i j
        rw [h, ChoiJamiolkowski.omegaCoeff_eq_inv hdpos]
        simp [Matrix.smul_single]
      _ = ((1 / (d : ℂ)) * Matrix.trace (Matrix.single i j (1 : ℂ))) * Y a b := by
        rw [Matrix.trace_smul, smul_eq_mul]
      _ = (1 / (d : ℂ)) * (kroneckerMap (· * ·) Y (1 : Matrix (Fin d) (Fin d) ℂ))
            (a, i) (b, j) := by
        by_cases hij : i = j
        · subst hij
          simp [kroneckerMap_apply]
        · simp [kroneckerMap_apply, hij]
      _ = ((1 / (d : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin d) (Fin d) ℂ)))
            (a, i) (b, j) := by
        rw [Matrix.smul_apply, smul_eq_mul]

/-- **Choi-dominated Doeblin contraction.**

Let $T : M_D(\mathbb{C}) \to M_{D'}(\mathbb{C})$ be a trace-preserving, Hermiticity-preserving
linear map.  For $\varepsilon \ge 0$ and a Hermitian $Y$ with trace one, if
the (rectangular, output-factor-first) Choi matrix satisfies
```
τ = choi(T) ≥ (ε/D)(Y ⊗ 𝟙),
```
then for all density operators $\rho_1, \rho_2 \in M_D$,
```
‖T(ρ₁) - T(ρ₂)‖₁ ≤ (1 - ε) ‖ρ₁ - ρ₂‖₁.
```

The proof constructs $T'(X) = \mathrm{tr}[X]Y$ (the trace-prepare map) and applies
`Matrix.traceNorm_map_sub_map_le_of_doeblin` (Wolf Theorem 8.17, Eq. (8.82)).
The Choi domination guarantees, via the rectangular CP/PSD equivalence
(`ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef`), that $T - \varepsilon T'$ is
positive, satisfying the hypothesis of Theorem 8.17.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 971–979. -/
theorem traceNorm_map_sub_map_le_of_choi_domination
    {D D' : ℕ}
    {ε : ℝ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ}
    {Y : Matrix (Fin D') (Fin D') ℂ}
    (htrT : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T X).trace = X.trace)
    (hhermT : ∀ X : Matrix (Fin D) (Fin D) ℂ, X.IsHermitian → (T X).IsHermitian)
    (hYherm : Y.IsHermitian)
    (hYtr : Y.trace = 1)
    (hε_nonneg : 0 ≤ ε)
    (hchoi : ChoiRectangular.choiMatrix T ≥
      ((ε : ℂ) / (D : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ)))
    {ρ₁ ρ₂ : Matrix (Fin D) (Fin D) ℂ} (h₁ : ρ₁.PosSemidef)
    (h₂ : ρ₂.PosSemidef) (h₁tr : ρ₁.trace = 1) (h₂tr : ρ₂.trace = 1) :
    traceNorm (T ρ₁ - T ρ₂) ≤ (1 - ε) * traceNorm (ρ₁ - ρ₂) := by
  by_cases hD : D = 0
  · subst hD
    have hzero : (ρ₁ : Matrix (Fin 0) (Fin 0) ℂ).trace = (0 : ℂ) := by simp
    rw [hzero] at h₁tr
    norm_num at h₁tr
  · haveI : NeZero D := ⟨hD⟩
    -- Step 1: construct T' = tracePrepareMap Y
    set T' := tracePrepareMap (α := Fin D) Y with hT'_def
    -- T' is trace-preserving (since tr Y = 1)
    have htrT' : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T' X).trace = X.trace := by
      intro X
      rw [hT'_def, tracePrepareMap_trace, hYtr, mul_one]
    -- T' is Hermiticity-preserving
    have hhermT' : ∀ X : Matrix (Fin D) (Fin D) ℂ, X.IsHermitian → (T' X).IsHermitian := by
      intro X hX
      have htr_star : star (X.trace) = X.trace := by
        calc
          star (X.trace) = (Xᴴ).trace := by rw [Matrix.trace_conjTranspose]
          _ = X.trace := by rw [hX]
      rw [hT'_def, tracePrepareMap_apply]
      calc
        (X.trace • Y)ᴴ = star (X.trace) • Yᴴ := by simp [Matrix.conjTranspose_smul]
        _ = star (X.trace) • Y := by rw [hYherm.eq]
        _ = X.trace • Y := by rw [htr_star]
    -- T' has the special form T'(X) = tr[X]·Y
    have hT'_form : ∃ Y' : Matrix (Fin D') (Fin D') ℂ,
        ∀ X : Matrix (Fin D) (Fin D) ℂ, T' X = (X.trace) • Y' := by
      refine ⟨Y, ?_⟩
      intro X
      rw [hT'_def, tracePrepareMap_apply]
    -- Step 2: key identity choiMatrix(T') = (1/D)(Y ⊗ 𝟙)
    have hchoi_T' : ChoiRectangular.choiMatrix T' =
        (1 / (D : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ)) :=
      choiMatrix_tracePrepareMap D D' Y
    -- Step 3: choi(T - ε·T') ≥ 0 via linearity and Choi domination
    have hchoi_diff_pos : (ChoiRectangular.choiMatrix (T - (ε : ℂ) • T')).PosSemidef := by
      have hsub : ChoiRectangular.choiMatrix (T - (ε : ℂ) • T') =
          ChoiRectangular.choiMatrix T - ChoiRectangular.choiMatrix ((ε : ℂ) • T') :=
        (ChoiRectangular.choiMatrixLinearMap (d := D) (d' := D')).map_sub T ((ε : ℂ) • T')
      rw [hsub, ChoiRectangular.choiMatrix_smul, hchoi_T']
      -- Now:  choi(T) - (ε:ℂ) • ((1/D)(Y⊗1)) = choi(T) - ((ε:ℂ)/D)(Y⊗1)
      have hsmul : (ε : ℂ) • ((1 / (D : ℂ)) •
          (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ))) =
          ((ε : ℂ) / (D : ℂ)) •
          (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [smul_smul]
        congr
        ring
      rw [hsmul]
      -- hchoi says choi(T) ≥ ((ε:ℂ)/D)(Y⊗1), so the difference is PSD
      exact (Matrix.le_iff.mp hchoi)
    -- Step 4: by rectangular CP/PSD equivalence, T - ε·T' is completely positive
    have hCP_diff : IsKrausCP (T - (ε : ℂ) • T') :=
      (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (T - (ε : ℂ) • T')).mpr hchoi_diff_pos
    -- Hence T - ε·T' preserves PSD (positive map)
    have hpos_diff : ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef →
        ((T - (ε : ℂ) • T') ρ).PosSemidef :=
      fun ρ hρ => hCP_diff.map_posSemidef hρ
    -- Step 5: apply the quantum Doeblin theorem
    exact traceNorm_map_sub_map_le_of_doeblin htrT htrT' hhermT hhermT' hT'_form
      hε_nonneg hpos_diff h₁ h₂ h₁tr h₂tr

end Matrix
