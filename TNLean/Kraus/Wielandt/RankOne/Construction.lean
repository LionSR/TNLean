/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.Tuple.Basic
import TNLean.Kraus.Word
import TNLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Rank-one construction for finite matrix families

This module contains the channel-generic row-spreading and rank-one construction
reductions used in the proof of Sanz, Pérez-García, Wolf, and Cirac,
arXiv:0909.5347, Lemma 2(b).
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- The pointwise transpose of a finite matrix family. -/
noncomputable abbrev transposeFamily
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i ↦ (K i)ᵀ

/-- Full fixed-length word span is preserved by pointwise transposition. -/
theorem wordSpan_transposeFamily_eq_top_of_wordSpan_eq_top
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (h : wordSpan K N = ⊤) :
    wordSpan (transposeFamily K) N = ⊤ := by
  classical
  unfold wordSpan at h ⊢
  have hrange :
      Set.range (fun σ : Fin N → Fin d =>
        Kraus.evalWord (transposeFamily K) (List.ofFn σ)) =
        Set.range (fun σ : Fin N → Fin d =>
          (Kraus.evalWord K (List.ofFn σ))ᵀ) := by
    ext M
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨σ ∘ Fin.rev, ?_⟩
      have hrev : ((σ ∘ Fin.rev) ∘ Fin.rev) = σ := by
        funext i
        simpa only [Function.comp_apply] using congrArg σ (Fin.rev_rev i)
      simpa [transposeFamily, List.ofFn_reverse, hrev] using
        (evalWord_transpose K (List.ofFn (σ ∘ Fin.rev)))
    · rintro ⟨σ, rfl⟩
      refine ⟨σ ∘ Fin.rev, ?_⟩
      simpa [transposeFamily, List.ofFn_reverse] using
        (evalWord_transpose K (List.ofFn σ)).symm
  rw [hrange]
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ
  have hmap :
      Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (Submodule.span ℂ
            (Set.range fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ))) =
        Submodule.span ℂ
          (Set.range fun σ : Fin N → Fin d =>
            (Kraus.evalWord K (List.ofFn σ))ᵀ) := by
    rw [Submodule.map_span]
    have hrange' :
        (fun M : Matrix (Fin D) (Fin D) ℂ => Mᵀ) ''
            Set.range (fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ)) =
          Set.range fun σ : Fin N → Fin d =>
            (Kraus.evalWord K (List.ofFn σ))ᵀ := by
      simpa [Function.comp_def] using
        (Set.range_comp (fun M : Matrix (Fin D) (Fin D) ℂ => Mᵀ)
          (fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ))).symm
    simp [e, hrange']
  calc
    Submodule.span ℂ
        (Set.range fun σ : Fin N → Fin d =>
          (Kraus.evalWord K (List.ofFn σ))ᵀ) =
        Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (Submodule.span ℂ
            (Set.range fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ))) := by
      symm
      exact hmap
    _ = Submodule.map
        (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ⊤ := by
      rw [h]
    _ = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
      simp [Submodule.map_top, LinearEquiv.range (e := e)]

/-- Full cumulative word span is preserved by pointwise transposition. -/
theorem cumulativeSpan_transposeFamily_eq_top_of_cumulativeSpan_eq_top
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (h : cumulativeSpan K N = ⊤) :
    cumulativeSpan (transposeFamily K) N = ⊤ := by
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ
  have hmap :
      Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (cumulativeSpan K N) =
        cumulativeSpan (transposeFamily K) N := by
    unfold cumulativeSpan
    rw [Submodule.map_span]
    have hset :
        (fun M : Matrix (Fin D) (Fin D) ℂ => Mᵀ) ''
            {M | ∃ w : List (Fin d), w.length ≤ N ∧ M = Kraus.evalWord K w} =
          {M | ∃ w : List (Fin d), w.length ≤ N ∧
            M = Kraus.evalWord (transposeFamily K) w} := by
      ext M
      constructor
      · rintro ⟨M', ⟨w, hw, rfl⟩, hM⟩
        refine ⟨w.reverse, by simpa using hw, ?_⟩
        rw [← hM]
        simpa [transposeFamily] using evalWord_transpose K w
      · rintro ⟨w, hw, hM⟩
        refine ⟨Kraus.evalWord K w.reverse, ⟨w.reverse, by simpa using hw, rfl⟩, ?_⟩
        rw [hM]
        simpa [transposeFamily] using evalWord_transpose K w.reverse
    simp [e, hset]
  calc
    cumulativeSpan (transposeFamily K) N =
        Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (cumulativeSpan K N) := hmap.symm
    _ = Submodule.map
        (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ⊤ := by
      rw [h]
    _ = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
      simp [Submodule.map_top, LinearEquiv.range (e := e)]

/-- The linear map `M ↦ ψ ᵥ* M` for a fixed row vector `ψ`. -/
noncomputable def vecMulLinearMap (ψ : Fin D → ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D → ℂ) :=
  { toFun := fun M ↦ Matrix.vecMul ψ M
    map_add' := fun M N ↦ by
      simpa using Matrix.vecMul_add (A := M) (B := N) (x := ψ)
    map_smul' := fun c M ↦ by
      simpa using Matrix.vecMul_smul (v := ψ) (b := c) (M := M) }

/-- The span of row vectors obtained by right multiplication with words of length `n`. -/
noncomputable def rowSpreadSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (n : ℕ) :
    Submodule ℂ (Fin D → ℂ) :=
  Submodule.span ℂ (Set.range fun σ : Fin n → Fin d =>
    Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ)))

private theorem vecMul_evalWord_ofFn_eq_evalWord_transposeFamily_mulVec
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ)
    {n : ℕ} (σ : Fin n → Fin d) :
    Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ)) =
      Kraus.evalWord (transposeFamily K) (List.ofFn (σ ∘ Fin.rev)) *ᵥ ψ := by
  calc
    Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ)) =
        (Kraus.evalWord K (List.ofFn σ))ᵀ *ᵥ ψ := by
      simpa using Matrix.vecMul_transpose
        (A := (Kraus.evalWord K (List.ofFn σ))ᵀ) (x := ψ)
    _ = Kraus.evalWord (transposeFamily K) (List.ofFn σ).reverse *ᵥ ψ := by
      simp [evalWord_transpose]
    _ = Kraus.evalWord (transposeFamily K) (List.ofFn (σ ∘ Fin.rev)) *ᵥ ψ := by
      simp [List.ofFn_reverse]

/-- Row spreading is vector spreading for the pointwise-transposed family. -/
theorem rowSpreadSpan_eq_vectorSpreadSpan_transpose
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (n : ℕ) :
    rowSpreadSpan K ψ n = vectorSpreadSpan (transposeFamily K) ψ n := by
  classical
  unfold rowSpreadSpan vectorSpreadSpan
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨σ, rfl⟩
    apply Submodule.subset_span
    refine ⟨σ ∘ Fin.rev, ?_⟩
    simpa using
      (vecMul_evalWord_ofFn_eq_evalWord_transposeFamily_mulVec
        (K := K) (ψ := ψ) (σ := σ)).symm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨σ, rfl⟩
    apply Submodule.subset_span
    refine ⟨σ ∘ Fin.rev, ?_⟩
    have h := vecMul_evalWord_ofFn_eq_evalWord_transposeFamily_mulVec
      (K := K) (ψ := ψ) (σ := σ ∘ Fin.rev)
    have hrev : ((σ ∘ Fin.rev) ∘ Fin.rev) = σ := by
      funext i
      simpa only [Function.comp_apply] using congrArg σ (Fin.rev_rev i)
    simpa [hrev] using h

/-- Mapping `wordSpan` along `M ↦ ψ ᵥ* M` yields `rowSpreadSpan`. -/
theorem map_wordSpan_eq_rowSpreadSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (n : ℕ) :
    Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan K n) =
      rowSpreadSpan K ψ n := by
  classical
  unfold vecMulLinearMap wordSpan rowSpreadSpan
  rw [Submodule.map_span]
  have hrange :
      (Set.range fun σ : Fin n → Fin d =>
        Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ))) =
        (fun M : Matrix (Fin D) (Fin D) ℂ => Matrix.vecMul ψ M) ''
          (Set.range fun σ : Fin n → Fin d => Kraus.evalWord K (List.ofFn σ)) := by
    simpa [Function.comp_def] using
      (Set.range_comp (fun M : Matrix (Fin D) (Fin D) ℂ => Matrix.vecMul ψ M)
        (fun σ : Fin n → Fin d => Kraus.evalWord K (List.ofFn σ)))
  simp [hrange]

/-- Full row spread realizes every standard basis row by a word-span matrix. -/
theorem exists_wordSpan_vecMul_eq_pi_single
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) {n : ℕ}
    (hRow : rowSpreadSpan K ψ n = ⊤) (j : Fin D) :
    ∃ M : Matrix (Fin D) (Fin D) ℂ,
      M ∈ wordSpan K n ∧ Matrix.vecMul ψ M = Pi.single j (1 : ℂ) := by
  classical
  have hmap :
      Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan K n) = ⊤ := by
    rw [map_wordSpan_eq_rowSpreadSpan K ψ n, hRow]
  have hj_mem :
      Pi.single j (1 : ℂ) ∈
        Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan K n) := by
    simp [hmap]
  rcases hj_mem with ⟨M, hM, hM_apply⟩
  exact ⟨M, hM, by simpa [vecMulLinearMap] using hM_apply⟩

/-- Cumulative spanning and a nonzero transpose eigenvector imply full row spread. -/
theorem rowSpreadSpan_eq_top_of_cumulativeSpan_eq_top_of_eigenvector_transpose
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (hψ : ψ ≠ 0)
    (i₁ : Fin d) (ν : ℂ) (hν : ν ≠ 0)
    (heigψ : (K i₁)ᵀ *ᵥ ψ = ν • ψ)
    {N : ℕ} (hCum : cumulativeSpan K N = ⊤) :
    rowSpreadSpan K ψ (D - 1) = ⊤ := by
  have hCumT : cumulativeSpan (transposeFamily K) N = ⊤ :=
    cumulativeSpan_transposeFamily_eq_top_of_cumulativeSpan_eq_top K hCum
  have hcum : cumulativeVectorSpan (transposeFamily K) ψ (D - 1) = ⊤ :=
    eigenvector_spreading_of_cumulativeSpan_eq_top
      (transposeFamily K) ψ hψ hCumT
  have hvec : vectorSpreadSpan (transposeFamily K) ψ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
      (transposeFamily K) ψ (D - 1) i₁ ν hν (by simpa [transposeFamily] using heigψ) hcum
  simpa [rowSpreadSpan_eq_vectorSpreadSpan_transpose K ψ (D - 1)] using hvec

/-- One rank-one word-span element and full row spread yield the rank-one basis. -/
theorem vecMulVec_pi_single_mem_wordSpan_of_rankOne
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (φ ψ : Fin D → ℂ) {m k : ℕ}
    (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan K m)
    (hRow : rowSpreadSpan K ψ k = ⊤) :
    ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan K (m + k) := by
  classical
  intro j
  obtain ⟨M, hM, hvec⟩ := exists_wordSpan_vecMul_eq_pi_single K ψ hRow j
  have hprod : Matrix.vecMulVec φ ψ * M ∈ wordSpan K (m + k) :=
    wordSpan_mul_le K m k (Submodule.mul_mem_mul hRankOne hM)
  simpa [Matrix.vecMulVec_mul, hvec] using hprod

/-- Vector spread, one rank-one element, and row spread imply full matrix span. -/
theorem wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOne
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (φ ψ : Fin D → ℂ) {n m k : ℕ}
    (hVec : vectorSpreadSpan K φ n = ⊤)
    (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan K m)
    (hRow : rowSpreadSpan K ψ k = ⊤) :
    wordSpan K (n + (m + k)) = ⊤ := by
  have hRankOneBasis : ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan K (m + k) :=
    vecMulVec_pi_single_mem_wordSpan_of_rankOne K φ ψ hRankOne hRow
  exact wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis K φ hVec hRankOneBasis

end Kraus
