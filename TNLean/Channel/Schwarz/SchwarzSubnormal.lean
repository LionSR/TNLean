/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.SchwarzNormal
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Schwarz inequalities for subnormal and commuting dominant operators

This file records the Chapter 5 extensions of the normal-input Schwarz inequality
that appear in Wolf's notes.

## Main declarations

* `KadisonSchwarz.IsSubnormal`
* `KadisonSchwarz.schwarz_inequality_subnormal_operator`
* `KadisonSchwarz.wolf_theorem_5_5`
* `KadisonSchwarz.commuting_dominant_right_bound`
* `KadisonSchwarz.kadison_schwarz_commuting_dominant_cp_of_two_sided_bound`
* `KadisonSchwarz.kadison_schwarz_commuting_dominant_cp`
* `KadisonSchwarz.schwarz_inequality_commuting_dominant_operator`
* `KadisonSchwarz.wolf_theorem_5_6`

The key new result is `commuting_dominant_right_bound`: if `D ≥ 0` commutes with
`A` and dominates `A† A`, then it also dominates `A A†`.  The proof uses the
C*-algebra structure on matrices: the PD case uses the CFC square root and the
contraction lemma `B† B ≤ 1 → B B† ≤ 1` (proved via the C*-identity), and the
general PSD case follows by approximating `D` with `D + ε · I`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorems 5.5 and 5.6][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

/-! ### C*-algebra infrastructure for matrices -/

namespace KadisonSchwarz

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

-- Equip matrices with the L2 operator norm for the C*-algebra structure.
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

noncomputable local instance : CStarAlgebra Mat where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := Matrix.instCStarRing
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance

/-! ### Contraction lemma -/

/-- The **contraction lemma**: for any square matrix `B`, if `B† B ≤ 1` then `B B† ≤ 1`.
The proof uses the C*-identity `‖x* x‖ = ‖x‖²`. -/
private lemma contraction_conjTranspose
    (B : Mat) (h : Bᴴ * B ≤ 1) : B * Bᴴ ≤ 1 := by
  change B * star B ≤ 1
  have h' : star B * B ≤ 1 := by simpa using h
  have h_norm_sq : ‖B‖₊ * ‖B‖₊ ≤ 1 := by
    simpa [CStarRing.nnnorm_star_mul_self] using
      (CStarAlgebra.nnnorm_le_one_iff_of_nonneg _ (star_mul_self_nonneg B)).2 h'
  have h_norm_mul_star : ‖B * star B‖₊ ≤ 1 := by
    rw [show B * star B = star (star B) * star B from by rw [star_star],
      CStarRing.nnnorm_star_mul_self]
    simpa [nnnorm_star] using h_norm_sq
  exact (CStarAlgebra.nnnorm_le_one_iff_of_nonneg _ (mul_star_self_nonneg B)).1 h_norm_mul_star

/-! ### Positive definite case -/

/-- The commuting-dominant right bound for the **positive definite** case.
If `Dom` is PD, `[Dom, A] = 0`, and `A† A ≤ Dom`, then `A A† ≤ Dom`.

The proof sets `S = √Dom`, `X = A S⁻¹`, shows `X† X ≤ 1` by conjugation,
applies `contraction_conjTranspose` to obtain `X X† ≤ 1`, and then rewrites
`A A† = S (X X†) S ≤ S² = Dom`. -/
private lemma commuting_dominant_right_bound_posDef
    (A Dom : Mat) (hPD : Dom.PosDef) (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    A * Aᴴ ≤ Dom := by
  have hDom_nonneg : (0 : Mat) ≤ Dom := by
    rw [Matrix.le_iff]
    simpa using hPD.posSemidef
  let S : Mat := CFC.sqrt Dom
  have hS_sq : S * S = Dom := by
    simpa [S] using CFC.sqrt_mul_sqrt_self Dom hDom_nonneg
  have hS_selfAdjoint : IsSelfAdjoint S := by
    simpa [S] using (CFC.sqrt_nonneg (a := Dom)).isSelfAdjoint
  have hSA : Commute S A := by
    simpa [S] using hComm.cfcₙ_nnreal NNReal.sqrt
  obtain ⟨u, hu⟩ : ∃ u : Matˣ, (u : Mat) = S := by
    have hS_unit : IsUnit S := by
      dsimp [S]
      rw [CFC.isUnit_sqrt_iff Dom hDom_nonneg]
      exact hPD.isUnit
    simpa using hS_unit
  have hU_selfAdjoint : IsSelfAdjoint u := by
    refine Units.ext ?_
    simpa [hu] using hS_selfAdjoint.star_eq
  have hSi_selfAdjoint : IsSelfAdjoint (u⁻¹ : Matˣ) := hU_selfAdjoint.inv
  have hSi_star : star (↑u⁻¹ : Mat) = (↑u⁻¹ : Mat) :=
    congrArg (fun v : Matˣ => (v : Mat)) hSi_selfAdjoint.star_eq
  have hSiS : (↑u⁻¹ : Mat) * S = 1 := by rw [← hu]; simp
  have hSSi : S * (↑u⁻¹ : Mat) = 1 := by rw [← hu]; simp
  let X : Mat := A * (↑u⁻¹ : Mat)
  have hX_contr : Xᴴ * X ≤ 1 := by
    calc
      Xᴴ * X = star (↑u⁻¹ : Mat) * (Aᴴ * A) * (↑u⁻¹ : Mat) := by
        dsimp [X]
        rw [conjTranspose_mul,
          show ((↑u⁻¹ : Mat))ᴴ = star (↑u⁻¹ : Mat) from rfl, hSi_star]
        simp only [mul_assoc]
      _ ≤ star (↑u⁻¹ : Mat) * Dom * (↑u⁻¹ : Mat) :=
        star_left_conjugate_le_conjugate hDom (↑u⁻¹ : Mat)
      _ = 1 := by
        rw [hSi_star, ← hS_sq]
        calc (↑u⁻¹ : Mat) * (S * S) * (↑u⁻¹ : Mat) =
              ((↑u⁻¹ : Mat) * S) * (S * (↑u⁻¹ : Mat)) := by simp only [mul_assoc]
          _ = 1 := by rw [hSiS, hSSi]; simp only [one_mul]
  have hSX : S * X = A := by
    dsimp [X]
    calc S * (A * (↑u⁻¹ : Mat)) = A * S * (↑u⁻¹ : Mat) := by
          rw [← mul_assoc, hSA.eq, mul_assoc]
      _ = A := by simpa [mul_assoc] using congrArg (fun M : Mat => A * M) hSSi
  have hS_conjTranspose : Sᴴ = S := by simpa using hS_selfAdjoint.star_eq
  have hXstarS : Xᴴ * S = Aᴴ := by
    have hXstarS' : Xᴴ * Sᴴ = Aᴴ := by
      simpa [conjTranspose_mul] using congrArg Matrix.conjTranspose hSX
    simpa [hS_conjTranspose] using hXstarS'
  calc
    A * Aᴴ = S * (X * Xᴴ) * S := by
      calc A * Aᴴ = (S * X) * Aᴴ := by rw [hSX]
        _ = S * (X * Xᴴ) * S := by rw [← hXstarS]; simp only [mul_assoc]
    _ ≤ S * 1 * S := by
      simpa [hS_selfAdjoint.star_eq] using
        star_left_conjugate_le_conjugate (contraction_conjTranspose X hX_contr) S
    _ = Dom := by rw [mul_one, hS_sq]

/-! ### General PSD case -/

/-- `Dom.PosSemidef` implies `(Dom + ε • 1).PosDef` for `ε > 0`. -/
private lemma posDef_add_pos_smul_one (Dom : Mat) (hPSD : Dom.PosSemidef)
    (ε : ℝ) (hε : 0 < ε) :
    (Dom + (ε : ℂ) • (1 : Mat)).PosDef := by
  rw [add_comm]
  apply Matrix.PosDef.add_posSemidef _ hPSD
  have h1 : (ε : ℂ) • (1 : Mat) = (ε : ℝ) • (1 : Mat) := by
    ext i j; simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  rw [h1]
  exact Matrix.PosDef.one.smul hε

/-- If `B ≤ D + ε • 1` for all `ε > 0`, then `B ≤ D`.
This is the closedness of the PSD cone, applied to the differences
`D - B + ε • 1`. -/
private lemma le_of_forall_le_add_pos_smul_one (B D : Mat)
    (h : ∀ ε : ℝ, 0 < ε → B ≤ D + (ε : ℂ) • (1 : Mat)) :
    B ≤ D := by
  rw [Matrix.le_iff]
  let g : ℕ → Mat := fun n => (D - B) + ((1 / ((n : ℝ) + 1)) : ℝ) • (1 : Mat)
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds (D - B)) := by
    have hzero : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1)) : ℝ) • (1 : Mat))
        Filter.atTop (nhds (0 : Mat)) := by
      rw [show (0 : Mat) = (0 : ℝ) • (1 : Mat) from by simp]
      exact (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (1 : Mat))
    simpa [g, add_zero] using hzero.const_add (D - B)
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have h_smul : ((1 / ((n : ℝ) + 1)) : ℝ) • (1 : Mat) =
        ((((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) • (1 : Mat) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    have hg_eq : g n = (D + ((((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) • 1) - B := by
      change (D - B) + ((1 / ((n : ℝ) + 1)) : ℝ) • 1 = _
      rw [h_smul]
      abel
    rw [hg_eq, Matrix.le_iff]
    simpa using h (1 / ((n : ℝ) + 1)) (by positivity)
  simpa [Matrix.le_iff] using ge_of_tendsto' hg_tendsto hg_nonneg

/-- An operator is subnormal if it is the north-west block of a normal operator
on a larger space `H ⊕ H⊥`. -/
def IsSubnormal (A : Mat) : Prop :=
  ∃ E : ℕ,
    ∃ B : Matrix (Fin D) (Fin E) ℂ,
      ∃ C : Matrix (Fin E) (Fin E) ℂ,
        let N : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ := Matrix.fromBlocks A B 0 C
        Nᴴ * N = N * Nᴴ

private noncomputable def nwExtendLinearMap (T : Mat →ₗ[ℂ] Mat) (E : ℕ) :
    Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ →ₗ[ℂ]
      Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ where
  toFun := fun M => Matrix.fromBlocks (T (M.toBlocks₁₁)) 0 0 0
  map_add' := by
    intro M N
    have hAdd : T ((M + N).toBlocks₁₁) = T (M.toBlocks₁₁) + T (N.toBlocks₁₁) := by
      simpa [Matrix.toBlocks₁₁] using T.map_add M.toBlocks₁₁ N.toBlocks₁₁
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [hAdd]
  map_smul' := by
    intro c M
    have hSmul : T ((c • M).toBlocks₁₁) = c • T (M.toBlocks₁₁) := by
      simpa [Matrix.toBlocks₁₁] using T.map_smul c M.toBlocks₁₁
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [hSmul]

private lemma nwExtendLinearMap_isPositiveMap (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T) (E : ℕ) :
    IsPositiveMap (nwExtendLinearMap (D := D) T E) := by
  intro M hM
  refine Matrix.PosSemidef.fromBlocks_diag ?_ Matrix.PosSemidef.zero
  exact hPos _ (by simpa [Matrix.toBlocks₁₁, Matrix.submatrix_apply] using hM.submatrix Sum.inl)

private lemma nwExtendLinearMap_subunital (T : Mat →ₗ[ℂ] Mat)
    (hSub : T 1 ≤ (1 : Mat)) (E : ℕ) :
    nwExtendLinearMap (D := D) T E 1 ≤
      (1 : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ) := by
  rw [Matrix.le_iff]
  have hTop : (1 - T 1).PosSemidef := by
    simpa [Matrix.le_iff] using hSub
  have hDiag :
      (Matrix.fromBlocks (1 - T 1) 0 0 (1 : Matrix (Fin E) (Fin E) ℂ)).PosSemidef :=
    Matrix.PosSemidef.fromBlocks_diag hTop Matrix.PosSemidef.one
  have hOne11 : (1 : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ).toBlocks₁₁ = (1 : Mat) := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  have hEq : (1 : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ) - nwExtendLinearMap (D := D) T E 1 =
      Matrix.fromBlocks (1 - T 1) 0 0 (1 : Matrix (Fin E) (Fin E) ℂ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [nwExtendLinearMap, hOne11, Matrix.one_apply]
  simpa [hEq] using hDiag

/-- Wolf Thm. 5.5: Schwarz inequality for subnormal operators.

The intended proof composes the given positive subunital map with the north-west
block extraction map on a normal extension of `A`, then applies Wolf Prop. 5.1
(`schwarz_inequality_normal_operator`) to the resulting positive map. -/
private theorem topLeft_schwarz_of_normal_extension
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    {E : ℕ}
    (N : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ)
    (hNormal : Nᴴ * N = N * Nᴴ) :
    T (Nᴴ.toBlocks₁₁) * T (N.toBlocks₁₁) ≤ T ((Nᴴ * N).toBlocks₁₁) ∧
      T (N.toBlocks₁₁) * T (Nᴴ.toBlocks₁₁) ≤ T ((Nᴴ * N).toBlocks₁₁) := by
  classical
  let S : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ →ₗ[ℂ]
      Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ :=
    nwExtendLinearMap (D := D) T E
  have hPosS : IsPositiveMap S := nwExtendLinearMap_isPositiveMap (D := D) T hPos E
  have hSubS : S 1 ≤ (1 : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ) :=
    nwExtendLinearMap_subunital (D := D) T hSub E
  let e : (Fin D ⊕ Fin E) ≃ Fin (D + E) := finSumFinEquiv (m := D) (n := E)
  let ρ := Matrix.reindexLinearEquiv ℂ ℂ e e
  let Nf : Matrix (Fin (D + E)) (Fin (D + E)) ℂ := Matrix.reindex e e N
  let Sf : Matrix (Fin (D + E)) (Fin (D + E)) ℂ →ₗ[ℂ]
      Matrix (Fin (D + E)) (Fin (D + E)) ℂ :=
    ρ.toLinearMap.comp (S.comp ρ.symm.toLinearMap)
  have hPosSf : IsPositiveMap Sf := by
    intro M hM
    change (Matrix.reindex e e (S (Matrix.reindex e.symm e.symm M))).PosSemidef
    have hM' : (Matrix.reindex e.symm e.symm M).PosSemidef := by
      simpa [Matrix.reindex_apply] using hM.submatrix e
    have hSM : (S (Matrix.reindex e.symm e.symm M)).PosSemidef := hPosS _ hM'
    simpa using hSM.reindex e
  have hSubSf : Sf 1 ≤ (1 : Matrix (Fin (D + E)) (Fin (D + E)) ℂ) := by
    rw [Matrix.le_iff] at hSubS ⊢
    have hEq :
        (1 : Matrix (Fin (D + E)) (Fin (D + E)) ℂ) - Sf 1 =
          Matrix.reindex e e ((1 : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ) - S 1) := by
      ext i j
      simp [Sf, ρ, Matrix.reindexLinearEquiv_apply, Matrix.one_apply]
    simpa [hEq] using hSubS.reindex e
  have hNormalf : Nfᴴ * Nf = Nf * Nfᴴ := by
    change (Matrix.reindex e e N)ᴴ * Matrix.reindex e e N =
      Matrix.reindex e e N * (Matrix.reindex e e N)ᴴ
    calc
      (Matrix.reindex e e N)ᴴ * Matrix.reindex e e N =
          Matrix.reindex e e Nᴴ * Matrix.reindex e e N := by
            rw [Matrix.reindex_conjTranspose e N]
      _ = Matrix.reindex e e (Nᴴ * N) := by
        convert (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e Nᴴ N) using 1
      _ = Matrix.reindex e e (N * Nᴴ) := by rw [hNormal]
      _ = Matrix.reindex e e N * Matrix.reindex e e Nᴴ := by
        convert (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e N Nᴴ).symm using 1
      _ = Matrix.reindex e e N * (Matrix.reindex e e N)ᴴ := by
        rw [Matrix.reindex_conjTranspose e N]
  have hLeftf : (Sf (Nfᴴ * Nf) - Sf Nfᴴ * Sf Nf).PosSemidef :=
    schwarz_inequality_normal_operator (D := D + E) Sf hPosSf hSubSf Nf hNormalf
  have hLeftSum : (S (Nᴴ * N) - S Nᴴ * S N).PosSemidef := by
    have h :
        ((S (Nᴴ * N)).submatrix e.symm e.symm -
          (S Nᴴ * S N).submatrix e.symm e.symm).PosSemidef := by
      simpa [Sf, Nf, ρ, Matrix.reindex_conjTranspose e N,
        Matrix.reindexLinearEquiv_apply, Matrix.reindexLinearEquiv_mul,
        Matrix.submatrix_sub] using hLeftf
    simpa [Matrix.submatrix_submatrix, Matrix.submatrix_sub] using h.submatrix e
  have hRightf : (Sf ((Nfᴴ)ᴴ * Nfᴴ) - Sf (Nfᴴ)ᴴ * Sf Nfᴴ).PosSemidef := by
    have hNormalf' : (Nfᴴ)ᴴ * Nfᴴ = Nfᴴ * (Nfᴴ)ᴴ := by
      simpa using hNormalf.symm
    simpa using
      schwarz_inequality_normal_operator (D := D + E) Sf hPosSf hSubSf Nfᴴ hNormalf'
  have hRightSum : (S (N * Nᴴ) - S N * S Nᴴ).PosSemidef := by
    have h :
        ((S (N * Nᴴ)).submatrix e.symm e.symm -
          (S N * S Nᴴ).submatrix e.symm e.symm).PosSemidef := by
      simpa [Sf, Nf, ρ, Matrix.reindex_conjTranspose e N,
        Matrix.reindexLinearEquiv_apply, Matrix.reindexLinearEquiv_mul,
        conjTranspose_conjTranspose, Matrix.submatrix_sub] using hRightf
    simpa [Matrix.submatrix_submatrix, Matrix.submatrix_sub] using h.submatrix e
  refine ⟨?_, ?_⟩
  · rw [Matrix.le_iff]
    have hTop := hLeftSum.submatrix Sum.inl
    simpa [S, nwExtendLinearMap, Matrix.fromBlocks_multiply,
      Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.submatrix_sub] using hTop
  · rw [Matrix.le_iff]
    have hBlockEq : (N * Nᴴ).toBlocks₁₁ = (Nᴴ * N).toBlocks₁₁ := by
      simpa using congrArg Matrix.toBlocks₁₁ hNormal.symm
    have hEqTop :
        (S (N * Nᴴ) - S N * S Nᴴ).submatrix Sum.inl Sum.inl =
          T ((N * Nᴴ).toBlocks₁₁) - T (N.toBlocks₁₁) * T (Nᴴ.toBlocks₁₁) := by
      ext i j
      simp [S, nwExtendLinearMap, Matrix.fromBlocks_multiply,
        Matrix.toBlocks₁₁, Matrix.submatrix_apply]
    have hTop' := hRightSum.submatrix Sum.inl
    rw [hEqTop] at hTop'
    simpa [hBlockEq] using hTop'

theorem schwarz_inequality_subnormal_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A : Mat)
    (hSubnormal : IsSubnormal A) :
    T (Aᴴ) * T A ≤ T (Aᴴ * A) ∧ T A * T (Aᴴ) ≤ T (Aᴴ * A) := by
  rcases hSubnormal with ⟨E, B, C, hNormal⟩
  simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁] using
    topLeft_schwarz_of_normal_extension (D := D) T hPos hSub
      (Matrix.fromBlocks A B 0 C) hNormal

/-- Alias for `schwarz_inequality_subnormal_operator` matching Wolf Theorem 5.5. -/
alias wolf_theorem_5_5 := schwarz_inequality_subnormal_operator

/-- Linear-map wrapper for the canonical adjoint Kraus map.

This bundles `KadisonSchwarz.krausAdjointMap` from `KadisonSchwarz.lean` as a
linear map. It is convenient for reusing the generic positivity/monotonicity
API from `PositiveMapProperties`.

Note: `TNLean.Channel.Semigroup.Generator` contains an older duplicate
formula with the same name; inside `namespace KadisonSchwarz`, this wrapper
intentionally uses the canonical Schwarz-side definition. -/
noncomputable def krausAdjointMapLinear (K : Fin d → Mat) : Mat →ₗ[ℂ] Mat where
  toFun := krausAdjointMap K
  map_add' := by
    intro X Y
    simp [krausAdjointMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c X
    simp [krausAdjointMap, Finset.smul_sum, Matrix.mul_assoc]

/-- The adjoint Kraus map is positive. -/
private lemma krausAdjointMapLinear_isPositiveMap (K : Fin d → Mat) :
    IsPositiveMap (krausAdjointMapLinear (d := d) (D := D) K) := by
  intro X hX
  classical
  simpa [krausAdjointMapLinear, krausAdjointMap, Matrix.mul_assoc] using
    Matrix.posSemidef_sum (s := Finset.univ) (x := fun i => (K i)ᴴ * X * K i)
      (fun i _ => by
        simpa [Matrix.mul_assoc] using hX.mul_mul_conjTranspose_same (B := (K i)ᴴ))

/-- The missing order-theoretic step in Wolf Thm. 5.6: if `D ≥ 0` commutes with
`A` and dominates `Aᴴ * A`, then it also dominates `A * Aᴴ`.

Wolf proves this first for invertible `D` using `X = A D^{-1/2}`, and then passes
to the general case by replacing `D` with `D + ε • 1` and letting `ε → 0`.

The proof uses:
1. **Contraction lemma** (`contraction_conjTranspose`): `B† B ≤ 1 → B B† ≤ 1`
   via the C*-identity.
2. **CFC square root** and commutativity propagation for the invertible case.
3. **Approximation**: `D + ε I` is PD for `ε > 0`, and the result follows by
   letting `ε → 0`. -/
theorem commuting_dominant_right_bound
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    A * Aᴴ ≤ Dom := by
  apply le_of_forall_le_add_pos_smul_one _ _
  intro ε hε
  have hPD : (Dom + (ε : ℂ) • (1 : Mat)).PosDef :=
    posDef_add_pos_smul_one Dom hDomPos ε hε
  have hComm' : Commute (Dom + (ε : ℂ) • (1 : Mat)) A :=
    hComm.add_left ((Commute.one_left A).smul_left (ε : ℂ))
  have hDom' : Aᴴ * A ≤ Dom + (ε : ℂ) • (1 : Mat) :=
    hDom.trans <| le_add_of_nonneg_right <| by
      rw [Matrix.le_iff]
      simpa using (Matrix.PosSemidef.one (n := Fin D) (R := ℂ)).smul hε.le
  exact commuting_dominant_right_bound_posDef A _ hPD hComm' hDom'

/-- CP/Kraus version of Wolf Thm. 5.6 under both dominant bounds.

Once both inequalities `Aᴴ * A ≤ D` and `A * Aᴴ ≤ D` are available, the proof is
just Kadison--Schwarz for the adjoint Kraus map, followed by monotonicity of the
positive map `X ↦ ∑ᵢ Kᵢ† X Kᵢ`. -/
theorem kadison_schwarz_commuting_dominant_cp_of_two_sided_bound
    (K : Fin d → Mat)
    (h_tp : IsTPKraus K)
    (A Dom : Mat)
    (_hDomPos : Dom.PosSemidef)
    (_hComm : Commute Dom A)
    (hDomLeft : Aᴴ * A ≤ Dom)
    (hDomRight : A * Aᴴ ≤ Dom) :
    krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K Dom ∧
      krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K Dom := by
  let T : Mat →ₗ[ℂ] Mat := krausAdjointMapLinear (d := d) (D := D) K
  have hPosT : IsPositiveMap T := krausAdjointMapLinear_isPositiveMap (d := d) (D := D) K
  have hKSLeft' : (krausAdjointMap K A)ᴴ * krausAdjointMap K A ≤
      krausAdjointMap K (Aᴴ * A) := by
    rw [Matrix.le_iff]
    exact kadison_schwarz_adjoint K h_tp A
  have hKSLeft : krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤
      krausAdjointMap K (Aᴴ * A) := by
    simpa [krausAdjointMap_conjTranspose] using hKSLeft'
  have hDomLeftMap : krausAdjointMap K (Aᴴ * A) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomLeft
  have hKSRight' : (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [conjTranspose_conjTranspose] using
      (show (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤
          krausAdjointMap K ((Aᴴ)ᴴ * Aᴴ) from by
        rw [Matrix.le_iff]; exact kadison_schwarz_adjoint K h_tp (Aᴴ))
  have hKSRight : krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [krausAdjointMap_conjTranspose] using hKSRight'
  have hDomRightMap : krausAdjointMap K (A * Aᴴ) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomRight
  exact ⟨hKSLeft.trans hDomLeftMap, hKSRight.trans hDomRightMap⟩

/-- Wolf Thm. 5.6 in the CP/Kraus setting.

The only missing ingredient beyond `kadison_schwarz_commuting_dominant_cp_of_two_sided_bound`
is the right-dominance lemma `commuting_dominant_right_bound`. -/
theorem kadison_schwarz_commuting_dominant_cp
    (K : Fin d → Mat)
    (h_tp : IsTPKraus K)
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K Dom ∧
      krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K Dom := by
  have hDomRight : A * Aᴴ ≤ Dom :=
    commuting_dominant_right_bound (A := A) (Dom := Dom) hDomPos hComm hDom
  exact kadison_schwarz_commuting_dominant_cp_of_two_sided_bound
    (K := K) h_tp A Dom hDomPos hComm hDom hDomRight

private lemma intertwine_sqrt_of_mul_eq
    (P Q A : Mat)
    (hP : (0 : Mat) ≤ P)
    (hQ : (0 : Mat) ≤ Q)
    (hAQ : A * Q = P * A) :
    A * CFC.sqrt Q = CFC.sqrt P * A := by
  letI : CStarAlgebra (Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) :=
    { toNormedRing := Matrix.instL2OpNormedRing
      toStarRing := inferInstance
      toCompleteSpace := inferInstance
      toCStarRing := Matrix.instCStarRing
      toNormedAlgebra := Matrix.instL2OpNormedAlgebra
      toStarModule := inferInstance }
  let M : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ := Matrix.fromBlocks P 0 0 Q
  let K : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ := Matrix.fromBlocks 0 A 0 0
  let J : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ := Matrix.fromBlocks (1 : Mat) 0 0 0
  have hMK : Commute M K := by
    refine Commute.eq ?_
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [M, K, Matrix.fromBlocks_multiply, hAQ]
  have hMJ : Commute M J := by
    refine Commute.eq ?_
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [M, J, Matrix.fromBlocks_multiply]
  have hM_nonneg : (0 : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) ≤ M := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.PosSemidef.fromBlocks_diag
      ((Matrix.nonneg_iff_posSemidef).mp hP) ((Matrix.nonneg_iff_posSemidef).mp hQ)
  have hSJ : Commute (CFC.sqrt M) J := (Commute.cfcₙ_nnreal hMJ NNReal.sqrt)
  have hSK : Commute (CFC.sqrt M) K := (Commute.cfcₙ_nnreal hMK NNReal.sqrt)
  have h12 : (CFC.sqrt M).toBlocks₁₂ = 0 := by
    let S := CFC.sqrt M
    have h : (S * J).toBlocks₁₂ = (J * S).toBlocks₁₂ := by
      simpa using congrArg Matrix.toBlocks₁₂ hSJ.eq
    rw [show S = Matrix.fromBlocks S.toBlocks₁₁ S.toBlocks₁₂ S.toBlocks₂₁ S.toBlocks₂₂ from
      (Matrix.fromBlocks_toBlocks S).symm] at h
    simp [J, Matrix.fromBlocks_multiply] at h
    simpa using h.symm
  have h21 : (CFC.sqrt M).toBlocks₂₁ = 0 := by
    let S := CFC.sqrt M
    have h : (S * J).toBlocks₂₁ = (J * S).toBlocks₂₁ := by
      simpa using congrArg Matrix.toBlocks₂₁ hSJ.eq
    rw [show S = Matrix.fromBlocks S.toBlocks₁₁ S.toBlocks₁₂ S.toBlocks₂₁ S.toBlocks₂₂ from
      (Matrix.fromBlocks_toBlocks S).symm] at h
    simp [J, Matrix.fromBlocks_multiply] at h
    simpa using h
  have hSdecomp : CFC.sqrt M =
      Matrix.fromBlocks (CFC.sqrt M).toBlocks₁₁ 0 0 (CFC.sqrt M).toBlocks₂₂ := by
    simpa [h12, h21] using (Matrix.fromBlocks_toBlocks (CFC.sqrt M)).symm
  have hS_nonneg : (0 : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) ≤ CFC.sqrt M :=
    CFC.sqrt_nonneg (a := M)
  have hS_psd : (CFC.sqrt M).PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hS_nonneg
  have hS11_nonneg : (0 : Mat) ≤ (CFC.sqrt M).toBlocks₁₁ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [Matrix.toBlocks₁₁, Matrix.submatrix_apply] using hS_psd.submatrix Sum.inl
  have hS22_nonneg : (0 : Mat) ≤ (CFC.sqrt M).toBlocks₂₂ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [Matrix.submatrix_apply] using hS_psd.submatrix Sum.inr
  have hSq : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM_nonneg
  have h11sq : (CFC.sqrt M).toBlocks₁₁ * (CFC.sqrt M).toBlocks₁₁ = P := by
    have h := congrArg Matrix.toBlocks₁₁ hSq
    rw [hSdecomp, Matrix.fromBlocks_multiply] at h
    simpa [M] using h
  have h22sq : (CFC.sqrt M).toBlocks₂₂ * (CFC.sqrt M).toBlocks₂₂ = Q := by
    have h := congrArg Matrix.toBlocks₂₂ hSq
    rw [hSdecomp, Matrix.fromBlocks_multiply] at h
    simpa [M] using h
  have h11eq : CFC.sqrt P = (CFC.sqrt M).toBlocks₁₁ :=
    (CFC.sqrt_eq_iff P _ hP hS11_nonneg).2 h11sq
  have h22eq : CFC.sqrt Q = (CFC.sqrt M).toBlocks₂₂ :=
    (CFC.sqrt_eq_iff Q _ hQ hS22_nonneg).2 h22sq
  let S := CFC.sqrt M
  have h : (S * K).toBlocks₁₂ = (K * S).toBlocks₁₂ := congrArg Matrix.toBlocks₁₂ hSK.eq
  rw [show S = Matrix.fromBlocks S.toBlocks₁₁ S.toBlocks₁₂ S.toBlocks₂₁ S.toBlocks₂₂ from
    (Matrix.fromBlocks_toBlocks S).symm] at h
  simp [K, Matrix.fromBlocks_multiply] at h
  simpa [S, h11eq, h22eq] using h.symm

/-- Helper: the PD Schwarz inequality for commuting dominant operators.

This is proved by a normal dilation whose `NᴴN` top-left block is `Dom`. -/
private lemma schwarz_commuting_dominant_posDef
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A Dom : Mat)
    (hPD : Dom.PosDef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    T (Aᴴ) * T A ≤ T Dom ∧ T A * T (Aᴴ) ≤ T Dom := by
  let L : Mat := Dom - A * Aᴴ
  let R : Mat := Dom - Aᴴ * A
  have hRight : A * Aᴴ ≤ Dom :=
    commuting_dominant_right_bound_posDef A Dom hPD hComm hDom
  have hL_nonneg : (0 : Mat) ≤ L := by
    dsimp [L]
    exact sub_nonneg.mpr hRight
  have hR_nonneg : (0 : Mat) ≤ R := by
    dsimp [R]
    exact sub_nonneg.mpr hDom
  have hAQ : A * R = L * A := by
    dsimp [L, R]
    calc
      A * (Dom - Aᴴ * A) = A * Dom - A * (Aᴴ * A) := by rw [mul_sub]
      _ = Dom * A - (A * Aᴴ) * A := by rw [hComm.eq, ← mul_assoc]
      _ = (Dom - A * Aᴴ) * A := by
        rw [sub_mul]
  let DL : Mat := CFC.sqrt L
  let DR : Mat := CFC.sqrt R
  have hInter : A * DR = DL * A := by
    simpa [DL, DR] using intertwine_sqrt_of_mul_eq L R A hL_nonneg hR_nonneg hAQ
  have hDL_self : DLᴴ = DL := by
    simpa [DL, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg (a := L)).isSelfAdjoint.star_eq
  have hDR_self : DRᴴ = DR := by
    simpa [DR, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg (a := R)).isSelfAdjoint.star_eq
  have hInterAdj : DR * Aᴴ = Aᴴ * DL := by
    simpa [Matrix.conjTranspose_mul, hDL_self, hDR_self] using congrArg Matrix.conjTranspose hInter
  have hDL_sq : DL * DL = L := by
    simpa [DL] using CFC.sqrt_mul_sqrt_self L hL_nonneg
  have hDR_sq : DR * DR = R := by
    simpa [DR] using CFC.sqrt_mul_sqrt_self R hR_nonneg
  let N : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ := Matrix.fromBlocks A DL DR (-Aᴴ)
  have hNstar : Nᴴ = Matrix.fromBlocks Aᴴ DR DL (-A) := by
    simpa [N, hDL_self, hDR_self] using Matrix.fromBlocks_conjTranspose A DL DR (-Aᴴ)
  have hNstarN : Nᴴ * N = Matrix.fromBlocks Dom 0 0 Dom := by
    rw [hNstar]
    dsimp [N]
    rw [Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp [R, hDR_sq]
    · calc
        Aᴴ * DL + DR * (-Aᴴ) = Aᴴ * DL - DR * Aᴴ := by simp [sub_eq_add_neg]
        _ = 0 := by rw [hInterAdj]; simp
    · calc
        DL * A + (-A) * DR = DL * A - A * DR := by simp [sub_eq_add_neg]
        _ = 0 := by rw [hInter]; simp
    · simp [L, hDL_sq]
  have hNNstar : N * Nᴴ = Matrix.fromBlocks Dom 0 0 Dom := by
    dsimp [N]
    rw [hNstar, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp [L, hDL_sq]
    · calc
        A * DR + DL * (-A) = A * DR - DL * A := by simp [sub_eq_add_neg]
        _ = 0 := by rw [hInter]; simp
    · calc
        DR * Aᴴ + (-Aᴴ) * DL = DR * Aᴴ - Aᴴ * DL := by simp [sub_eq_add_neg]
        _ = 0 := by rw [hInterAdj]; simp
    · simp [R, hDR_sq]
  have hNormal : Nᴴ * N = N * Nᴴ := hNstarN.trans hNNstar.symm
  have hBlock := topLeft_schwarz_of_normal_extension (D := D) T hPos hSub N hNormal
  have hN11 : N.toBlocks₁₁ = A := by simp [N]
  have hNstar11 : Nᴴ.toBlocks₁₁ = Aᴴ := by rw [hNstar]; simp
  have hNstarN11 : (Nᴴ * N).toBlocks₁₁ = Dom := by rw [hNstarN]; simp
  simpa [hN11, hNstar11, hNstarN11] using hBlock

/-- Wolf Thm. 5.6: Schwarz inequality for commuting dominant operators.

If `T` is a positive subunital linear map, `D ≥ 0` commutes with `A`, and
`Aᴴ * A ≤ D`, then `T(Aᴴ) T(A) ≤ T(D)` and `T(A) T(Aᴴ) ≤ T(D)`.

The proof handles the positive definite case via a PSD decomposition and
`diagonal_family_schwarz_le`, then extends to general PSD `D` by
approximating with `D + ε · I` and letting `ε → 0`. -/
theorem schwarz_inequality_commuting_dominant_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    T (Aᴴ) * T A ≤ T Dom ∧ T A * T (Aᴴ) ≤ T Dom := by
  have hComm_add (ε : ℂ) : Commute (Dom + ε • 1) A :=
    hComm.add_left ((Commute.one_left A).smul_left ε)
  have hDom_add (ε : ℝ) (hε : 0 ≤ ε) : Aᴴ * A ≤ Dom + (ε : ℂ) • 1 :=
    hDom.trans <| le_add_of_nonneg_right <| by
      rw [Matrix.le_iff]
      simpa using (Matrix.PosSemidef.one (n := Fin D) (R := ℂ)).smul hε
  have hApprox : ∀ ε : ℝ, 0 < ε →
      T Aᴴ * T A ≤ T Dom + (ε : ℂ) • 1 ∧
        T A * T Aᴴ ≤ T Dom + (ε : ℂ) • 1 := by
    intro ε hε
    have hPD := posDef_add_pos_smul_one Dom hDomPos ε hε
    have hPD_result :=
      schwarz_commuting_dominant_posDef T hPos hSub A _ hPD (hComm_add (ε : ℂ))
        (hDom_add ε hε.le)
    refine ⟨?_, ?_⟩
    · calc T Aᴴ * T A ≤ T (Dom + (ε : ℂ) • 1) := hPD_result.1
        _ = T Dom + (ε : ℂ) • T 1 := by simp [map_add]
        _ ≤ T Dom + (ε : ℂ) • 1 := by gcongr
    · calc T A * T Aᴴ ≤ T (Dom + (ε : ℂ) • 1) := hPD_result.2
        _ = T Dom + (ε : ℂ) • T 1 := by simp [map_add]
        _ ≤ T Dom + (ε : ℂ) • 1 := by gcongr
  exact ⟨le_of_forall_le_add_pos_smul_one _ _ fun ε hε => (hApprox ε hε).1,
         le_of_forall_le_add_pos_smul_one _ _ fun ε hε => (hApprox ε hε).2⟩

/-- Alias for `schwarz_inequality_commuting_dominant_operator` matching Wolf Theorem 5.6. -/
alias wolf_theorem_5_6 := schwarz_inequality_commuting_dominant_operator

end KadisonSchwarz
