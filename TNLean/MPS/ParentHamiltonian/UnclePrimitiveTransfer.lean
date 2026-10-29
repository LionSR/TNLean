/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Channel.Peripheral.SpectralRadius
import QICLean.Channel.Peripheral.AdjointSpectrum
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Kraus.Injectivity
import QICLean.Kraus.Wielandt.Primitivity.EasyDirections
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive

/-!
# Exponential transfer convergence for the normalized uncle blocks

An injective unital block has primitive transfer dynamics. The actual
stationary trace functional defines its canonical rank-one projection;
subtracting that projection leaves spectral radius strictly below one.
Gelfand's formula then gives quantitative convergence of the actual
transfer powers. No convergence or spectral-gap hypothesis is added.

Source: arXiv:1210.6613, Lemma exptransferoperator, lines 1165–1175,
under the normalized standard form used in the gaplessness argument.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace MPSTensor

variable {d D : ℕ}

private noncomputable def uncleDensityFunctional (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (mulLeftLinearMap (n := Fin D) ℂ ρ)

private noncomputable def uncleDensityProjection (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  (uncleDensityFunctional ρ).smulRight 1

private theorem uncleDensityFunctional_one (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ = 1) : uncleDensityFunctional ρ 1 = 1 := by
  simp [uncleDensityFunctional, htr]

private theorem uncleDensityFunctional_map (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hfix : Kraus.adjointMap A ρ = ρ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    uncleDensityFunctional ρ (Kraus.mapLM A X) = uncleDensityFunctional ρ X := by
  change Matrix.trace (ρ * Kraus.mapLM A X) = Matrix.trace (ρ * X)
  rw [Kraus.mapLM_apply, Kraus.trace_mul_map_eq_trace_adjointMap_mul, hfix]

/-- Source block injectivity and unital normalization imply actual
peripheral primitivity; arXiv:1210.6613, Lemma exptransferoperator.
The trace-preserving bridge is applied to the adjoint family and then
transported back algebraically, with no adjoint norm comparison. -/
theorem uncleTransfer_isPrimitive_of_injective_unital [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hU : Kraus.mapLM A 1 = 1) :
    _root_.IsPrimitive (Kraus.mapLM A) := by
  classical
  let S := Submodule.span ℂ (Set.range fun i ↦ (A i)ᴴ)
  have hstar (Y : Matrix (Fin D) (Fin D) ℂ)
      (hY : Y ∈ Submodule.span ℂ (Set.range A)) : Yᴴ ∈ S := by
    induction hY using Submodule.span_induction with
    | mem Y hY =>
        obtain ⟨i, rfl⟩ := hY
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add X Y _ _ hX hY =>
        simpa only [Matrix.conjTranspose_add] using S.add_mem hX hY
    | smul c X _ hX =>
        simpa only [Matrix.conjTranspose_smul] using S.smul_mem (star c) hX
  have hspan : Kraus.wordSpan (fun i ↦ (A i)ᴴ) 1 = ⊤ := by
    rw [Kraus.wordSpan_one]
    apply Submodule.eq_top_iff'.mpr
    intro X
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hstar Xᴴ (by rw [hA.span_eq_top]; exact Submodule.mem_top)
  have hTP : Kraus.IsTP (fun i ↦ (A i)ᴴ) := by
    simpa only [Kraus.IsTP, Matrix.conjTranspose_conjTranspose,
      Kraus.mapLM_apply, Kraus.map_apply, Matrix.mul_one] using hU
  have hPrim := Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top
    (fun i ↦ (A i)ᴴ) hTP
    (fun φ hφ ↦ Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top _ hspan φ hφ)
  have hspec := Kraus.peripheralEigenvalues_mapLM_conjTranspose (fun i ↦ (A i)ᴴ)
  simp only [Matrix.conjTranspose_conjTranspose] at hspec
  rw [isPrimitive_iff] at hPrim ⊢
  rw [hspec, hPrim]
  simp

/-- Subtracting the actual canonical rank-one contraction from a source
injective unital transfer leaves spectral radius strictly below one.
Source: arXiv:1210.6613, Lemma exptransferoperator, lines 1165–1175. -/
theorem uncleTransfer_complement_spectralRadius_lt_one [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hU : Kraus.mapLM A 1 = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ = 1)
    (hfix : Kraus.adjointMap A ρ = ρ) :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
      (Kraus.mapLM A - ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
        (mulLeftLinearMap (n := Fin D) ℂ ρ)).smulRight 1)) < 1 := by
  let E := Kraus.mapLM A
  let f := uncleDensityFunctional ρ
  let P := uncleDensityProjection ρ
  have hf1 : f 1 = 1 := uncleDensityFunctional_one ρ htr
  have hfE (X) : f (E X) = f X := uncleDensityFunctional_map A ρ hfix X
  have hfP (X) : f (P X) = f X := by
    simp [P, uncleDensityProjection, f, hf1]
  have hPos : IsPositiveMap E := Kraus.isPositiveMap_mapLM A
  have hIrr : IsIrreducibleMap E := Kraus.injective_implies_irreducibleCP A hA
  have hPrim := uncleTransfer_isPrimitive_of_injective_unital A hA hU
  change spectralRadius ℂ ((Module.End.toContinuousLinearMap
    (Matrix (Fin D) (Fin D) ℂ)) (E - P)) < 1
  apply spectralRadius_lt_one_of_eigenvalues_lt_one
  intro ν hν
  obtain ⟨X, hX⟩ := hν.exists_hasEigenvector
  have hNX : (E - P) X = ν • X := Module.End.mem_eigenspace_iff.mp hX.1
  by_cases hfX : f X = 0
  · have hPX : P X = 0 := by simp [P, uncleDensityProjection, f, hfX]
    have hEX : E X = ν • X := by
      simpa only [LinearMap.sub_apply, hPX, sub_zero] using hNX
    have hEig : Module.End.HasEigenvalue E ν :=
      hasEigenvalue_of_eigenvector_eq E ν X hEX hX.2
    have hle : ‖ν‖ ≤ 1 := hPos.eigenvalue_norm_le_one_of_map_one_eq_one hU ν hEig
    by_contra hn
    have hnorm : ‖ν‖ = 1 := le_antisymm hle (le_of_not_gt hn)
    have hν1 : ν = 1 := hPrim.unique_peripheral ν hEig hnorm
    rw [hν1, one_smul] at hEX
    obtain ⟨c, hc⟩ := eigenvector_eq_smul_of_irreducible_positive E hPos hIrr zero_le_one
      (Matrix.PosDef.one (n := Fin D) (R := ℂ))
      (by simpa using hU) (by simpa using hEX)
    have hc0 : c = 0 := by simpa [hc, hf1] using hfX
    exact hX.2 (by rw [hc, hc0, zero_smul])
  · have heq := congrArg f hNX
    change f (E X - P X) = f (ν • X) at heq
    simp only [map_sub, map_smul, hfE, hfP, sub_self, smul_eq_mul] at heq
    have hν0 : ν = 0 := (mul_eq_zero.mp heq.symm).resolve_right hfX
    simp [hν0]

private theorem uncleTransfer_pow_decomposition
    (A : MPSTensor d D) (hU : Kraus.mapLM A 1 = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ = 1)
    (hfix : Kraus.adjointMap A ρ = ρ) (n : ℕ) :
    Kraus.mapLM A ^ (n + 1) = uncleDensityProjection ρ +
      (Kraus.mapLM A - uncleDensityProjection ρ) ^ (n + 1) := by
  let E := Kraus.mapLM A
  let P := uncleDensityProjection ρ
  let N := E - P
  have hf1 := uncleDensityFunctional_one ρ htr
  have hPP : P * P = P := by
    ext X
    simp [P, uncleDensityProjection, Module.End.mul_apply, hf1]
  have hPE : P * E = P := by
    ext X
    simp [P, E, uncleDensityProjection, Module.End.mul_apply,
      uncleDensityFunctional_map A ρ hfix]
  have hEP : E * P = P := by
    ext X
    simp [P, E, uncleDensityProjection, Module.End.mul_apply, hU]
  have hPN : P * N = 0 := by
    change P * (E - P) = 0
    rw [mul_sub, hPE, hPP, sub_self]
  have hNP : N * P = 0 := by
    change (E - P) * P = 0
    rw [sub_mul, hEP, hPP, sub_self]
  change E ^ (n + 1) = P + N ^ (n + 1)
  induction n with
  | zero => simp [N]
  | succ n ih =>
      have hpowP : N ^ (n + 1) * P = 0 := by
        rw [pow_succ, mul_assoc, hNP, mul_zero]
      rw [pow_succ, ih]
      conv_lhs => rhs; rw [show E = P + N by dsimp [N]; abel]
      simp only [add_mul, mul_add, hPP, hPN, hpowP, add_zero, zero_add, ← pow_succ]

/-- Actual source transfer powers converge geometrically to their
canonical weighted trace contraction. The strict complementary gap and
peripheral primitivity are derived from block injectivity and unitality,
not assumed. Source: arXiv:1210.6613, Lemma exptransferoperator. -/
theorem uncleTransfer_pow_sub_projection_bound [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hU : Kraus.mapLM A 1 = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ = 1)
    (hfix : Kraus.adjointMap A ρ = ρ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧
      ∀ n : ℕ, 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
        ‖((Kraus.mapLM A) ^ n) X - Matrix.trace (ρ * X) • 1‖ ≤ C * r ^ n * ‖X‖ := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let P := uncleDensityProjection ρ
  let N := Kraus.mapLM A - P
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  have hgap : spectralRadius ℂ (Φ N) < 1 :=
    uncleTransfer_complement_spectralRadius_lt_one A hA hU ρ htr hfix
  obtain ⟨C, r, hC, hr, hr1, hgeom⟩ :=
    geometric_apply_bound_of_spectralRadius_lt_one (Φ N) hgap
  refine ⟨C, r, hC, hr, hr1, fun n hn X ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hdecomp := uncleTransfer_pow_decomposition A hU ρ htr hfix m
  have hpow : ((Φ N) ^ (m + 1)) X = (N ^ (m + 1)) X :=
    congrArg (fun F : V →L[ℂ] V ↦ F X) (map_pow Φ N (m + 1)).symm
  have hbound := hgeom (m + 1) X
  rw [hpow] at hbound
  simpa only [hdecomp, LinearMap.add_apply, P, N, uncleDensityProjection,
    LinearMap.smulRight_apply, uncleDensityFunctional, LinearMap.comp_apply,
    Matrix.traceLinearMap_apply, mulLeftLinearMap_apply, add_sub_cancel_left] using hbound

end MPSTensor
