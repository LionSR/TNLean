/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.FaithfulStationaryClosure
import TNLean.MPS.FundamentalTheorem.Reduction.Splitting

/-!
# Stationary splitting in the asymmetric fundamental theorem

Invariant-projector closure makes the source word module semisimple by giving
an orthogonal invariant complement to each invariant subspace. Left-canonical
normalization and a positive-definite stationary matrix provide that closure.
The asymmetric compression can therefore be chosen with zero remainder, and
its word reductions become sitewise intertwiners.

These are sufficient criteria with all additional channel hypotheses explicit.
They do not restate the unrestricted asymmetric theorem with those hypotheses
silently added. The analytic converse and the exclusion of zero factors are
proved separately in the stationary-semisimplicity note cited below.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix WordAlgebra
namespace MPSTensor
variable {d D : ℕ}

/-- Invariant-projector closure makes the word module semisimple: every invariant
subspace has its orthogonal complement as an invariant complement. This is the
algebraic consequence of CPSV16, lines 253--254, used in the splitting criterion
of the project asymmetric fundamental theorem (P5, Theorem 7.7). -/
theorem isSemisimpleModule_wordModule_of_hasInvariantProjectorClosure (B : MPSTensor d D)
    (hClosure : HasInvariantProjectorClosure B) :
    IsSemisimpleModule (WordAlgebra d) B.WordModule := by
  classical
  rw [isSemisimpleModule_iff]
  refine ⟨fun K => ?_⟩
  let E := EuclideanSpace ℂ (Fin D)
  let e : B.WordModule ≃ₗ[ℂ] E := B.wordRep.asModuleEquiv.trans
    (WithLp.linearEquiv 2 ℂ (Fin D → ℂ)).symm
  let p : Submodule ℂ E := (K.restrictScalars ℂ).map e.toLinearMap
  have heletter (i : Fin d) (v : B.WordModule) :
      e ((ofWord [i] : WordAlgebra d) • v) = Matrix.toEuclideanLin (B i) (e v) := by
    change WithLp.toLp 2 (B.wordRep.asModuleEquiv ((ofWord [i] : WordAlgebra d) • v)) =
      WithLp.toLp 2 (B i *ᵥ B.wordRep.asModuleEquiv v)
    exact congrArg (WithLp.toLp 2) (B.asModuleEquiv_letter_smul i v)
  have hinv (i : Fin d) {v : E} (hv : v ∈ p) : Matrix.toEuclideanLin (B i) v ∈ p := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨(ofWord [i] : WordAlgebra d) • w, K.smul_mem _ hw, heletter i w⟩
  let P : Matrix (Fin D) (Fin D) ℂ := Matrix.toEuclideanLin.symm p.starProjection.toLinearMap
  have hPlin : Matrix.toEuclideanLin P = p.starProjection.toLinearMap := by simp [P]
  have hmul (X Y : Matrix (Fin D) (Fin D) ℂ) :
      Matrix.toEuclideanLin (X * Y) =
        (Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y) :=
    Matrix.toLpLin_mul_same 2 X Y
  have hP : IsOrthogonalProjection P := by
    constructor
    · apply (Matrix.isSymmetric_toEuclideanLin_iff (A := P) (𝕜 := ℂ)).mp
      rw [hPlin]
      exact Submodule.starProjection_isSymmetric p
    · apply Matrix.toEuclideanLin.injective
      rw [hmul, hPlin]
      apply LinearMap.ext
      intro x
      exact (Submodule.starProjection_eq_self_iff).2 (by simp)
  have hAP (i : Fin d) : B i * P = P * B i * P := by
    apply Matrix.toEuclideanLin.injective
    rw [hmul, hmul, hmul, hPlin]
    apply LinearMap.ext
    intro x
    symm
    exact (Submodule.starProjection_eq_self_iff).2 (hinv i (by simp))
  have hLower (i : Fin d) : (1 - P) * B i * P = 0 := by
    calc
      (1 - P) * B i * P = B i * P - P * B i * P := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr (hAP i)
  have hComm := commutes_of_hasInvariantProjectorClosure_of_lowerZero B P hClosure hP hLower
  have hperp (i : Fin d) {v : E} (hv : v ∈ pᗮ) : Matrix.toEuclideanLin (B i) v ∈ pᗮ := by
    have hv0 : p.starProjection v = 0 := by
      have hv' : v ∈ p.starProjection.toLinearMap.ker := by
        rw [Submodule.ker_starProjection]
        exact hv
      exact hv'
    have h := congrArg (fun X => Matrix.toEuclideanLin X v) (hComm i)
    simp only [hmul, hPlin, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hv0,
      map_zero] at h
    rw [← Submodule.ker_starProjection]
    exact h
  let N : Submodule ℂ B.WordModule := pᗮ.comap e.toLinearMap
  have hN (i : Fin d) {v : B.WordModule} (hv : v ∈ N) :
      (ofWord [i] : WordAlgebra d) • v ∈ N := by
    change e ((ofWord [i] : WordAlgebra d) • v) ∈ pᗮ
    rw [heletter]
    exact hperp i hv
  refine ⟨submoduleOfLetterInvariant N (fun i v hv => hN i hv), ?_⟩
  rw [← Submodule.isCompl_restrictScalars_iff ℂ]
  have hK : K.restrictScalars ℂ = p.comap e.toLinearMap :=
    (Submodule.comap_map_eq_of_injective e.injective _).symm
  rw [hK]
  exact (Submodule.orderIsoMapComap e).symm.isCompl (Submodule.isCompl_orthogonal (K := p))

/-- A left-canonical tensor with a faithful stationary matrix has a semisimple
word module. This is the forward implication of the stationary-semisimplicity
criterion in `Notes/OpenProblemsTN/followup/2026_10_02_finite_asymmetric_tests/
stationary_semisimplicity.tex`, Theorem 1, using Wolf Proposition 6.11. -/
theorem isSemisimpleModule_wordModule_of_leftCanonical_of_posDef_fixedPoint
    (B : MPSTensor d D) (hB : IsLeftCanonical B)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map B ρ = ρ) : IsSemisimpleModule (WordAlgebra d) B.WordModule :=
  B.isSemisimpleModule_wordModule_of_hasInvariantProjectorClosure
    (B.hasInvariantProjectorClosure_of_leftCanonical_of_posDef_fixedPoint hB hρ hFix)

section Compression

variable {ι : Type*} [DecidableEq ι] {dim : ι → ℕ}

/-- A faithful stationary matrix splits a left-canonical source compression.
The periodic-character hypotheses are those of P5, Theorem 7.7; normalization
and faithful stationarity are additional sufficient splitting hypotheses, stated
explicitly in `stationary_semisimplicity.tex`, Corollary 2. -/
theorem exists_multiBlockCompression_remainder_eq_zero_of_leftCanonical_of_posDef_fixedPoint
    (S : Finset ι) (C : ∀ s, MPSTensor d (dim s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < dim s)
    (B : MPSTensor d D)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    (hB : IsLeftCanonical B) {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map B ρ = ρ) :
    ∃ P : MultiBlockCompression B S C, P.remainder = 0 := by
  have := B.isSemisimpleModule_wordModule_of_leftCanonical_of_posDef_fixedPoint hB hρ hFix
  exact exists_multiBlockCompression_remainder_eq_zero_of_isSemisimpleModule S C hC hD B htr

omit [DecidableEq ι] in
/-- A left-canonical source with a faithful stationary matrix admits two-sided
sitewise fusion tensors. This is the local-intertwiner consequence of the
stationary splitting criterion in `stationary_semisimplicity.tex`, Corollary 2;
it does not infer stationarity from periodic equality alone. -/
theorem exists_fusionTensors_of_leftCanonical_of_posDef_fixedPoint
    (S : Finset ι) (C : ∀ s, MPSTensor d (dim s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < dim s)
    (B : MPSTensor d D)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    (hB : IsLeftCanonical B) {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map B ρ = ρ) :
    ∃ (left : ∀ s : {s // s ∈ S}, Matrix (Fin (dim s.1)) (Fin D) ℂ)
      (right : ∀ s : {s // s ∈ S}, Matrix (Fin D) (Fin (dim s.1)) ℂ),
      (∀ s, MPSTensor.IsReduction B (C s.1) (left s) (right s)) ∧
      (∀ (i : Fin d) (s : {s // s ∈ S}), B i * right s = right s * C s.1 i) ∧
      (∀ (i : Fin d) (s : {s // s ∈ S}), left s * B i = C s.1 i * left s) ∧
      (∀ s t : {s // s ∈ S}, s ≠ t → left s * right t = 0) := by
  classical
  obtain ⟨P, hP⟩ :=
    exists_multiBlockCompression_remainder_eq_zero_of_leftCanonical_of_posDef_fixedPoint
      S C hC hD B htr hB hρ hFix
  exact ⟨P.left, P.right, P.isReduction, fun i s => P.mul_right_eq_right_mul hP i s,
    fun i s => P.left_mul_eq_mul_left hP i s, fun _ _ h => P.left_mul_right_of_ne h⟩

end Compression
end MPSTensor
