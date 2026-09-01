/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.TracePairing
import TNLean.MPS.ParentHamiltonian.FNWBoundaryConvention
import TNLean.MPS.ParentHamiltonian.FNWTransferDecay

/-!
# FNW boundary near-isometry

This module realizes the boundary map of Fannes--Nachtergaele--Werner,
*Communications in Mathematical Physics* 144 (1992), 443--490, equation (5.5),
as a continuous linear map from the matrix Hilbert space weighted by the
faithful stationary density to the ordinary physical Euclidean space.  In
TNLean coordinates, the source matrices satisfy \(A^\mu=v(\mu)^\dagger\).

The exact boundary recursion and scalar-product formula are equations (5.8),
and the resulting near-isometry estimate is equation (5.9).  Physical-site
reversal remains explicit through `FNWBoundaryConvention`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Physical-site reversal as an isometric equivalence of the standard physical
Euclidean space. -/
noncomputable def physicalSiteReverseES (d N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (physicalSiteReverseConfigEquiv d N)

@[simp]
theorem physicalSiteReverseES_apply
    (ψ : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    physicalSiteReverseES d N ψ σ = ψ (σ ∘ Fin.rev) := by
  rfl

/-- The FNW boundary map in TNLean coordinates \(A^\mu=v(\mu)^\dagger\), with
its source carrying the rho-weighted matrix norm and its target carrying the
ordinary physical Euclidean norm. -/
noncomputable def fnwBoundaryMapCLM
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    Mat →L[ℂ] EuclideanSpace ℂ (Cfg d N) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  exact LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap.comp
      (fnwBoundaryMap (fun μ => (A μ)ᴴ) N)

/-- Application of the continuous FNW boundary map is the raw boundary
coefficient function, viewed in the physical Euclidean space. -/
@[simp]
theorem fnwBoundaryMapCLM_apply
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ)
    (B : Mat) (σ : Cfg d N) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    fnwBoundaryMapCLM ρ hρ A N B σ =
      fnwBoundaryMap (fun μ => (A μ)ᴴ) N B σ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rfl

/-- The continuous FNW boundary map is the ordinary TNLean boundary map
followed by the isometric reversal of physical sites. -/
theorem fnwBoundaryMapCLM_eq_physicalSiteReverseES_comp
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    fnwBoundaryMapCLM ρ hρ A N =
      (physicalSiteReverseES d N).toLinearIsometry.toContinuousLinearMap.comp
        (LinearMap.toContinuousLinearMap <|
          (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap.comp
            (groundSpaceMap A N)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  apply ContinuousLinearMap.ext
  intro B
  ext σ
  simp only [fnwBoundaryMapCLM_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  have hraw := congrArg (fun f : NSiteSpace d N => f σ)
    (LinearMap.congr_fun
      (fnwBoundaryMap_eq_physicalSiteReverse_comp_groundSpaceMap
        (fun μ => (A μ)ᴴ) N) B)
  simpa using hraw

private theorem sum_tracePairing_evalWord
    (K : Fin d → Mat) (N : ℕ) (B C : Mat) :
    ∑ σ : Cfg d N,
        Matrix.trace (Bᴴ * Kraus.evalWord K (List.ofFn σ)) *
          star (Matrix.trace (Cᴴ * Kraus.evalWord K (List.ofFn σ))) =
      ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * (Kraus.mapLM K ^ N) (Matrix.single i k 1) * C) i k := by
  simp only [Kraus.mapLM_pow_apply]
  have hpush : ∀ (i k : Fin D),
      (Bᴴ * (∑ σ : Cfg d N,
        Kraus.evalWord K (List.ofFn σ) * Matrix.single i k (1 : ℂ) *
          (Kraus.evalWord K (List.ofFn σ))ᴴ) * C) i k =
      ∑ σ : Cfg d N,
        (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i *
          ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k := by
    intro i k
    have hdist : Bᴴ * (∑ σ : Cfg d N,
        Kraus.evalWord K (List.ofFn σ) * Matrix.single i k (1 : ℂ) *
          (Kraus.evalWord K (List.ofFn σ))ᴴ) * C =
        ∑ σ : Cfg d N,
          Bᴴ * Kraus.evalWord K (List.ofFn σ) * Matrix.single i k (1 : ℂ) *
            ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) := by
      rw [Matrix.mul_sum, Finset.sum_mul]
      congr 1
      ext σ
      simp only [Matrix.mul_assoc]
    rw [hdist, Matrix.sum_apply]
    congr 1
    ext σ
    exact Matrix.entry_mul_single_mul
      (Bᴴ * Kraus.evalWord K (List.ofFn σ))
      ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) i k
  simp_rw [hpush]
  rw [show (∑ i : Fin D, ∑ k : Fin D, ∑ σ : Cfg d N,
        (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i *
          ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k) =
      ∑ σ : Cfg d N, ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i *
          ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k from by
    simpa using Finset.sum_comm_cycle
      (s := (Finset.univ : Finset (Fin D)))
      (t := (Finset.univ : Finset (Fin D)))
      (u := (Finset.univ : Finset (Cfg d N)))
      (f := fun i k σ =>
        (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i *
          ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k)]
  congr 1
  ext σ
  rw [show (∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i *
          ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k) =
      (∑ i, (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i) *
        (∑ k, ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k) from by
    simpa using (Fintype.sum_mul_sum
      (f := fun i : Fin D => (Bᴴ * Kraus.evalWord K (List.ofFn σ)) i i)
      (g := fun k : Fin D => ((Kraus.evalWord K (List.ofFn σ))ᴴ * C) k k)).symm]
  change Matrix.trace (Bᴴ * Kraus.evalWord K (List.ofFn σ)) *
      star (Matrix.trace (Cᴴ * Kraus.evalWord K (List.ofFn σ))) =
    Matrix.trace (Bᴴ * Kraus.evalWord K (List.ofFn σ)) *
      Matrix.trace ((Kraus.evalWord K (List.ofFn σ))ᴴ * C)
  congr 1
  rw [← Matrix.trace_conjTranspose (Cᴴ * Kraus.evalWord K (List.ofFn σ))]
  simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

private theorem boundary_scalarProduct_formula
    (A : MPSTensor d D) (N : ℕ) (B C : Mat) :
    ∑ σ : Cfg d N,
        star (fnwBoundaryMap (fun μ => (A μ)ᴴ) N B σ) *
          fnwBoundaryMap (fun μ => (A μ)ᴴ) N C σ =
      ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * (fnwTransferMap A ^ N) (Matrix.single i k 1) * C) i k := by
  rw [show fnwTransferMap A = Kraus.mapLM (fun μ => (A μ)ᴴ) by rfl]
  rw [← sum_tracePairing_evalWord (fun μ => (A μ)ᴴ) N B C]
  congr 1
  ext σ
  rw [fnwBoundaryMap_apply, fnwBoundaryMap_apply]
  let V := Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn σ)
  have hB : star (Matrix.trace (B * Vᴴ)) = Matrix.trace (Bᴴ * V) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact Matrix.trace_mul_comm V Bᴴ
  have hC : Matrix.trace (C * Vᴴ) = star (Matrix.trace (Cᴴ * V)) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact Matrix.trace_mul_comm C Vᴴ
  exact congrArg₂ (· * ·) hB hC

/-- Exact scalar-product formula from FNW 1992, equation (5.8), in TNLean
coordinates \(A^\mu=v(\mu)^\dagger\). -/
theorem inner_fnwBoundaryMapCLM
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) (B C : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    inner ℂ (fnwBoundaryMapCLM ρ hρ A N B)
        (fnwBoundaryMapCLM ρ hρ A N C) =
      ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * (fnwTransferMap A ^ N) (Matrix.single i k 1) * C) i k := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rw [PiLp.inner_apply]
  simpa only [RCLike.inner_apply, starRingEnd_apply, fnwBoundaryMapCLM_apply,
    mul_comm] using boundary_scalarProduct_formula A N B C

private theorem fnwBoundaryMap_snoc
    (A : MPSTensor d D) (N : ℕ) (B : Mat) (μ : Fin d) (σ : Cfg d N) :
    fnwBoundaryMap (fun ν => (A ν)ᴴ) (N + 1) B (Fin.snoc σ μ) =
      fnwBoundaryMap (fun ν => (A ν)ᴴ) N (B * A μ) σ := by
  rw [fnwBoundaryMap_apply, fnwBoundaryMap_apply, List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [List.concat_eq_append, Kraus.evalWord_append]
  simp only [Kraus.evalWord, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_assoc]

/-- Exact boundary recursion from FNW 1992, equation (5.8), in TNLean
coordinates: adjoining the final physical index multiplies the boundary matrix
on the right by the corresponding \(A^\mu\). -/
theorem fnwBoundaryMapCLM_norm_sq_succ
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    ‖fnwBoundaryMapCLM ρ hρ A (N + 1) B‖ ^ 2 =
      ∑ μ : Fin d, ‖fnwBoundaryMapCLM ρ hρ A N (B * A μ)‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (N + 1) => Fin d))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro σ _
  change ‖fnwBoundaryMap (fun ν => (A ν)ᴴ) (N + 1) B
      (Fin.snoc σ μ)‖ ^ 2 =
    ‖fnwBoundaryMap (fun ν => (A ν)ᴴ) N (B * A μ) σ‖ ^ 2
  rw [fnwBoundaryMap_snoc]

end

end MPSTensor
