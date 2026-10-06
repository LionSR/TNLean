/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.MixedBoundaryGram
import TNLean.MPS.ParentHamiltonian.LocalObservableInsertion
import QICLean.Kraus.MixedMap.Gap
import QICLean.Analysis.OperatorNormConvergence
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Observable insertions between distinct MPS sectors

For two tensors, the rectangular insertion map of a local observable is
\(Y\mapsto\sum_{\sigma,\tau}X_{\sigma\tau}B_\tau Y A_\sigma^*\).
Its matrix entries give the observable pullback between the two boundary
maps. A strict mixed-transfer spectral radius implies that these pullbacks
decay when the free physical intervals grow.

These are intermediate distinct-sector estimates in the pure-GVBS argument
of Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint` and lines 2649--2675.
They do not assert an infinite-volume spectral gap.
-/

open Filter
open scoped BigOperators Matrix Topology Matrix.Norms.Operator InnerProductSpace

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

/-- The rectangular transfer insertion between a bra tensor and a ket tensor.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint`, equations
`ip`--`P12`, with a local observable inserted in the physical contraction. -/
noncomputable def mixedPhysicalObservableTransfer
    (B : MPSTensor d D₂) (A : MPSTensor d D₁) (k : ℕ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    Matrix (Fin D₂) (Fin D₁) ℂ →ₗ[ℂ] Matrix (Fin D₂) (Fin D₁) ℂ :=
  ∑ σ : Cfg d k, ∑ τ : Cfg d k, X τ σ •
    ((mulLeftLinearMap (n := Fin D₁) ℂ (Kraus.evalWord B (List.ofFn σ))).comp
      (mulRightLinearMap (l := Fin D₂) ℂ (Kraus.evalWord A (List.ofFn τ))ᴴ))

/-- Explicit physical contraction defining the rectangular insertion. -/
theorem mixedPhysicalObservableTransfer_apply
    (B : MPSTensor d D₂) (A : MPSTensor d D₁) (k : ℕ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (Y : Matrix (Fin D₂) (Fin D₁) ℂ) :
    mixedPhysicalObservableTransfer B A k X Y =
      ∑ σ : Cfg d k, ∑ τ : Cfg d k,
        X τ σ • (Kraus.evalWord B (List.ofFn σ) * Y * (Kraus.evalWord A (List.ofFn τ))ᴴ) := by
  simp [mixedPhysicalObservableTransfer, Matrix.mul_assoc]

/-- The diagonal mixed insertion is the usual single-tensor insertion.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem mixedPhysicalObservableTransfer_self {D : ℕ}
    (A : MPSTensor d D) (k : ℕ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    mixedPhysicalObservableTransfer A A k X = physicalObservableTransfer A k X := by
  exact LinearMap.ext fun Y ↦ by
    simp only [mixedPhysicalObservableTransfer_apply, physicalObservableTransfer_apply]

/-- Matrix-unit entries of a mixed physical observable pullback. Source:
Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint`, equations `ip`--`P12`. -/
theorem inner_single_mixed_observable_groundSpaceMapES_single
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (a b : Fin D₁) (c e : Fin D₂) :
    ⟪EuclideanSpace.single (b, a) 1,
      ((groundSpaceMapES A k).adjoint.comp
        ((Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X).comp
          (groundSpaceMapES B k))) (EuclideanSpace.single (e, c) 1)⟫_ℂ =
      mixedPhysicalObservableTransfer B A k X (Matrix.single c a 1) e b := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, groundSpaceMapES_single, groundSpaceMapES_single]
  change inner ℂ (WithLp.toLp 2 (groundSpaceMap A k (Matrix.single a b 1)))
    (Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X
      (WithLp.toLp 2 (groundSpaceMap B k (Matrix.single c e 1)))) = _
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
    mixedPhysicalObservableTransfer_apply, Finset.sum_comm]
  simp [groundSpaceMap_apply, Matrix.trace_mul_single, dotProduct,
    Matrix.mulVec, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.single_apply, ite_and, Finset.mul_sum, mul_comm, mul_assoc]

/-- Exact rectangular reshuffling of a mixed observable insertion into its
physical boundary pullback. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `disjoint`, equations `ip`--`P12`. -/
theorem adjoint_groundSpaceMapES_observable_groundSpaceMapES_eq_mixedTransfer
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    (groundSpaceMapES A k).adjoint.comp
      ((Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X).comp (groundSpaceMapES B k)) =
      (Matrix.toEuclideanLin
        (fun (b, a) (e, c) ↦ mixedPhysicalObservableTransfer B A k X
          (Matrix.single c a 1) e b)).toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin D₂ × Fin D₂) ℂ).toBasis.ext fun ⟨e, c⟩ ↦ ?_
  refine PiLp.ext fun ⟨b, a⟩ ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.coe_toContinuousLinearMap]
  change _ = ∑ j : Fin D₂ × Fin D₂,
    mixedPhysicalObservableTransfer B A k X (Matrix.single j.2 a 1) j.1 b *
      (EuclideanSpace.single (e, c) (1 : ℂ)) j
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.single, PiLp.single_apply]
    using inner_single_mixed_observable_groundSpaceMapES_single A B X a b c e

/-- Inserting the identity gives the ordinary mixed transfer power. Source:
Nachtergaele, arXiv:cond-mat/9410110, Lemma `disjoint`, equation `ip`. -/
theorem mixedPhysicalObservableTransfer_one
    (B : MPSTensor d D₂) (A : MPSTensor d D₁) (k : ℕ) :
    mixedPhysicalObservableTransfer B A k (1 : Matrix (Cfg d k) (Cfg d k) ℂ) =
      Kraus.mixedMapLM B A ^ k := by
  classical
  apply LinearMap.ext
  simp [mixedPhysicalObservableTransfer_apply, Kraus.mixedMapLM_pow_apply,
    Matrix.one_apply, ite_smul]

/-- Concatenation of physical observables composes their rectangular insertion
maps. Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
the ordered transfer contraction underlying Lemma `disjoint`. -/
theorem mixedPhysicalObservableTransfer_appendObservable
    (B : MPSTensor d D₂) (A : MPSTensor d D₁) {k l : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (Z : Matrix (Cfg d l) (Cfg d l) ℂ) :
    mixedPhysicalObservableTransfer B A (k + l) (appendObservable X Z) =
      mixedPhysicalObservableTransfer B A k X * mixedPhysicalObservableTransfer B A l Z := by
  classical
  have hsum : ∀ f : Cfg d (k + l) → Matrix (Fin D₂) (Fin D₁) ℂ,
      ∑ σ, f σ = ∑ σ₁ : Cfg d k, ∑ σ₂ : Cfg d l, f (Fin.append σ₁ σ₂) :=
    fun f ↦ by
      rw [← (Fin.appendEquiv k l).sum_comp, Fintype.sum_prod_type]
      rfl
  refine LinearMap.ext fun Y ↦ ?_
  rw [Module.End.mul_apply, mixedPhysicalObservableTransfer_apply, hsum]
  dsimp only [Cfg] at X Z hsum ⊢
  simp_rw [hsum, mixedPhysicalObservableTransfer_apply, appendObservable_append,
    List.ofFn_fin_append, Kraus.evalWord_append, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul, Matrix.mul_assoc]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- A fixed mixed insertion between free physical intervals is a sandwich of
mixed transfer powers. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `disjoint` and lines 2649--2675. -/
theorem mixedPhysicalObservableTransfer_bulkObservable
    (B : MPSTensor d D₂) (A : MPSTensor d D₁) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    mixedPhysicalObservableTransfer B A ((ℓ + k) + r) (bulkObservable X ℓ r) =
      (Kraus.mixedMapLM B A) ^ ℓ * mixedPhysicalObservableTransfer B A k X *
        (Kraus.mixedMapLM B A) ^ r := by
  rw [bulkObservable, mixedPhysicalObservableTransfer_appendObservable,
    mixedPhysicalObservableTransfer_appendObservable, mixedPhysicalObservableTransfer_one,
    mixedPhysicalObservableTransfer_one]

/-- Strict mixed spectral radius implies operator-norm convergence of the
rectangular transfer powers. This is the finite-dimensional decay step in
Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma `disjoint`. -/
theorem mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one
    (B : MPSTensor d D₂) (A : MPSTensor d D₁)
    (h : Kraus.mixedMapSpectralRadius B A < 1) :
    let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D₂) (Fin D₁) ℂ)
    Tendsto (fun n : ℕ ↦ Φ ((Kraus.mixedMapLM B A) ^ n)) atTop (nhds 0) := by
  exact ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional
    (fun Y ↦ Kraus.mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one B A h Y)

/-- Mixed observable sandwiches vanish when both free intervals grow and the
mixed spectral radius is strict. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `disjoint` and the distinct-sector estimates used in lines 2649--2675. -/
theorem mixedPhysicalObservableTransfer_sandwich_tendsto_zero
    (B : MPSTensor d D₂) (A : MPSTensor d D₁)
    (h : Kraus.mixedMapSpectralRadius B A < 1) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D₂) (Fin D₁) ℂ)
    Tendsto (fun n ↦ Φ ((Kraus.mixedMapLM B A) ^ ℓ n *
      mixedPhysicalObservableTransfer B A k X * (Kraus.mixedMapLM B A) ^ r n)) f
      (nhds 0) := by
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D₂) (Fin D₁) ℂ)
  simpa only [map_mul, zero_mul, mul_zero, Function.comp_def, Φ] using
    (((mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one B A h).comp hℓ).mul
      (tendsto_const_nhds (x := Φ (mixedPhysicalObservableTransfer B A k X)))).mul
        ((mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one B A h).comp hr)

/-- The boundary pullback of an interior observable is the rectangular
reshuffling of its mixed transfer sandwich. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `disjoint` and lines 2649--2675. -/
theorem adjoint_groundSpaceMapES_bulkObservable_groundSpaceMapES_eq_mixedTransfer
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    (groundSpaceMapES A ((ℓ + k) + r)).adjoint.comp
      ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)).comp (groundSpaceMapES B ((ℓ + k) + r))) =
      (Matrix.toEuclideanLin (fun (b, a) (e, c) ↦
        ((Kraus.mixedMapLM B A) ^ ℓ * mixedPhysicalObservableTransfer B A k X *
          (Kraus.mixedMapLM B A) ^ r) (Matrix.single c a 1) e b)).toContinuousLinearMap := by
  rw [adjoint_groundSpaceMapES_observable_groundSpaceMapES_eq_mixedTransfer,
    mixedPhysicalObservableTransfer_bulkObservable]

/-- Strict mixed spectral radius makes the pullback of a fixed interior
observable vanish in operator norm as both free intervals grow. This is an
intermediate distinct-sector estimate in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `disjoint` and lines 2649--2675. -/
theorem adjoint_groundSpaceMapES_bulkObservable_comp_tendsto_zero
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : Kraus.mixedMapSpectralRadius B A < 1) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n ↦ (groundSpaceMapES A ((ℓ n + k) + r n)).adjoint.comp
      ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
        (bulkObservable X (ℓ n) (r n))).comp
          (groundSpaceMapES B ((ℓ n + k) + r n)))) f (nhds 0) := by
  let F n := (Kraus.mixedMapLM B A) ^ ℓ n * mixedPhysicalObservableTransfer B A k X *
    (Kraus.mixedMapLM B A) ^ r n
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D₂) (Fin D₁) ℂ)
  have hF : Tendsto (fun n ↦ Φ (F n)) f (nhds 0) :=
    mixedPhysicalObservableTransfer_sandwich_tendsto_zero B A h X hℓ hr
  have hM : Tendsto (fun n ↦ fun (b, a) (e, c) ↦ F n (Matrix.single c a 1) e b) f
      (nhds (0 : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ)) := by
    refine tendsto_pi_nhds.mpr fun ⟨b, a⟩ ↦ tendsto_pi_nhds.mpr fun ⟨e, c⟩ ↦ ?_
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
      (((ContinuousLinearMap.apply ℂ (Matrix (Fin D₂) (Fin D₁) ℂ))
        (Matrix.single c a (1 : ℂ))).continuous.tendsto 0 |>.comp hF) e) b
  let S : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin D₂ × Fin D₂) →L[ℂ] EuclideanSpace ℂ (Fin D₁ × Fin D₁)) :=
    Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap
  have hlim := (S.toLinearMap.continuous_of_finiteDimensional.tendsto 0).comp hM
  rw [map_zero] at hlim
  change Tendsto (fun n ↦ (Matrix.toEuclideanLin
    (fun (b, a) (e, c) ↦ F n (Matrix.single c a 1) e b)).toContinuousLinearMap)
      f (nhds 0) at hlim
  simpa only [F, ← adjoint_groundSpaceMapES_bulkObservable_groundSpaceMapES_eq_mixedTransfer]
    using hlim

end MPSTensor
