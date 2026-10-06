/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GramConvergence
import TNLean.MPS.Preparation.WindowCorrelator

/-!
# Local observable insertions in the MPS transfer map

For a local observable \(X\) on \(k\) sites, its insertion transfer map is
\[
  E_X(Y)=\sum_{\sigma,\tau}X_{\sigma\tau}A_\tau Y A_\sigma^*.
\]
For a normalized primitive tensor, the transfer powers on both sides of
this insertion converge to the rank-one fixed-point projection. Their
limiting sandwich is \(\eta_A(X)P_\rho\), where
\(\eta_A(X)=\operatorname{Tr}(E_X(\rho))/\operatorname{Tr}\rho\).

This is the transfer-map step in the pure-GVBS expectation limit used by
Nachtergaele, arXiv:cond-mat/9410110, lines 933--947 and 2649--2675.
The identities below identify the virtual insertion with the physical
boundary-map compression. Norm compression onto the full physical ground
space additionally uses the inverse-Gram estimates, developed separately.
-/

open Filter
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ}

/-- The limiting local expectation associated with the transfer invariant
matrix. Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b)
and lines 2649--2675. -/
noncomputable def observableInsertionExpectation (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) : ℂ :=
  Matrix.trace (physicalObservableTransfer A k X ρ) / Matrix.trace ρ

/-- The two rank-one limiting transfer projections reduce an insertion to its
scalar expectation. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 2649--2675, the pure-sector local expectation limit. -/
theorem fixedPointProj_physicalObservableTransfer_fixedPointProj
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    (fixedPointProj ρ htr).comp
      ((physicalObservableTransfer A k X).comp (fixedPointProj ρ htr)) =
      observableInsertionExpectation A ρ X • fixedPointProj ρ htr := by
  ext Y i j
  simp only [LinearMap.comp_apply, fixedPointProj, LinearMap.coe_mk, AddHom.coe_mk,
    map_smul, smul_eq_mul, Matrix.smul_apply,
    LinearMap.smul_apply, observableInsertionExpectation]
  ring

/-- The powers of a normalized primitive transfer map converge in operator norm
 to its rank-one fixed-point projection. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b) and Section 6. -/
theorem IsPrimitiveMPS.transferMap_pow_tendsto_fixedPointProj
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) :
    let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
    Tendsto (fun n : ℕ => Φ ((Kraus.transferMap A) ^ n)) atTop
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero))) := by
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
  have hlim : Tendsto (fun n : ℕ => Φ (fixedPointProj ρ hP.trace_ne_zero) +
      (Φ (Kraus.transferMap A - fixedPointProj ρ hP.trace_ne_zero)) ^ n) atTop
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero) + 0)) :=
    tendsto_const_nhds.add hP.complement_pow_tendsto_zero
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [pow_eq_fixedPointProj_add_compl_pow (Kraus.transferMap A) hP.trace_ne_zero
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hP.norm) hP.fixedPoint_is_fixed hn,
    map_add, map_pow]


/-- An observable insertion between two expanding primitive transfer intervals
converges to its scalar local expectation times the limiting transfer projection.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsPrimitiveMPS.physicalObservableTransfer_sandwich_tendsto
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
    Tendsto (fun n => Φ ((Kraus.transferMap A) ^ ℓ n *
      physicalObservableTransfer A k X * (Kraus.transferMap A) ^ r n)) f
      (nhds (observableInsertionExpectation A ρ X •
        Φ (fixedPointProj ρ hP.trace_ne_zero))) := by
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
  have hpow : Tendsto (fun n : ℕ => Φ ((Kraus.transferMap A) ^ n)) atTop
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero))) :=
    hP.transferMap_pow_tendsto_fixedPointProj
  have hleft : Tendsto (fun n => Φ ((Kraus.transferMap A) ^ ℓ n)) f
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero))) := hpow.comp hℓ
  have hright : Tendsto (fun n => Φ ((Kraus.transferMap A) ^ r n)) f
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero))) := hpow.comp hr
  have hconst : Tendsto (fun _ : ι => Φ (physicalObservableTransfer A k X)) f
      (nhds (Φ (physicalObservableTransfer A k X))) := tendsto_const_nhds
  have hlim : Tendsto (fun n => Φ ((Kraus.transferMap A) ^ ℓ n) *
      Φ (physicalObservableTransfer A k X) * Φ ((Kraus.transferMap A) ^ r n)) f
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero) *
        Φ (physicalObservableTransfer A k X) * Φ (fixedPointProj ρ hP.trace_ne_zero))) :=
    (hleft.mul hconst).mul hright
  have hlimit : Φ (fixedPointProj ρ hP.trace_ne_zero) *
      Φ (physicalObservableTransfer A k X) * Φ (fixedPointProj ρ hP.trace_ne_zero) =
      observableInsertionExpectation A ρ X • Φ (fixedPointProj ρ hP.trace_ne_zero) := by
    rw [← map_mul, ← map_mul]
    change Φ ((fixedPointProj ρ hP.trace_ne_zero).comp
      ((physicalObservableTransfer A k X).comp (fixedPointProj ρ hP.trace_ne_zero))) = _
    rw [fixedPointProj_physicalObservableTransfer_fixedPointProj, map_smul]
  simpa only [map_mul, hlimit] using hlim


/-- The boundary-map compression of a physical observable is exactly the Choi
reshuffling of its insertion transfer map. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b) and lines 2649--2675. -/
theorem adjoint_groundSpaceMapES_observable_groundSpaceMapES
    (A : MPSTensor d D) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    (groundSpaceMapES A k).adjoint.comp
      ((Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X).comp (groundSpaceMapES A k)) =
        Matrix.gramReshuffle (physicalObservableTransfer A k X) := by
  classical
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin D × Fin D) ℂ).toBasis.ext fun ⟨e, c⟩ => ?_
  apply PiLp.ext
  rintro ⟨b, a⟩
  have h : inner ℂ (EuclideanSpace.single (b, a) 1)
      (((groundSpaceMapES A k).adjoint.comp
        ((Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X).comp (groundSpaceMapES A k)))
          (EuclideanSpace.single (e, c) 1)) =
      Matrix.rectangularChoi (physicalObservableTransfer A k X) (c, e) (a, b) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.comp_apply, groundSpaceMapES_single, groundSpaceMapES_single]
    change inner ℂ (WithLp.toLp 2 (groundSpaceMap A k (Matrix.single a b 1)))
      (Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X
        (WithLp.toLp 2 (groundSpaceMap A k (Matrix.single c e 1)))) = _
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
      Matrix.rectangularChoi_apply, physicalObservableTransfer_apply, Finset.sum_comm]
    simp [groundSpaceMap_apply, Matrix.trace_mul_single, dotProduct,
      Matrix.mulVec, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.single_apply, ite_and, Finset.mul_sum,
      mul_comm, mul_assoc]
  have h' := h.trans
    (Matrix.inner_single_gramReshuffle_single (physicalObservableTransfer A k X) a b c e).symm
  simpa [PiLp.inner_apply] using h'


/-- A fixed observable supported between free physical intervals of lengths
\(\ell\) and \(r\). Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 933--947 and 2649--2675. -/
noncomputable def bulkObservable {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    Matrix (Cfg d ((ℓ + k) + r)) (Cfg d ((ℓ + k) + r)) ℂ :=
  appendObservable (appendObservable (1 : Matrix (Cfg d ℓ) (Cfg d ℓ) ℂ) X)
    (1 : Matrix (Cfg d r) (Cfg d r) ℂ)

/-- The transfer insertion of an interior observable has ordinary transfer
powers on both sides. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 2649--2675. -/
theorem physicalObservableTransfer_bulkObservable
    (A : MPSTensor d D) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    physicalObservableTransfer A ((ℓ + k) + r) (bulkObservable X ℓ r) =
      (Kraus.transferMap A) ^ ℓ * physicalObservableTransfer A k X *
        (Kraus.transferMap A) ^ r := by
  rw [bulkObservable, physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_appendObservable, physicalObservableTransfer_one,
    physicalObservableTransfer_one]

/-- Exact boundary compression of an interior observable. This identity and
primitive transfer convergence supply the tensor-specific scalarity estimate
required in the infinite-volume argument of Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem adjoint_groundSpaceMapES_bulkObservable_groundSpaceMapES
    (A : MPSTensor d D) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    (groundSpaceMapES A ((ℓ + k) + r)).adjoint.comp
      (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ))
        (bulkObservable X ℓ r)).comp (groundSpaceMapES A ((ℓ + k) + r))) =
      Matrix.gramReshuffle ((Kraus.transferMap A) ^ ℓ *
        physicalObservableTransfer A k X * (Kraus.transferMap A) ^ r) := by
  rw [adjoint_groundSpaceMapES_observable_groundSpaceMapES,
    physicalObservableTransfer_bulkObservable]


private noncomputable def transferReshuffleLinear :
    (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D)) :=
  by
    let R : (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) →ₗ[ℂ]
        Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
      { toFun := fun F p q => F (Matrix.single q.2 p.2 1) q.1 p.1
        map_add' := by intro F G; ext p q; rfl
        map_smul' := by intro c F; ext p q; rfl }
    let S := (Matrix.toEuclideanCLM (n := Fin D × Fin D) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv
    exact S.toLinearMap.comp R

private theorem transferReshuffleLinear_apply
    (F : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    transferReshuffleLinear F = Matrix.gramReshuffle F.toLinearMap := by
  unfold transferReshuffleLinear
  change Matrix.toEuclideanCLM (n := Fin D × Fin D) (𝕜 := ℂ)
    (fun p q => F (Matrix.single q.2 p.2 1) q.1 p.1) = _
  unfold Matrix.gramReshuffle
  congr 1
  ext p q
  simp [Matrix.gramReshuffleMatrix]

/-- The virtual Gram compression of a fixed interior observable converges to
its scalar expectation times the limiting boundary Gram operator. Both free
intervals may expand along any common filter. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsPrimitiveMPS.groundSpaceMapES_bulkObservable_compression_tendsto
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n => (groundSpaceMapES A ((ℓ n + k) + r n)).adjoint.comp
      (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
        (bulkObservable X (ℓ n) (r n))).comp
          (groundSpaceMapES A ((ℓ n + k) + r n)))) f
      (nhds (observableInsertionExpectation A ρ X •
        Matrix.gramReshuffle (fixedPointProj ρ hP.trace_ne_zero))) := by
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
  let S := (transferReshuffleLinear (D := D)).toContinuousLinearMap
  have htransfer : Tendsto (fun n => Φ ((Kraus.transferMap A) ^ ℓ n *
      physicalObservableTransfer A k X * (Kraus.transferMap A) ^ r n)) f
      (nhds (observableInsertionExpectation A ρ X •
        Φ (fixedPointProj ρ hP.trace_ne_zero))) :=
    hP.physicalObservableTransfer_sandwich_tendsto X hℓ hr
  have hlim : Tendsto (fun n => transferReshuffleLinear
      (Φ ((Kraus.transferMap A) ^ ℓ n * physicalObservableTransfer A k X *
        (Kraus.transferMap A) ^ r n))) f
      (nhds (transferReshuffleLinear (observableInsertionExpectation A ρ X •
        Φ (fixedPointProj ρ hP.trace_ne_zero)))) :=
    (S.continuous.tendsto _).comp htransfer
  have heq (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
      transferReshuffleLinear (Φ F) = Matrix.gramReshuffle F :=
    transferReshuffleLinear_apply (Φ F)
  have hscalar : transferReshuffleLinear (observableInsertionExpectation A ρ X •
      Φ (fixedPointProj ρ hP.trace_ne_zero)) = observableInsertionExpectation A ρ X •
        Matrix.gramReshuffle (fixedPointProj ρ hP.trace_ne_zero) := by
    exact (transferReshuffleLinear (D := D)).map_smul
      (observableInsertionExpectation A ρ X) (Φ (fixedPointProj ρ hP.trace_ne_zero)) |>.trans
        (congrArg (fun Z => observableInsertionExpectation A ρ X • Z) (heq _))
  rw [hscalar] at hlim
  have hreshaped : Tendsto (fun n => Matrix.gramReshuffle
      ((Kraus.transferMap A) ^ ℓ n * physicalObservableTransfer A k X *
        (Kraus.transferMap A) ^ r n)) f
      (nhds (observableInsertionExpectation A ρ X •
        Matrix.gramReshuffle (fixedPointProj ρ hP.trace_ne_zero))) :=
    hlim.congr' (Eventually.of_forall fun n => heq _)
  simpa only [adjoint_groundSpaceMapES_bulkObservable_groundSpaceMapES] using hreshaped

end MPSTensor
