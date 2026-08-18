/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram
import TNLean.MPS.ParentHamiltonian.SpectatorBoundary

/-!
# Hilbert-space spectator boundary maps and their Gram operators

This file realizes the spectator-indexed boundary maps in finite-dimensional
unweighted Frobenius/Euclidean coordinates. It records their physical ranges,
the exact virtual factorizations of the ordinary MPS boundary map, injectivity,
and the fiberwise Gram identities. No contraction estimate is asserted.

## Main definitions

* `tailBoundaryMapES` and `leftBoundaryMapES` are the Euclidean spectator maps.
* `tailVirtualMapES` and `leftVirtualMapES` are their virtual common-factorization maps.
* `boundaryFiberwiseMap` applies a virtual endomorphism independently on every fiber.
* `physicalReassocES` identifies the two parenthesizations of a three-block physical chain.
* `reassocTailBoundaryMapES` places a whole-increment tail map in the left-associated ambient
  chain.

## Main results

* `range_tailBoundaryMapES` and `range_leftBoundaryMapES_one` identify the physical ranges.
* `leftVirtualMapES_norm_map_of_leftCanonical` and
  `leftVirtualMapES_norm_le_one_of_leftCanonical` show that every whole-increment left virtual
  map is norm-preserving, hence has operator norm at most one.
* `physicalReassocES_comp_groundSpaceMapES` and
  `reassocTailBoundaryMapES_comp_tailVirtualMapES` give the reassociated full-map and tail-map
  factorizations.
* `whole_increment_injectiveRangeProjector_residual_eq` is the arbitrary-increment exact
  common-ambient identity; `c3_injectiveRangeProjector_residual_eq` is its one-site form.
* `tailVirtualMapES_adjoint_apply` and `leftVirtualMapES_adjoint_apply` compute the
  virtual-map adjoints.
* `norm_boundaryFiberwiseMap_le` bounds a fiberwise map uniformly in its spectator type.
* `tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram` and
  `leftBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram` identify the Grams.
* `inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram` and
  `inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram` identify the inverse Grams.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

open scoped Matrix.Norms.Frobenius

/-- Flattened Euclidean coordinates for a finite family of virtual matrices. -/
abbrev BoundaryFamilySpace (S : Type*) [Fintype S] :=
  EuclideanSpace ℂ (S × (Fin D × Fin D))

/-- The canonical linear equivalence between flattened Euclidean coordinates and a
finite family of matrices with the unweighted Frobenius coordinates. -/
noncomputable def boundaryFamilyEquiv (S : Type*) [Fintype S] :
    BoundaryFamilySpace (D := D) S ≃ₗ[ℂ] (S → Matrix (Fin D) (Fin D) ℂ) where
  toFun x s := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm
    (WithLp.toLp 2 fun p => x (s, p))
  invFun Y := WithLp.toLp 2 fun sp =>
    Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (Y sp.1) sp.2
  map_add' x y := by
    ext s a b
    simp
  map_smul' c x := by
    ext s a b
    simp
  left_inv x := by
    apply PiLp.ext
    rintro ⟨s, p⟩
    simp
  right_inv Y := by
    ext s a b
    simp

/-- Evaluation of `boundaryFamilyEquiv` at one family index. -/
@[simp]
theorem boundaryFamilyEquiv_apply_apply (S : Type*) [Fintype S]
    (x : BoundaryFamilySpace (D := D) S) (s : S) :
    boundaryFamilyEquiv (D := D) S x s =
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm
        (WithLp.toLp 2 fun p => x (s, p)) := rfl

/-- The tail spectator boundary map as a continuous map between Euclidean Hilbert spaces. -/
noncomputable def tailBoundaryMapES (A : MPSTensor d D) (K L : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg d K) →L[ℂ] EuclideanSpace ℂ (Cfg d (K + L)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm.toLinearMap.comp
      ((tailBoundaryMap A K L).comp (boundaryFamilyEquiv (D := D) (Cfg d K)).toLinearMap)

/-- The left spectator boundary map as a continuous map between Euclidean Hilbert spaces. -/
noncomputable def leftBoundaryMapES (A : MPSTensor d D) (K L : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg d L) →L[ℂ] EuclideanSpace ℂ (Cfg d (K + L)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm.toLinearMap.comp
      ((leftBoundaryMap A K L).comp (boundaryFamilyEquiv (D := D) (Cfg d L)).toLinearMap)

/-- Evaluation of the Euclidean tail boundary map in the underlying site-space coordinates. -/
@[simp]
theorem tailBoundaryMapES_apply (A : MPSTensor d D) (K L : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d K)) :
    tailBoundaryMapES A K L x =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm
        (tailBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d K) x)) := rfl

/-- Evaluation of the Euclidean left boundary map in the underlying site-space coordinates. -/
@[simp]
theorem leftBoundaryMapES_apply (A : MPSTensor d D) (K L : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d L)) :
    leftBoundaryMapES A K L x =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm
        (leftBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d L) x)) := rfl

/-- The Hilbert-space tail boundary map has exactly the open-chain tail ground space as range. -/
theorem range_tailBoundaryMapES (A : MPSTensor d D) (K L : ℕ) :
    (tailBoundaryMapES A K L).range = openChainTailGroundSpaceES A K L := by
  rw [← tailBoundaryMap_range_map_symm_eq_openChainTailGroundSpaceES A K L]
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨tailBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d K) x),
      ⟨boundaryFamilyEquiv (D := D) (Cfg d K) x, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨Y, rfl⟩, rfl⟩
    exact ⟨(boundaryFamilyEquiv (D := D) (Cfg d K)).symm Y, by simp⟩

/-- At suffix length one, the Hilbert-space left boundary map has exactly the
open-chain left ground space as range. -/
theorem range_leftBoundaryMapES_one (A : MPSTensor d D) (K : ℕ) :
    (leftBoundaryMapES A K 1).range = openChainLeftGroundSpaceES A K := by
  rw [← leftBoundaryMap_range_map_symm_eq_openChainLeftGroundSpaceES A K]
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨leftBoundaryMap A K 1 (boundaryFamilyEquiv (D := D) (Cfg d 1) x),
      ⟨boundaryFamilyEquiv (D := D) (Cfg d 1) x, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨Y, rfl⟩, rfl⟩
    exact ⟨(boundaryFamilyEquiv (D := D) (Cfg d 1)).symm Y, by simp⟩

/-! ### Virtual factorizations -/

/-- The virtual tail family before flattening, with fibers \(X A^u\). -/
private noncomputable def tailVirtualFamilyMap (A : MPSTensor d D) (K : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →ₗ[ℂ]
      (Cfg d K → Matrix (Fin D) (Fin D) ℂ) where
  toFun x u := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm x *
    evalWord A (List.ofFn u)
  map_add' x y := by
    funext u
    simp [Matrix.add_mul]
  map_smul' c x := by
    funext u
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Matrix.smul_mul]

/-- The virtual tail map with fibers \(X A^u\). -/
noncomputable def tailVirtualMapES (A : MPSTensor d D) (K : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d K) :=
  LinearMap.toContinuousLinearMap <|
    (boundaryFamilyEquiv (D := D) (Cfg d K)).symm.toLinearMap.comp
      (tailVirtualFamilyMap A K)

/-- The virtual left family before flattening, with fibers \(A^\tau X\). -/
private noncomputable def leftVirtualFamilyMap (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →ₗ[ℂ]
      (Cfg d L → Matrix (Fin D) (Fin D) ℂ) where
  toFun x τ := evalWord A (List.ofFn τ) *
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm x
  map_add' x y := by
    funext τ
    simp [Matrix.mul_add]
  map_smul' c x := by
    funext τ
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Matrix.mul_smul]

/-- The virtual left map with fibers \(A^\tau X\). -/
noncomputable def leftVirtualMapES (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d L) :=
  LinearMap.toContinuousLinearMap <|
    (boundaryFamilyEquiv (D := D) (Cfg d L)).symm.toLinearMap.comp
      (leftVirtualFamilyMap A L)

/-- A tail virtual vector has fiber \(X A^u\) at the prefix \(u\). -/
@[simp]
theorem boundaryFamilyEquiv_tailVirtualMapES_apply
    (A : MPSTensor d D) (K : ℕ) (x : EuclideanSpace ℂ (Fin D × Fin D))
    (u : Cfg d K) :
    boundaryFamilyEquiv (D := D) (Cfg d K) (tailVirtualMapES A K x) u =
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm x *
        evalWord A (List.ofFn u) := by
  change boundaryFamilyEquiv (D := D) (Cfg d K)
    ((boundaryFamilyEquiv (D := D) (Cfg d K)).symm (tailVirtualFamilyMap A K x)) u = _
  rw [(boundaryFamilyEquiv (D := D) (Cfg d K)).apply_symm_apply]
  rfl

/-- A left virtual vector has fiber \(A^\tau X\) at the suffix \(\tau\). -/
@[simp]
theorem boundaryFamilyEquiv_leftVirtualMapES_apply
    (A : MPSTensor d D) (L : ℕ) (x : EuclideanSpace ℂ (Fin D × Fin D))
    (τ : Cfg d L) :
    boundaryFamilyEquiv (D := D) (Cfg d L) (leftVirtualMapES A L x) τ =
      evalWord A (List.ofFn τ) *
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm x := by
  change boundaryFamilyEquiv (D := D) (Cfg d L)
    ((boundaryFamilyEquiv (D := D) (Cfg d L)).symm (leftVirtualFamilyMap A L x)) τ = _
  rw [(boundaryFamilyEquiv (D := D) (Cfg d L)).apply_symm_apply]
  rfl

/-- The adjoint of the tail virtual word map sums right-adjointed word
multiplication over the spectator fibers. -/
theorem tailVirtualMapES_adjoint_apply
    (A : MPSTensor d D) (K : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d K)) :
    (tailVirtualMapES A K).adjoint x =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (∑ u : Cfg d K,
          boundaryFamilyEquiv (D := D) (Cfg d K) x u *
            (evalWord A (List.ofFn u))ᴴ) := by
  apply ext_inner_left ℂ
  intro z
  obtain ⟨Z, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective z
  rw [ContinuousLinearMap.adjoint_inner_right,
    Matrix.inner_frobeniusEquivEuclidean, PiLp.inner_apply,
    Fintype.sum_prod_type]
  change (∑ u : Cfg d K, inner ℂ
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (Z * evalWord A (List.ofFn u)))
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (boundaryFamilyEquiv (D := D) (Cfg d K) x u))) = _
  simp only [Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  apply Finset.sum_congr rfl
  intro u _
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
    (evalWord A (List.ofFn u))ᴴ
    (Zᴴ * boundaryFamilyEquiv (D := D) (Cfg d K) x u)

/-- The adjoint of the left virtual word map sums left-adjointed word
multiplication over the spectator fibers. -/
theorem leftVirtualMapES_adjoint_apply
    (A : MPSTensor d D) (L : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d L)) :
    (leftVirtualMapES A L).adjoint x =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (∑ τ : Cfg d L,
          (evalWord A (List.ofFn τ))ᴴ *
            boundaryFamilyEquiv (D := D) (Cfg d L) x τ) := by
  apply ext_inner_left ℂ
  intro z
  obtain ⟨Z, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective z
  rw [ContinuousLinearMap.adjoint_inner_right,
    Matrix.inner_frobeniusEquivEuclidean, PiLp.inner_apply,
    Fintype.sum_prod_type]
  change (∑ τ : Cfg d L, inner ℂ
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (evalWord A (List.ofFn τ) * Z))
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (boundaryFamilyEquiv (D := D) (Cfg d L) x τ))) = _
  simp only [Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]

/-- For a left-canonical tensor, every fixed-length left virtual word map is an
isometry.  This is the uniform relation needed when the C3 filtration advances
by a whole block rather than by one input site. -/
theorem leftVirtualMapES_norm_map_of_leftCanonical
    (A : MPSTensor d D) (L : ℕ)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    ‖leftVirtualMapES A L x‖ = ‖x‖ := by
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  have hinner : inner ℂ
      (leftVirtualMapES A L
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X))
      (leftVirtualMapES A L
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
      inner ℂ
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X) := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    change (∑ τ : Cfg d L, inner ℂ
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (evalWord A (List.ofFn τ) * X))
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (evalWord A (List.ofFn τ) * X))) = _
    simp_rw [Matrix.inner_frobeniusEquivEuclidean, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
    rw [← Matrix.trace_sum]
    congr 1
    rw [← Matrix.mul_sum]
    simp_rw [← Matrix.mul_assoc]
    rw [← Matrix.sum_mul,
      sum_evalWord_conjTranspose_mul_evalWord A hLeft L]
    simp
  have hsquares : ‖leftVirtualMapES A L
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)‖ ^ 2 =
      ‖Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

/-- The norm of every fixed-length left virtual word map is uniformly at most one
for a left-canonical tensor. -/
theorem leftVirtualMapES_norm_le_one_of_leftCanonical
    (A : MPSTensor d D) (L : ℕ)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ‖leftVirtualMapES A L‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, leftVirtualMapES_norm_map_of_leftCanonical A L hLeft x]

/-- The ordinary Euclidean boundary map factors through the tail spectator map. -/
theorem tailBoundaryMapES_comp_tailVirtualMapES
    (A : MPSTensor d D) (K L : ℕ) :
    (tailBoundaryMapES A K L).comp (tailVirtualMapES A K) =
      groundSpaceMapES A (K + L) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm
      (tailBoundaryMap A K L
        (boundaryFamilyEquiv (D := D) (Cfg d K)
          (tailVirtualMapES A K
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)))) =
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm
      (groundSpaceMap A (K + L) X)
  refine congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm ?_
  have hfamily :
      boundaryFamilyEquiv (D := D) (Cfg d K)
          (tailVirtualMapES A K
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
        fun u => X * evalWord A (List.ofFn u) := by
    funext u
    rw [boundaryFamilyEquiv_tailVirtualMapES_apply,
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
  rw [hfamily, tailBoundaryMap_factorization]

/-- The ordinary Euclidean boundary map factors through the left spectator map. -/
theorem leftBoundaryMapES_comp_leftVirtualMapES
    (A : MPSTensor d D) (K L : ℕ) :
    (leftBoundaryMapES A K L).comp (leftVirtualMapES A L) =
      groundSpaceMapES A (K + L) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm
      (leftBoundaryMap A K L
        (boundaryFamilyEquiv (D := D) (Cfg d L)
          (leftVirtualMapES A L
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)))) =
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm
      (groundSpaceMap A (K + L) X)
  refine congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm ?_
  have hfamily :
      boundaryFamilyEquiv (D := D) (Cfg d L)
          (leftVirtualMapES A L
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
        fun τ => evalWord A (List.ofFn τ) * X := by
    funext τ
    rw [boundaryFamilyEquiv_leftVirtualMapES_apply,
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
  rw [hfamily, leftBoundaryMap_factorization]

/-! ### Injectivity -/

/-- Injectivity of the local length-\(L\) boundary map implies injectivity of the
tail spectator boundary map, including when the spectator configuration type is empty. -/
theorem tailBoundaryMapES_injective_of_groundSpaceMapES_injective
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A L)) :
    Function.Injective (tailBoundaryMapES A K L) := by
  intro x y hxy
  apply (boundaryFamilyEquiv (D := D) (Cfg d K)).injective
  funext u
  apply (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).injective
  apply h
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply]
  apply congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
  have hraw :
      tailBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d K) x) =
        tailBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d K) y) := by
    exact (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm.injective hxy
  simpa using congrArg (tailRestrictₗ u) hraw

/-- Injectivity of the local length-\(K\) boundary map implies injectivity of the
left spectator boundary map, including when the spectator configuration type is empty. -/
theorem leftBoundaryMapES_injective_of_groundSpaceMapES_injective
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A K)) :
    Function.Injective (leftBoundaryMapES A K L) := by
  intro x y hxy
  apply (boundaryFamilyEquiv (D := D) (Cfg d L)).injective
  funext τ
  apply (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).injective
  apply h
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply]
  apply congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d K)).symm
  have hraw :
      leftBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d L) x) =
        leftBoundaryMap A K L (boundaryFamilyEquiv (D := D) (Cfg d L) y) := by
    exact (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm.injective hxy
  simpa using congrArg (prefixRestrictₗ τ) hraw

/-! ### C3 overlapping-window projector identity -/

/-- Reassociate the physical configuration coordinates from \(K+(L+Q)\) sites to
\((K+L)+Q\) sites. -/
noncomputable def physicalReassocES (K L Q : ℕ) :
    EuclideanSpace ℂ (Cfg d (K + (L + Q))) ≃L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.arrowCongr (finCongr (Nat.add_assoc K L Q).symm)
      (Equiv.refl (Fin d)))).toContinuousLinearEquiv

/-- Reassociation is the identity when the suffix increment has length one. -/
theorem physicalReassocES_one (K L : ℕ) :
    physicalReassocES (d := d) K L 1 = 1 := by
  have hfin : finCongr (Nat.add_assoc K L 1).symm = Equiv.refl (Fin (K + L + 1)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact finCongr_apply_coe _ _
  have harrow :
      Equiv.arrowCongr (finCongr (Nat.add_assoc K L 1).symm) (Equiv.refl (Fin d)) =
        Equiv.refl (Cfg d (K + L + 1)) := by
    rw [hfin]
    rfl
  apply ContinuousLinearEquiv.coe_injective
  apply ContinuousLinearMap.ext
  intro v
  change LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.arrowCongr (finCongr (Nat.add_assoc K L 1).symm)
        (Equiv.refl (Fin d))) v = v
  rw [harrow]
  rfl

/-- Reassociation sends the length-\(K+(L+Q)\) ground-space map to the
length-\((K+L)+Q\) ground-space map in the common physical coordinates. -/
theorem physicalReassocES_comp_groundSpaceMapES
    (A : MPSTensor d D) (K L Q : ℕ) :
    (physicalReassocES (d := d) K L Q).toContinuousLinearMap.comp
        (groundSpaceMapES A (K + (L + Q))) =
      groundSpaceMapES A (K + L + Q) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply PiLp.ext
  intro σ
  have hword :
      List.ofFn (((finCongr (Nat.add_assoc K L Q)).arrowCongr
        (Equiv.refl (Fin d))) σ) = List.ofFn σ := by
    convert (List.ofFn_congr (m := K + L + Q) (n := K + (L + Q))
      (Nat.add_assoc K L Q) σ).symm using 1
    ext i
    rfl
  simp [physicalReassocES, groundSpaceMapES, groundSpaceMap_apply,
    Function.comp_def, hword]

/-- The tail window of length \(L+Q\), reassociated into the
\((K+L)+Q\)-site ambient Euclidean space. -/
noncomputable def reassocTailBoundaryMapES (A : MPSTensor d D) (K L Q : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg d K) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  (physicalReassocES (d := d) K L Q).toContinuousLinearMap.comp
    (tailBoundaryMapES A K (L + Q))

/-- A one-site suffix increment needs no physical-coordinate reassociation. -/
theorem reassocTailBoundaryMapES_one (A : MPSTensor d D) (K L : ℕ) :
    reassocTailBoundaryMapES A K L 1 = tailBoundaryMapES A K (L + 1) := by
  rw [reassocTailBoundaryMapES, physicalReassocES_one]
  rfl

/-- The reassociated tail map has the same whole-window factorization as the
left window with \(Q\) spectator sites. -/
theorem reassocTailBoundaryMapES_comp_tailVirtualMapES
    (A : MPSTensor d D) (K L Q : ℕ) :
    (reassocTailBoundaryMapES A K L Q).comp (tailVirtualMapES A K) =
      groundSpaceMapES A (K + L + Q) := by
  rw [reassocTailBoundaryMapES, ContinuousLinearMap.comp_assoc,
    tailBoundaryMapES_comp_tailVirtualMapES,
    physicalReassocES_comp_groundSpaceMapES]

/-- Exact common-ambient residual identity when the overlapping-window filtration
advances by an arbitrary suffix increment \(Q\). The tail window has length
\(L+Q\), the left window has length \(K+L\) with \(Q\) spectators, and the full
window has length \(K+L+Q\). Reassociation places all three maps in that last
Euclidean ambient space. This identity is algebraic and asserts no norm estimate. -/
theorem whole_increment_injectiveRangeProjector_residual_eq
    (A : MPSTensor d D) (K L Q : ℕ)
    (hTail : Function.Injective (reassocTailBoundaryMapES A K L Q))
    (hLeft : Function.Injective (leftBoundaryMapES A (K + L) Q))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    (ContinuousLinearMap.injectiveRangeProjector
        (reassocTailBoundaryMapES A K L Q) hTail).comp
        (ContinuousLinearMap.injectiveRangeProjector
          (leftBoundaryMapES A (K + L) Q) hLeft) -
      ContinuousLinearMap.injectiveRangeProjector
        (groundSpaceMapES A (K + L + Q)) hFull =
        (reassocTailBoundaryMapES A K L Q).comp
          ((ContinuousLinearMap.inverseGram
            (reassocTailBoundaryMapES A K L Q) hTail).comp
            (((reassocTailBoundaryMapES A K L Q).adjoint.comp
                (leftBoundaryMapES A (K + L) Q) -
              ((reassocTailBoundaryMapES A K L Q).adjoint.comp
                (reassocTailBoundaryMapES A K L Q)).comp
                ((tailVirtualMapES A K).comp
                  ((ContinuousLinearMap.inverseGram
                    (groundSpaceMapES A (K + L + Q)) hFull).comp
                    ((leftVirtualMapES A Q).adjoint.comp
                      ((leftBoundaryMapES A (K + L) Q).adjoint.comp
                        (leftBoundaryMapES A (K + L) Q)))))).comp
              ((ContinuousLinearMap.inverseGram
                (leftBoundaryMapES A (K + L) Q) hLeft).comp
                (leftBoundaryMapES A (K + L) Q).adjoint))) :=
  ContinuousLinearMap.injectiveRangeProjector_comp_sub_of_factorizations
    (T := reassocTailBoundaryMapES A K L Q)
    (L := leftBoundaryMapES A (K + L) Q)
    (C := groundSpaceMapES A (K + L + Q))
    (J₁ := tailVirtualMapES A K) (J₂ := leftVirtualMapES A Q)
    hTail hLeft hFull
    (reassocTailBoundaryMapES_comp_tailVirtualMapES A K L Q)
    (leftBoundaryMapES_comp_leftVirtualMapES A (K + L) Q)

/-- Exact C3-window specialization of the common-factorization projector residual.
The three ranges are, respectively, the open-chain tail space for \((K,L₀+1)\),
the open-chain left space for \(K+L₀\), and the full \((K+L₀+1)\)-site MPS
ground space, by `range_tailBoundaryMapES`, `range_leftBoundaryMapES_one`, and
`range_groundSpaceMapES`. All three map injectivity assumptions are explicit.
This identity is purely algebraic and asserts no norm estimate. -/
theorem c3_injectiveRangeProjector_residual_eq
    (A : MPSTensor d D) (K L₀ : ℕ)
    (hTail : Function.Injective (tailBoundaryMapES A K (L₀ + 1)))
    (hLeft : Function.Injective (leftBoundaryMapES A (K + L₀) 1))
    (hFull : Function.Injective (groundSpaceMapES A (K + L₀ + 1))) :
    (ContinuousLinearMap.injectiveRangeProjector
        (tailBoundaryMapES A K (L₀ + 1)) hTail).comp
        (ContinuousLinearMap.injectiveRangeProjector
          (leftBoundaryMapES A (K + L₀) 1) hLeft) -
      ContinuousLinearMap.injectiveRangeProjector
        (groundSpaceMapES A (K + L₀ + 1)) hFull =
        (tailBoundaryMapES A K (L₀ + 1)).comp
          ((ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (L₀ + 1)) hTail).comp
            (((tailBoundaryMapES A K (L₀ + 1)).adjoint.comp
                (leftBoundaryMapES A (K + L₀) 1) -
              ((tailBoundaryMapES A K (L₀ + 1)).adjoint.comp
                (tailBoundaryMapES A K (L₀ + 1))).comp
                ((tailVirtualMapES A K).comp
                  ((ContinuousLinearMap.inverseGram
                    (groundSpaceMapES A (K + L₀ + 1)) hFull).comp
                    ((leftVirtualMapES A 1).adjoint.comp
                      ((leftBoundaryMapES A (K + L₀) 1).adjoint.comp
                        (leftBoundaryMapES A (K + L₀) 1)))))).comp
              ((ContinuousLinearMap.inverseGram
                (leftBoundaryMapES A (K + L₀) 1) hLeft).comp
                (leftBoundaryMapES A (K + L₀) 1).adjoint))) :=
  ContinuousLinearMap.injectiveRangeProjector_comp_sub_of_factorizations
    (T := tailBoundaryMapES A K (L₀ + 1))
    (L := leftBoundaryMapES A (K + L₀) 1)
    (C := groundSpaceMapES A (K + L₀ + 1))
    (J₁ := tailVirtualMapES A K) (J₂ := leftVirtualMapES A 1)
    hTail hLeft hFull
    (tailBoundaryMapES_comp_tailVirtualMapES A K (L₀ + 1))
    (leftBoundaryMapES_comp_leftVirtualMapES A (K + L₀) 1)

/-! ### Fiberwise Gram identities -/

/-- The Euclidean virtual-matrix fiber at a spectator configuration. -/
noncomputable def boundaryFamilyFiber {S : Type*} [Fintype S]
    (x : BoundaryFamilySpace (D := D) S) (s : S) :
    EuclideanSpace ℂ (Fin D × Fin D) :=
  WithLp.toLp 2 fun p => x (s, p)

/-- A flattened family fiber is the Frobenius coordinate vector of the
corresponding matrix in `boundaryFamilyEquiv`. -/
theorem boundaryFamilyFiber_eq_frobeniusEquivEuclidean
    {S : Type*} [Fintype S]
    (x : BoundaryFamilySpace (D := D) S) (s : S) :
    boundaryFamilyFiber (D := D) x s =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (boundaryFamilyEquiv (D := D) S x s) := by
  rw [boundaryFamilyEquiv_apply_apply,
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).apply_symm_apply]
  rfl

/-- Apply an endomorphism independently to every virtual-matrix fiber. -/
noncomputable def boundaryFiberwiseMap (S : Type*) [Fintype S]
    (G : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D)) :
    BoundaryFamilySpace (D := D) S →L[ℂ] BoundaryFamilySpace (D := D) S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun sp => G (boundaryFamilyFiber (D := D) x sp.1) sp.2
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨s, p⟩
        change (G (boundaryFamilyFiber (D := D) (x + y) s)) p = _
        rw [show boundaryFamilyFiber (D := D) (x + y) s =
            boundaryFamilyFiber (D := D) x s + boundaryFamilyFiber (D := D) y s by
          apply PiLp.ext
          intro q
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨s, p⟩
        change (G (boundaryFamilyFiber (D := D) (c • x) s)) p = _
        rw [show boundaryFamilyFiber (D := D) (c • x) s =
            c • boundaryFamilyFiber (D := D) x s by
          apply PiLp.ext
          intro q
          rfl, map_smul]
        rfl }

/-- Evaluation of a fiberwise map at one family and matrix index. -/
@[simp]
theorem boundaryFiberwiseMap_apply_apply (S : Type*) [Fintype S]
    (G : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D))
    (x : BoundaryFamilySpace (D := D) S) (s : S) (p : Fin D × Fin D) :
    boundaryFiberwiseMap (D := D) S G x (s, p) =
      G (boundaryFamilyFiber (D := D) x s) p := rfl

/-- The fiber of a fiberwise map is the original fiber acted on by the
virtual endomorphism. -/
@[simp]
private theorem boundaryFamilyFiber_boundaryFiberwiseMap
    (S : Type*) [Fintype S]
    (G : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D))
    (x : BoundaryFamilySpace (D := D) S) (s : S) :
    boundaryFamilyFiber (D := D) (boundaryFiberwiseMap (D := D) S G x) s =
      G (boundaryFamilyFiber (D := D) x s) := by
  apply PiLp.ext
  intro p
  rfl

/-- In matrix coordinates, a fiberwise map acts on the Frobenius coordinate
vector of each matrix fiber. -/
@[simp]
theorem boundaryFamilyEquiv_boundaryFiberwiseMap_apply
    (S : Type*) [Fintype S]
    (G : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D))
    (x : BoundaryFamilySpace (D := D) S) (s : S) :
    boundaryFamilyEquiv (D := D) S
        (boundaryFiberwiseMap (D := D) S G x) s =
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm
        (G (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
          (boundaryFamilyEquiv (D := D) S x s))) := by
  apply (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).injective
  rw [(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).apply_symm_apply,
    ← boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
    boundaryFamilyFiber_boundaryFiberwiseMap,
    boundaryFamilyFiber_eq_frobeniusEquivEuclidean]

/-- Fiberwise maps preserve composition. -/
theorem boundaryFiberwiseMap_comp (S : Type*) [Fintype S]
    (G H : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D)) :
    (boundaryFiberwiseMap (D := D) S G).comp (boundaryFiberwiseMap (D := D) S H) =
      boundaryFiberwiseMap (D := D) S (G.comp H) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply PiLp.ext
  rintro ⟨s, p⟩
  rfl

/-- The fiberwise identity is the identity on the flattened family space. -/
theorem boundaryFiberwiseMap_id (S : Type*) [Fintype S] :
    boundaryFiberwiseMap (D := D) S (ContinuousLinearMap.id ℂ _) =
      ContinuousLinearMap.id ℂ (BoundaryFamilySpace (D := D) S) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply PiLp.ext
  rintro ⟨s, p⟩
  rfl

/-- Inner products against a fiberwise map split exactly as a finite direct sum. -/
theorem inner_boundaryFiberwiseMap (S : Type*) [Fintype S]
    (G : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D))
    (x y : BoundaryFamilySpace (D := D) S) :
    inner ℂ y (boundaryFiberwiseMap (D := D) S G x) =
      ∑ s : S, inner ℂ (boundaryFamilyFiber (D := D) y s)
        (G (boundaryFamilyFiber (D := D) x s)) := by
  rw [PiLp.inner_apply]
  simp only [boundaryFiberwiseMap_apply_apply, Fintype.sum_prod_type,
    boundaryFamilyFiber, PiLp.inner_apply]

/-- Applying the same operator independently on each boundary fiber does not
increase its operator norm. This estimate is uniform in the finite spectator
type and remains valid when that type is empty. -/
theorem norm_boundaryFiberwiseMap_le (S : Type*) [Fintype S]
    (G : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D)) :
    ‖boundaryFiberwiseMap (D := D) S G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg x)),
    mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ sp : S × (Fin D × Fin D),
        ‖boundaryFiberwiseMap (D := D) S G x sp‖ ^ 2 =
        ∑ s, ∑ p, ‖G (boundaryFamilyFiber (D := D) x s) p‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ s, ‖G (boundaryFamilyFiber (D := D) x s)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ s, (‖G‖ * ‖boundaryFamilyFiber (D := D) x s‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg G) (norm_nonneg _))).mpr (G.le_opNorm _)
    _ = ‖G‖ ^ 2 * ∑ sp : S × (Fin D × Fin D), ‖x sp‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [boundaryFamilyFiber, Finset.mul_sum]

/-- The tail Gram is the direct sum, over prefix spectators, of copies of the
length-`L` MPS Gram. This bilinear identity remains valid for empty spectator types. -/
theorem inner_tailBoundaryMapES_adjoint_comp_self
    (A : MPSTensor d D) (K L : ℕ)
    (x y : BoundaryFamilySpace (D := D) (Cfg d K)) :
    inner ℂ y ((tailBoundaryMapES A K L).adjoint (tailBoundaryMapES A K L x)) =
      ∑ u : Cfg d K, inner ℂ (boundaryFamilyFiber (D := D) y u)
        (groundSpaceGram A L (boundaryFamilyFiber (D := D) x u)) := by
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  trans ∑ p : Cfg d K × Cfg d L,
      inner ℂ ((tailBoundaryMapES A K L y) (Fin.appendEquiv K L p))
        ((tailBoundaryMapES A K L x) (Fin.appendEquiv K L p))
  · symm
    apply Fintype.sum_equiv (Fin.appendEquiv K L)
    intro p
    rfl
  · simp only [Fin.appendEquiv, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    rw [groundSpaceGram, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro τ _
    have hp : Fin.append u τ ∘ Fin.castAdd L = u := by
      ext i
      simp [Fin.append_left]
    have hs : Fin.append u τ ∘ Fin.natAdd K = τ := by
      ext i
      simp [Fin.append_right]
    simp [boundaryFamilyFiber, tailBoundaryMapES, groundSpaceMapES,
      groundSpaceMap_apply, hp, hs]

/-- The left Gram is the direct sum, over suffix spectators, of copies of the
length-`K` MPS Gram. This bilinear identity remains valid for empty spectator types. -/
theorem inner_leftBoundaryMapES_adjoint_comp_self
    (A : MPSTensor d D) (K L : ℕ)
    (x y : BoundaryFamilySpace (D := D) (Cfg d L)) :
    inner ℂ y ((leftBoundaryMapES A K L).adjoint (leftBoundaryMapES A K L x)) =
      ∑ τ : Cfg d L, inner ℂ (boundaryFamilyFiber (D := D) y τ)
        (groundSpaceGram A K (boundaryFamilyFiber (D := D) x τ)) := by
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  trans ∑ p : Cfg d K × Cfg d L,
      inner ℂ ((leftBoundaryMapES A K L y) (Fin.appendEquiv K L p))
        ((leftBoundaryMapES A K L x) (Fin.appendEquiv K L p))
  · symm
    apply Fintype.sum_equiv (Fin.appendEquiv K L)
    intro p
    rfl
  · simp only [Fin.appendEquiv, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ _
    rw [groundSpaceGram, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro u _
    have hp : Fin.append u τ ∘ Fin.castAdd L = u := by
      ext i
      simp [Fin.append_left]
    have hs : Fin.append u τ ∘ Fin.natAdd K = τ := by
      ext i
      simp [Fin.append_right]
    simp [boundaryFamilyFiber, leftBoundaryMapES, groundSpaceMapES,
      groundSpaceMap_apply, hp, hs]

/-- Operator form of the exact tail direct-sum Gram identity. -/
theorem tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram
    (A : MPSTensor d D) (K L : ℕ) :
    (tailBoundaryMapES A K L).adjoint.comp (tailBoundaryMapES A K L) =
      boundaryFiberwiseMap (D := D) (Cfg d K) (groundSpaceGram A L) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((tailBoundaryMapES A K L).adjoint (tailBoundaryMapES A K L x)) =
    inner ℂ y (boundaryFiberwiseMap (D := D) (Cfg d K) (groundSpaceGram A L) x)
  rw [inner_tailBoundaryMapES_adjoint_comp_self,
    inner_boundaryFiberwiseMap]

/-- The inverse Gram of the tail spectator map acts independently by the inverse
length-`L` Gram on every prefix fiber. -/
theorem inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A L)) :
    ContinuousLinearMap.inverseGram (tailBoundaryMapES A K L)
        (tailBoundaryMapES_injective_of_groundSpaceMapES_injective A K L h) =
      boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A L) h) := by
  rw [ContinuousLinearMap.inverseGram_eq_inverse]
  apply ContinuousLinearMap.inverse_eq
  · rw [tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  · rw [tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.inverseGram_comp_adjoint_comp_self,
      boundaryFiberwiseMap_id]

/-- Operator form of the exact left direct-sum Gram identity. -/
theorem leftBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram
    (A : MPSTensor d D) (K L : ℕ) :
    (leftBoundaryMapES A K L).adjoint.comp (leftBoundaryMapES A K L) =
      boundaryFiberwiseMap (D := D) (Cfg d L) (groundSpaceGram A K) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((leftBoundaryMapES A K L).adjoint (leftBoundaryMapES A K L x)) =
    inner ℂ y (boundaryFiberwiseMap (D := D) (Cfg d L) (groundSpaceGram A K) x)
  rw [inner_leftBoundaryMapES_adjoint_comp_self,
    inner_boundaryFiberwiseMap]

/-- The inverse Gram of the left spectator map acts independently by the inverse
length-`K` Gram on every suffix fiber. -/
theorem inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram
    (A : MPSTensor d D) (K L : ℕ)
    (h : Function.Injective (groundSpaceMapES A K)) :
    ContinuousLinearMap.inverseGram (leftBoundaryMapES A K L)
        (leftBoundaryMapES_injective_of_groundSpaceMapES_injective A K L h) =
      boundaryFiberwiseMap (D := D) (Cfg d L)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A K) h) := by
  rw [ContinuousLinearMap.inverseGram_eq_inverse]
  apply ContinuousLinearMap.inverse_eq
  · rw [leftBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  · rw [leftBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.inverseGram_comp_adjoint_comp_self,
      boundaryFiberwiseMap_id]

end MPSTensor
