/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWLowerBoundary

/-!
# FNW overlap coordinates

This module begins the source-coordinate proof of Fannes--Nachtergaele--Werner,
*Communications in Mathematical Physics* 144 (1992), 443--490, Lemma 6.2.
The common physical chain is split into consecutive blocks of lengths
\(\ell,m,r\). The left overlap family applies the boundary map \(F_{\ell+m}\)
to a rho-weighted matrix family indexed by the right block, while the right
overlap family applies \(F_{m+r}\) to a rho-weighted matrix family indexed by
the left block.

The virtual convention is \(A^\mu=v(\mu)^\dagger\). Thus the aggregate matrices
have the source orientation
\[
  A_\varphi=\sum_{\mu^r}\Phi(\mu^r)\rho v(\mu^r)\rho^{-1},\qquad
  A_\psi=\sum_{\mu^\ell}v(\mu^\ell)\Psi(\mu^\ell).
\]

This file keeps the linear contribution in FNW equation (6.5) separate. It does
not assert the final projector-defect estimate or introduce its quadratic term.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The rho-weighted Hilbert direct sum of virtual matrices indexed by a finite
spectator configuration space. The matrix norm and inner product are supplied
locally by `Matrix.toMatrixNormedAddCommGroup` and
`Matrix.toMatrixInnerProductSpace`. -/
abbrev FNWBoundaryFamilySpace (S : Type*) [Fintype S] :=
  PiLp 2 fun _ : S => Mat

/-- Three consecutive physical configuration blocks, with the left and middle
blocks grouped before appending the right block. -/
def fnwThreeBlockConfigEquiv (d ℓ m r : ℕ) :
    (Cfg d ℓ × Cfg d m) × Cfg d r ≃ Cfg d ((ℓ + m) + r) :=
  (Equiv.prodCongr (Fin.appendEquiv ℓ m) (Equiv.refl (Cfg d r))).trans
    (Fin.appendEquiv (ℓ + m) r)

@[simp]
theorem fnwThreeBlockConfigEquiv_apply
    (d ℓ m r : ℕ) (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    fnwThreeBlockConfigEquiv d ℓ m r ((μℓ, μm), μr) =
      Fin.append (Fin.append μℓ μm) μr := by
  rfl

@[simp]
theorem fnwThreeBlockConfigEquiv_symm_apply_apply
    (d ℓ m r : ℕ) (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    (fnwThreeBlockConfigEquiv d ℓ m r).symm
      (Fin.append (Fin.append μℓ μm) μr) = ((μℓ, μm), μr) := by
  exact (fnwThreeBlockConfigEquiv d ℓ m r).symm_apply_apply ((μℓ, μm), μr)

/-- The left overlap family in FNW Lemma 6.2. For fixed right spectator
\(\mu^r\), its coefficient on the first two blocks is
\(F_{\ell+m}(\Phi(\mu^r))\). -/
noncomputable def fnwLeftOverlapMap
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    FNWBoundaryFamilySpace (D := D) (Cfg d r) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact
    { toFun := fun Φ => WithLp.toLp 2 fun σ =>
        let blocks := (fnwThreeBlockConfigEquiv d ℓ m r).symm σ
        fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp blocks.2)
          (Fin.append blocks.1.1 blocks.1.2)
      map_add' := by
        intro Φ Ψ
        apply PiLp.ext
        intro σ
        simp
      map_smul' := by
        intro c Φ
        apply PiLp.ext
        intro σ
        simp }

/-- The right overlap family in FNW Lemma 6.2. For fixed left spectator
\(\mu^\ell\), its coefficient on the final two blocks is
\(F_{m+r}(\Psi(\mu^\ell))\). -/
noncomputable def fnwRightOverlapMap
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    FNWBoundaryFamilySpace (D := D) (Cfg d ℓ) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact
    { toFun := fun Ψ => WithLp.toLp 2 fun σ =>
        let blocks := (fnwThreeBlockConfigEquiv d ℓ m r).symm σ
        fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp blocks.1.1)
          (Fin.append blocks.1.2 blocks.2)
      map_add' := by
        intro Φ Ψ
        apply PiLp.ext
        intro σ
        simp
      map_smul' := by
        intro c Φ
        apply PiLp.ext
        intro σ
        simp }

@[simp]
theorem fnwLeftOverlapMap_apply_append
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLeftOverlapMap ρ hρ A ℓ m r Φ (Fin.append (Fin.append μℓ μm) μr) =
      fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr) (Fin.append μℓ μm) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  simp [fnwLeftOverlapMap]

@[simp]
theorem fnwRightOverlapMap_apply_append
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwRightOverlapMap ρ hρ A ℓ m r Ψ (Fin.append (Fin.append μℓ μm) μr) =
      fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ) (Fin.append μm μr) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  simp [fnwRightOverlapMap]

/-- Splitting an FNW boundary configuration after a left block moves the
adjoint left word to the left of the boundary matrix. -/
theorem fnwBoundaryMapCLM_append_eq_leftWord
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (K L : ℕ)
    (B : Mat) (u : Cfg d K) (τ : Cfg d L) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwBoundaryMapCLM ρ hρ A (K + L) B (Fin.append u τ) =
      fnwBoundaryMapCLM ρ hρ A L
        ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B) τ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  simp only [fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply,
    List.ofFn_fin_append, Kraus.evalWord_append, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  exact Matrix.trace_mul_cycle' B
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn τ))ᴴ
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ

/-- Splitting an FNW boundary configuration before a right block moves the
adjoint right word to the right of the boundary matrix. -/
theorem fnwBoundaryMapCLM_append_eq_rightWord
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (K L : ℕ)
    (B : Mat) (u : Cfg d K) (τ : Cfg d L) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwBoundaryMapCLM ρ hρ A (K + L) B (Fin.append u τ) =
      fnwBoundaryMapCLM ρ hρ A K
        (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn τ))ᴴ) u := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  simp only [fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply,
    List.ofFn_fin_append, Kraus.evalWord_append, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- The virtual boundary entering the middle block from the left overlap
family. -/
def fnwLeftMiddleBoundary
    (A : MPSTensor d D) {ℓ r : ℕ}
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (p : Cfg d ℓ × Cfg d r) : Mat :=
  (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn p.1))ᴴ * Φ.ofLp p.2

/-- The virtual boundary entering the middle block from the right overlap
family. -/
def fnwRightMiddleBoundary
    (A : MPSTensor d D) {ℓ r : ℕ}
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (p : Cfg d ℓ × Cfg d r) : Mat :=
  Ψ.ofLp p.1 *
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn p.2))ᴴ

/-- The physical inner product of the two overlap families decomposes into
length-\(m\) FNW boundary inner products, one for each pair of spectator
configurations. -/
theorem inner_fnwLeftOverlapMap_fnwRightOverlapMap
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) =
      ∑ μℓ : Cfg d ℓ, ∑ μr : Cfg d r,
        inner ℂ
          (fnwBoundaryMapCLM ρ hρ A m
            ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ * Φ.ofLp μr))
          (fnwBoundaryMapCLM ρ hρ A m
            (Ψ.ofLp μℓ *
              (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.inner_apply]
  trans ∑ p : (Cfg d ℓ × Cfg d m) × Cfg d r,
      inner ℂ
        (fnwLeftOverlapMap ρ hρ A ℓ m r Φ
          (fnwThreeBlockConfigEquiv d ℓ m r p))
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ
          (fnwThreeBlockConfigEquiv d ℓ m r p))
  · symm
    apply Fintype.sum_equiv (fnwThreeBlockConfigEquiv d ℓ m r)
    intro p
    rfl
  · simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro μℓ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro μr _
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro μm _
    simp only [fnwThreeBlockConfigEquiv_apply]
    rw [fnwLeftOverlapMap_apply_append, fnwRightOverlapMap_apply_append,
      fnwBoundaryMapCLM_append_eq_leftWord,
      fnwBoundaryMapCLM_append_eq_rightWord]

/-- The weighted source pairing after extracting left and right words is
exactly the pairing of the corresponding aggregate summands. -/
theorem inner_conjTranspose_mul_mul_conjTranspose_eq_aggregateSummands
    (ρ : Mat) (hρ : ρ.PosDef) (U V X Y : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    inner ℂ (Uᴴ * X) (Y * Vᴴ) =
      inner ℂ (X * ρ * V * ρ⁻¹) (U * Y) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [Matrix.rhoWeighted_inner ρ hρ, Matrix.rhoWeighted_inner ρ hρ]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_nonsing_inv, hρ.isHermitian.eq]
  rw [show ρ * (ρ⁻¹ * (Vᴴ * (ρ * Xᴴ))) * (U * Y) =
      (ρ * ρ⁻¹) * Vᴴ * ρ * Xᴴ * U * Y by simp only [Matrix.mul_assoc]]
  rw [Matrix.mul_nonsing_inv ρ
    ((Matrix.isUnit_iff_isUnit_det ρ).mp hρ.isUnit), Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle ρ (Xᴴ * U * Y) Vᴴ

/-- The aggregate matrix \(A_\varphi\) in FNW Lemma 6.2, with source order
\(\Phi(\mu^r)\rho v(\mu^r)\rho^{-1}\). -/
noncomputable def fnwLeftOverlapAggregate
    (ρ : Mat) (A : MPSTensor d D) (r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) : Mat :=
  ∑ μr : Cfg d r, Φ.ofLp μr * ρ *
    Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr) * ρ⁻¹

/-- The aggregate matrix \(A_\psi\) in FNW Lemma 6.2, with source order
\(v(\mu^\ell)\Psi(\mu^\ell)\). -/
noncomputable def fnwRightOverlapAggregate
    (A : MPSTensor d D) (ℓ : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) : Mat :=
  ∑ μℓ : Cfg d ℓ,
    Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ) * Ψ.ofLp μℓ

/-- The leading weighted term in the middle-block decomposition is the
rho-weighted inner product of the two FNW aggregate matrices. -/
theorem sum_inner_overlapFibers_eq_inner_aggregates
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ∑ μℓ : Cfg d ℓ, ∑ μr : Cfg d r,
        inner ℂ
          ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ * Φ.ofLp μr)
          (Ψ.ofLp μℓ *
            (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ) =
      inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
        (fnwRightOverlapAggregate A ℓ Ψ) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [fnwLeftOverlapAggregate, fnwRightOverlapAggregate, sum_inner]
  simp_rw [inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μr _
  apply Finset.sum_congr rfl
  intro μℓ _
  exact inner_conjTranspose_mul_mul_conjTranspose_eq_aggregateSummands
    ρ hρ
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))
    (Φ.ofLp μr) (Ψ.ofLp μℓ)

/-- Subtracting the aggregate pairing leaves the sum of the middle-block
boundary defects to which equation (5.9) applies termwise. -/
theorem inner_overlap_sub_inner_aggregates
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
      inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
        (fnwRightOverlapAggregate A ℓ Ψ) =
      ∑ p : Cfg d ℓ × Cfg d r,
        (inner ℂ
            (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
            (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
          inner ℂ (fnwLeftMiddleBoundary A Φ p)
            (fnwRightMiddleBoundary A Ψ p)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [inner_fnwLeftOverlapMap_fnwRightOverlapMap,
    ← sum_inner_overlapFibers_eq_inner_aggregates]
  simp only [fnwLeftMiddleBoundary, fnwRightMiddleBoundary,
    Fintype.sum_prod_type, Finset.sum_sub_distrib]

/-- The FNW transfer map remains unital under every word length. -/
theorem fnwTransferMap_pow_one
    (A : MPSTensor d D) (hA : IsLeftCanonical A) (N : ℕ) :
    (fnwTransferMap A ^ N) (1 : Mat) = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, Module.End.mul_apply, fnwTransferMap_one A hA, ih]

/-- The trace-pairing adjoint relation between the TNLean and FNW transfer maps
persists under every power. -/
theorem trace_mul_fnwTransferMap_pow
    (A : MPSTensor d D) (ρ X : Mat) (N : ℕ) :
    Matrix.trace (ρ * (fnwTransferMap A ^ N) X) =
      Matrix.trace ((Kraus.transferMap A ^ N) ρ * X) := by
  induction N generalizing X with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, Module.End.mul_apply]
      calc
        Matrix.trace (ρ * (fnwTransferMap A ^ N) (fnwTransferMap A X)) =
            Matrix.trace ((Kraus.transferMap A ^ N) ρ * fnwTransferMap A X) :=
          ih (fnwTransferMap A X)
        _ = Matrix.trace
            (Kraus.transferMap A ((Kraus.transferMap A ^ N) ρ) * X) :=
          trace_mul_fnwTransferMap A ((Kraus.transferMap A ^ N) ρ) X
        _ = Matrix.trace ((Kraus.transferMap A ^ (N + 1)) ρ * X) := by
          rw [pow_succ', Module.End.mul_apply]

/-- Word unitality gives the first spectator-family squared-norm identity in
FNW Lemma 6.2. -/
theorem sum_norm_sq_conjTranspose_evalWord_mul
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (N : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    ∑ u : Cfg d N,
      ‖(Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B‖ ^ 2 =
        ‖B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  simp_rw [Matrix.rhoWeighted_norm_sq ρ hρ]
  have hword :
      ∑ u : Cfg d N,
        Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u) *
          (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ = 1 := by
    have hpow := fnwTransferMap_pow_one A hA N
    rw [fnwTransferMap, Kraus.mapLM_pow_apply] at hpow
    simpa only [Matrix.mul_one] using hpow
  calc
    ∑ u : Cfg d N,
        (Matrix.trace (ρ *
          ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B)ᴴ *
          ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B))).re =
        (∑ u : Cfg d N, Matrix.trace (ρ *
          ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B)ᴴ *
          ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B))).re :=
      (map_sum Complex.reCLM (fun u : Cfg d N => Matrix.trace (ρ *
        ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B)ᴴ *
        ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B)))
        Finset.univ).symm
    _ = (Matrix.trace (ρ * Bᴴ * (∑ u : Cfg d N,
          Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u) *
            (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ) * B)).re := by
      congr 1
      rw [← Matrix.trace_sum Finset.univ]
      congr 1
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, Matrix.mul_sum, Finset.sum_mul]
    _ = (Matrix.trace (ρ * Bᴴ * B)).re := by rw [hword, Matrix.mul_one]

/-- Stationarity gives the second spectator-family squared-norm identity in
FNW Lemma 6.2. -/
theorem sum_norm_sq_mul_conjTranspose_evalWord
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (N : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    ∑ u : Cfg d N,
      ‖B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ‖ ^ 2 =
        ‖B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  simp_rw [Matrix.rhoWeighted_norm_sq ρ hρ]
  have hpow : (Kraus.transferMap A ^ N) ρ = ρ := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [pow_succ, Module.End.mul_apply, hρfix, ih]
  have htrace := trace_mul_fnwTransferMap_pow A ρ (Bᴴ * B) N
  rw [hpow] at htrace
  rw [fnwTransferMap, Kraus.mapLM_pow_apply] at htrace
  calc
    ∑ u : Cfg d N,
        (Matrix.trace (ρ *
          (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ)ᴴ *
          (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ))).re =
        (∑ u : Cfg d N, Matrix.trace (ρ *
          (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ)ᴴ *
          (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ))).re :=
      (map_sum Complex.reCLM (fun u : Cfg d N => Matrix.trace (ρ *
        (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ)ᴴ *
        (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ)))
        Finset.univ).symm
    _ = (Matrix.trace (ρ * (∑ u : Cfg d N,
          Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u) * (Bᴴ * B) *
            (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ))).re := by
      congr 1
      rw [Matrix.mul_sum, Matrix.trace_sum]
      congr 1
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = (Matrix.trace (ρ * Bᴴ * B)).re := by
      simpa only [Matrix.mul_assoc] using congrArg Complex.re htrace

/-- Word unitality identifies the squared norm of the left middle-boundary
family with the squared norm of its rho-weighted spectator family. -/
theorem sum_norm_sq_fnwLeftMiddleBoundary
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (ℓ r : ℕ) (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    ∑ p : Cfg d ℓ × Cfg d r, ‖fnwLeftMiddleBoundary A Φ p‖ ^ 2 = ‖Φ‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    ∑ μr : Cfg d r, ∑ μℓ : Cfg d ℓ,
        ‖fnwLeftMiddleBoundary A Φ (μℓ, μr)‖ ^ 2 =
        ∑ μr : Cfg d r, ‖Φ.ofLp μr‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro μr _
      exact sum_norm_sq_conjTranspose_evalWord_mul ρ hρ A hA ℓ (Φ.ofLp μr)
    _ = ‖Φ‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ Φ).symm

/-- Stationarity identifies the squared norm of the right middle-boundary
family with the squared norm of its rho-weighted spectator family. -/
theorem sum_norm_sq_fnwRightMiddleBoundary
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    ∑ p : Cfg d ℓ × Cfg d r, ‖fnwRightMiddleBoundary A Ψ p‖ ^ 2 = ‖Ψ‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  rw [Fintype.sum_prod_type]
  calc
    ∑ μℓ : Cfg d ℓ, ∑ μr : Cfg d r,
        ‖fnwRightMiddleBoundary A Ψ (μℓ, μr)‖ ^ 2 =
        ∑ μℓ : Cfg d ℓ, ‖Ψ.ofLp μℓ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro μℓ _
      exact sum_norm_sq_mul_conjTranspose_evalWord ρ hρ A hρfix r (Ψ.ofLp μℓ)
    _ = ‖Ψ‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ Ψ).symm

/-- Equation (5.9), applied to every pair of spectator configurations and
combined by finite Cauchy--Schwarz. This is the analytic numerator in FNW
1992, equation (6.5), before the lower-boundary estimate is used. -/
theorem norm_inner_overlap_sub_inner_aggregates_le [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      fnwMixingQuantity ρ hρ A htr m *
        (Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwLeftMiddleBoundary A Φ p‖ ^ 2) *
        Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwRightMiddleBoundary A Ψ p‖ ^ 2)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rw [inner_overlap_sub_inner_aggregates]
  calc
    ‖∑ p : Cfg d ℓ × Cfg d r,
        (inner ℂ
            (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
            (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
          inner ℂ (fnwLeftMiddleBoundary A Φ p)
            (fnwRightMiddleBoundary A Ψ p))‖
        ≤ ∑ p : Cfg d ℓ × Cfg d r,
          ‖inner ℂ
              (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
              (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
            inner ℂ (fnwLeftMiddleBoundary A Φ p)
              (fnwRightMiddleBoundary A Ψ p)‖ := by
          simpa using norm_sum_le (Finset.univ : Finset (Cfg d ℓ × Cfg d r))
            (fun p =>
              inner ℂ
                  (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
                  (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
                inner ℂ (fnwLeftMiddleBoundary A Φ p)
                  (fnwRightMiddleBoundary A Ψ p))
    _ ≤ ∑ p : Cfg d ℓ × Cfg d r,
        fnwMixingQuantity ρ hρ A htr m *
          ‖fnwLeftMiddleBoundary A Φ p‖ * ‖fnwRightMiddleBoundary A Ψ p‖ :=
      Finset.sum_le_sum fun p _ =>
        norm_inner_fnwBoundaryMapCLM_sub_rhoWeighted_le_fnwMixingQuantity
          ρ hρ htr A m (fnwLeftMiddleBoundary A Φ p)
            (fnwRightMiddleBoundary A Ψ p)
    _ = fnwMixingQuantity ρ hρ A htr m *
        ∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwLeftMiddleBoundary A Φ p‖ * ‖fnwRightMiddleBoundary A Ψ p‖ := by
      simpa only [mul_assoc] using
        (Finset.mul_sum (s := (Finset.univ : Finset (Cfg d ℓ × Cfg d r)))
          (f := fun p =>
            ‖fnwLeftMiddleBoundary A Φ p‖ * ‖fnwRightMiddleBoundary A Ψ p‖)
          (a := fnwMixingQuantity ρ hρ A htr m)).symm
    _ ≤ fnwMixingQuantity ρ hρ A htr m *
        (Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwLeftMiddleBoundary A Φ p‖ ^ 2) *
        Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwRightMiddleBoundary A Ψ p‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (Cfg d ℓ × Cfg d r))
          (fun p => ‖fnwLeftMiddleBoundary A Φ p‖)
          (fun p => ‖fnwRightMiddleBoundary A Ψ p‖)
      · exact mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)

/-- The squared norm of the left overlap vector is the sum of the squared
boundary-map norms of its right-spectator family. -/
theorem norm_fnwLeftOverlapMap_sq
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ ^ 2 =
      ∑ μr : Cfg d r, ‖fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr)‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2]
  trans ∑ p : (Cfg d ℓ × Cfg d m) × Cfg d r,
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ (fnwThreeBlockConfigEquiv d ℓ m r p)‖ ^ 2
  · symm
    apply Fintype.sum_equiv (fnwThreeBlockConfigEquiv d ℓ m r)
    intro p
    rfl
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro μr _
    rw [PiLp.norm_sq_eq_of_L2]
    apply Fintype.sum_equiv (Fin.appendEquiv ℓ m)
    intro q
    rw [fnwThreeBlockConfigEquiv_apply, fnwLeftOverlapMap_apply_append]
    change ‖fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr)
      (Fin.append q.1 q.2)‖ ^ 2 =
        ‖fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr)
          (Fin.append q.1 q.2)‖ ^ 2
    rfl

/-- The squared norm of the right overlap vector is the sum of the squared
boundary-map norms of its left-spectator family. -/
theorem norm_fnwRightOverlapMap_sq
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ ^ 2 =
      ∑ μℓ : Cfg d ℓ, ‖fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ)‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2]
  trans ∑ p : (Cfg d ℓ × Cfg d m) × Cfg d r,
      ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ (fnwThreeBlockConfigEquiv d ℓ m r p)‖ ^ 2
  · symm
    apply Fintype.sum_equiv (fnwThreeBlockConfigEquiv d ℓ m r)
    intro p
    rfl
  · simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro μℓ _
    trans ∑ q : Cfg d m × Cfg d r,
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ
          (fnwThreeBlockConfigEquiv d ℓ m r ((μℓ, q.1), q.2))‖ ^ 2
    · rw [Fintype.sum_prod_type]
    · rw [PiLp.norm_sq_eq_of_L2]
      apply Fintype.sum_equiv (Fin.appendEquiv m r)
      intro q
      rw [fnwThreeBlockConfigEquiv_apply, fnwRightOverlapMap_apply_append]
      change ‖fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ)
        (Fin.append q.1 q.2)‖ ^ 2 =
          ‖fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ)
            (Fin.append q.1 q.2)‖ ^ 2
      rfl

/-- The source lower-boundary constant controls the left spectator-family
norm through the left overlap vector. -/
theorem fnwLowerBoundaryConstant_mul_familyNorm_sq_le_leftOverlap [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLowerBoundaryConstant ρ hρ A (ℓ + m) * ‖Φ‖ ^ 2 ≤
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, norm_fnwLeftOverlapMap_sq]
  exact Finset.sum_le_sum fun μr _ =>
    fnwLowerBoundaryConstant_mul_norm_sq_le ρ hρ A (ℓ + m) (Φ.ofLp μr)

/-- The source lower-boundary constant controls the right spectator-family
norm through the right overlap vector. -/
theorem fnwLowerBoundaryConstant_mul_familyNorm_sq_le_rightOverlap [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLowerBoundaryConstant ρ hρ A (m + r) * ‖Ψ‖ ^ 2 ≤
      ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, norm_fnwRightOverlapMap_sq]
  exact Finset.sum_le_sum fun μℓ _ =>
    fnwLowerBoundaryConstant_mul_norm_sq_le ρ hρ A (m + r) (Ψ.ofLp μℓ)

/-- Monotonicity of the lower-boundary constant converts both spectator
family norms into the two physical overlap norms at the common middle length. -/
theorem fnwLowerBoundaryConstant_mul_familyNorms_le_overlapNorms [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLowerBoundaryConstant ρ hρ A m * ‖Φ‖ * ‖Ψ‖ ≤
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let c := fnwLowerBoundaryConstant ρ hρ A m
  have hc_left : c * ‖Φ‖ ^ 2 ≤ ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (fnwLowerBoundaryConstant_mono ρ hρ A hρfix (Nat.le_add_left m ℓ))
      (sq_nonneg ‖Φ‖)).trans
        (fnwLowerBoundaryConstant_mul_familyNorm_sq_le_leftOverlap
          ρ hρ A ℓ m r Φ)
  have hc_right : c * ‖Ψ‖ ^ 2 ≤ ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (fnwLowerBoundaryConstant_mono ρ hρ A hρfix (Nat.le_add_right m r))
      (sq_nonneg ‖Ψ‖)).trans
        (fnwLowerBoundaryConstant_mul_familyNorm_sq_le_rightOverlap
          ρ hρ A ℓ m r Ψ)
  have hsqrt : Real.sqrt c ^ 2 = c := Real.sq_sqrt hminus.le
  have hleft : Real.sqrt c * ‖Φ‖ ≤ ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ :=
    (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg Φ))
      (norm_nonneg _)).mp <| by
        rw [mul_pow, hsqrt]
        exact hc_left
  have hright : Real.sqrt c * ‖Ψ‖ ≤ ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ :=
    (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg Ψ))
      (norm_nonneg _)).mp <| by
        rw [mul_pow, hsqrt]
        exact hc_right
  calc
    c * ‖Φ‖ * ‖Ψ‖ = Real.sqrt c ^ 2 * ‖Φ‖ * ‖Ψ‖ := by rw [hsqrt]
    _ = (Real.sqrt c * ‖Φ‖) * (Real.sqrt c * ‖Ψ‖) := by ring
    _ ≤ ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ :=
      mul_le_mul hleft hright
        (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg Ψ)) (norm_nonneg _)

/-- The linear numerator estimate after the two spectator-family norm
identities are inserted. The two factors remain the genuine rho-weighted
`PiLp 2` family norms. -/
theorem norm_inner_overlap_sub_inner_aggregates_le_familyNorms [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      fnwMixingQuantity ρ hρ A htr m * ‖Φ‖ * ‖Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have h := norm_inner_overlap_sub_inner_aggregates_le ρ hρ htr A ℓ m r Φ Ψ
  rw [sum_norm_sq_fnwLeftMiddleBoundary ρ hρ A hA ℓ r Φ,
    sum_norm_sq_fnwRightMiddleBoundary ρ hρ A hρfix ℓ r Ψ,
    Real.sqrt_sq (norm_nonneg Φ), Real.sqrt_sq (norm_nonneg Ψ)] at h
  simpa only [mul_assoc] using h

/-- FNW 1992, equation (6.5). The middle-block overlap defect carries exactly
the linear coefficient \(a(m)/a_-(m)\). Positivity of the actual source
lower-boundary constant is assumed directly, without replacing it by
\(1-a(m)\) or assuming \(a(m)<1\). -/
theorem norm_inner_overlap_sub_inner_aggregates_le_div_lowerBoundary [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      (fnwMixingQuantity ρ hρ A htr m /
          fnwLowerBoundaryConstant ρ hρ A m) *
        ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let a := fnwMixingQuantity ρ hρ A htr m
  let c := fnwLowerBoundaryConstant ρ hρ A m
  have ha : 0 ≤ a := by
    exact mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)
  have hc : c ≠ 0 := ne_of_gt hminus
  have hfamilies := fnwLowerBoundaryConstant_mul_familyNorms_le_overlapNorms
    ρ hρ A hρfix ℓ m r Φ Ψ hminus
  calc
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤ a * ‖Φ‖ * ‖Ψ‖ :=
      norm_inner_overlap_sub_inner_aggregates_le_familyNorms
        ρ hρ htr A hA hρfix ℓ m r Φ Ψ
    _ = (a / c) * (c * ‖Φ‖ * ‖Ψ‖) := by
      calc
        a * ‖Φ‖ * ‖Ψ‖ = ((a / c) * c) * ‖Φ‖ * ‖Ψ‖ := by
          rw [div_mul_cancel₀ a hc]
        _ = (a / c) * (c * ‖Φ‖ * ‖Ψ‖) := by ring
    _ ≤ (a / c) *
        (‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
          ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖) :=
      mul_le_mul_of_nonneg_left hfamilies (div_nonneg ha hminus.le)
    _ = (a / c) * ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by ring

end

end MPSTensor
