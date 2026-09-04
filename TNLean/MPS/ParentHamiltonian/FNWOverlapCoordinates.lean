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

The linear equation (6.5) estimate built from these coordinates remains separate
from the later quadratic contribution to the projector defect.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The rho-weighted Hilbert direct sum of virtual matrices indexed by a finite
spectator configuration space. Each summand carries the rho-weighted matrix norm
and inner product. -/
abbrev FNWBoundaryFamilySpace (S : Type*) [Fintype S] :=
  PiLp 2 fun _ : S => Mat

/-- Three consecutive physical configuration blocks, with the left and middle
blocks grouped before appending the right block. -/
def fnwThreeBlockConfigEquiv (d ℓ m r : ℕ) :
    (Cfg d ℓ × Cfg d m) × Cfg d r ≃ Cfg d ((ℓ + m) + r) :=
  (Equiv.prodCongr (Fin.appendEquiv ℓ m) (Equiv.refl (Cfg d r))).trans
    (Fin.appendEquiv (ℓ + m) r)

/-- The three-block configuration equivalence sends a block triple to nested append. -/
@[simp]
theorem fnwThreeBlockConfigEquiv_apply
    (d ℓ m r : ℕ) (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    fnwThreeBlockConfigEquiv d ℓ m r ((μℓ, μm), μr) =
      Fin.append (Fin.append μℓ μm) μr := by
  rfl

/-- Splitting the nested append of three blocks recovers the original block triple. -/
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
    weighted_matrix_instances ρ hρ in
    FNWBoundaryFamilySpace (D := D) (Cfg d r) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) := by
  weighted_matrix_instances ρ hρ
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
    weighted_matrix_instances ρ hρ in
    FNWBoundaryFamilySpace (D := D) (Cfg d ℓ) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) := by
  weighted_matrix_instances ρ hρ
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

/-- The left overlap map on an appended configuration evaluates the boundary map
on the left and middle blocks. -/
@[simp]
theorem fnwLeftOverlapMap_apply_append
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    weighted_matrix_instances ρ hρ in
    fnwLeftOverlapMap ρ hρ A ℓ m r Φ (Fin.append (Fin.append μℓ μm) μr) =
      fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr) (Fin.append μℓ μm) := by
  weighted_matrix_instances ρ hρ
  simp [fnwLeftOverlapMap]

/-- The right overlap map on an appended configuration evaluates the boundary map
on the middle and right blocks. -/
@[simp]
theorem fnwRightOverlapMap_apply_append
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    weighted_matrix_instances ρ hρ in
    fnwRightOverlapMap ρ hρ A ℓ m r Ψ (Fin.append (Fin.append μℓ μm) μr) =
      fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ) (Fin.append μm μr) := by
  weighted_matrix_instances ρ hρ
  simp [fnwRightOverlapMap]

/-- The right-spectator family obtained by splitting the full FNW ground vector
with virtual boundary \(B\) after the left and middle blocks. -/
noncomputable def fnwLeftFullGroundFamily
    (A : MPSTensor d D) (r : ℕ) (B : Mat) :
    FNWBoundaryFamilySpace (D := D) (Cfg d r) :=
  WithLp.toLp 2 fun μr =>
    B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ

/-- The left-spectator family obtained by splitting the full FNW ground vector
with virtual boundary \(B\) before the middle and right blocks. -/
noncomputable def fnwRightFullGroundFamily
    (A : MPSTensor d D) (ℓ : ℕ) (B : Mat) :
    FNWBoundaryFamilySpace (D := D) (Cfg d ℓ) :=
  WithLp.toLp 2 fun μℓ =>
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ * B

/-- The special right-spectator family evaluates by right-word multiplication. -/
@[simp]
theorem fnwLeftFullGroundFamily_apply
    (A : MPSTensor d D) (r : ℕ) (B : Mat) (μr : Cfg d r) :
    (fnwLeftFullGroundFamily A r B).ofLp μr =
      B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ := by
  rfl

/-- The special left-spectator family evaluates by left-word multiplication. -/
@[simp]
theorem fnwRightFullGroundFamily_apply
    (A : MPSTensor d D) (ℓ : ℕ) (B : Mat) (μℓ : Cfg d ℓ) :
    (fnwRightFullGroundFamily A ℓ B).ofLp μℓ =
      (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ * B := by
  rfl

/-- Splitting an FNW boundary configuration after a left block moves the
adjoint left word to the left of the boundary matrix. -/
theorem fnwBoundaryMapCLM_append_eq_leftWord
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (K L : ℕ)
    (B : Mat) (u : Cfg d K) (τ : Cfg d L) :
    weighted_matrix_instances ρ hρ in
    fnwBoundaryMapCLM ρ hρ A (K + L) B (Fin.append u τ) =
      fnwBoundaryMapCLM ρ hρ A L
        ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn u))ᴴ * B) τ := by
  weighted_matrix_instances ρ hρ
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
    weighted_matrix_instances ρ hρ in
    fnwBoundaryMapCLM ρ hρ A (K + L) B (Fin.append u τ) =
      fnwBoundaryMapCLM ρ hρ A K
        (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn τ))ᴴ) u := by
  weighted_matrix_instances ρ hρ
  simp only [fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply,
    List.ofFn_fin_append, Kraus.evalWord_append, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- The left overlap map of the special right-spectator family is the full FNW
boundary vector at the associated total length. -/
theorem fnwLeftOverlapMap_fullGroundFamily
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) (B : Mat) :
    weighted_matrix_instances ρ hρ in
    fnwLeftOverlapMap ρ hρ A ℓ m r (fnwLeftFullGroundFamily A r B) =
      fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B := by
  weighted_matrix_instances ρ hρ
  apply PiLp.ext
  intro σ
  rw [← (fnwThreeBlockConfigEquiv d ℓ m r).apply_symm_apply σ]
  obtain ⟨⟨μℓ, μm⟩, μr⟩ := (fnwThreeBlockConfigEquiv d ℓ m r).symm σ
  simp only [fnwThreeBlockConfigEquiv_apply, fnwLeftOverlapMap_apply_append,
    fnwLeftFullGroundFamily_apply, fnwBoundaryMapCLM_apply,
    fnwBoundaryMap_apply, List.ofFn_fin_append, Kraus.evalWord_append,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The right overlap map of the special left-spectator family is the same full
FNW boundary vector, with the total length associated to the three blocks. -/
theorem fnwRightOverlapMap_fullGroundFamily
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) (B : Mat) :
    weighted_matrix_instances ρ hρ in
    fnwRightOverlapMap ρ hρ A ℓ m r (fnwRightFullGroundFamily A ℓ B) =
      fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B := by
  weighted_matrix_instances ρ hρ
  apply PiLp.ext
  intro σ
  rw [← (fnwThreeBlockConfigEquiv d ℓ m r).apply_symm_apply σ]
  obtain ⟨⟨μℓ, μm⟩, μr⟩ := (fnwThreeBlockConfigEquiv d ℓ m r).symm σ
  simp only [fnwThreeBlockConfigEquiv_apply, fnwRightOverlapMap_apply_append,
    fnwRightFullGroundFamily_apply, fnwBoundaryMapCLM_apply,
    fnwBoundaryMap_apply, List.ofFn_fin_append, Kraus.evalWord_append,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
    (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ
    (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ *
      (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μm))ᴴ)

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
    weighted_matrix_instances ρ hρ in
    inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) =
      ∑ μℓ : Cfg d ℓ, ∑ μr : Cfg d r,
        inner ℂ
          (fnwBoundaryMapCLM ρ hρ A m
            ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ * Φ.ofLp μr))
          (fnwBoundaryMapCLM ρ hρ A m
            (Ψ.ofLp μℓ *
              (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ)) := by
  weighted_matrix_instances ρ hρ
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

private theorem fnwPosDef_nonsingInverse_mul (ρ : Mat) (hρ : ρ.PosDef) :
    ρ * ρ⁻¹ = 1 ∧ ρ⁻¹ * ρ = 1 := by
  have hdet : IsUnit ρ.det := (Matrix.isUnit_iff_isUnit_det ρ).mp hρ.isUnit
  exact ⟨Matrix.mul_nonsing_inv ρ hdet, Matrix.nonsing_inv_mul ρ hdet⟩

/-- The weighted source pairing after extracting left and right words is
exactly the pairing of the corresponding aggregate summands. -/
theorem inner_conjTranspose_mul_mul_conjTranspose_eq_aggregateSummands
    (ρ : Mat) (hρ : ρ.PosDef) (U V X Y : Mat) :
    weighted_matrix_instances ρ hρ in
    inner ℂ (Uᴴ * X) (Y * Vᴴ) =
      inner ℂ (X * ρ * V * ρ⁻¹) (U * Y) := by
  weighted_matrix_instances ρ hρ
  rw [Matrix.rhoWeighted_inner ρ hρ, Matrix.rhoWeighted_inner ρ hρ]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_nonsing_inv, hρ.isHermitian.eq]
  rw [show ρ * (ρ⁻¹ * (Vᴴ * (ρ * Xᴴ))) * (U * Y) =
      (ρ * ρ⁻¹) * Vᴴ * ρ * Xᴴ * U * Y by simp only [Matrix.mul_assoc]]
  rw [(fnwPosDef_nonsingInverse_mul ρ hρ).1, Matrix.one_mul]
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
    weighted_matrix_instances ρ hρ in
    ∑ μℓ : Cfg d ℓ, ∑ μr : Cfg d r,
        inner ℂ
          ((Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ * Φ.ofLp μr)
          (Ψ.ofLp μℓ *
            (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ) =
      inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
        (fnwRightOverlapAggregate A ℓ Ψ) := by
  weighted_matrix_instances ρ hρ
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
    weighted_matrix_instances ρ hρ in
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
  weighted_matrix_instances ρ hρ
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

/-- Stationarity collapses the special left aggregate to its full-chain
virtual boundary. -/
theorem fnwLeftOverlapAggregate_fullGroundFamily
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (r : ℕ) (B : Mat) :
    weighted_matrix_instances ρ hρ in
    fnwLeftOverlapAggregate ρ A r (fnwLeftFullGroundFamily A r B) = B := by
  weighted_matrix_instances ρ hρ
  have hpow : (Kraus.transferMap A ^ r) ρ = ρ := by
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, Module.End.mul_apply, hρfix, ih]
  rw [Kraus.mapLM_pow_apply] at hpow
  have hsum :
      (∑ μr : Cfg d r,
        (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ * ρ *
          Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr)) = ρ := by
    calc
      (∑ μr : Cfg d r,
        (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ * ρ *
          Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr)) =
          ∑ σ : Cfg d r, Kraus.evalWord A (List.ofFn σ) * ρ *
            (Kraus.evalWord A (List.ofFn σ))ᴴ := by
        exact Fintype.sum_equiv (physicalSiteReverseConfigEquiv d r)
          (fun μr : Cfg d r =>
            (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ * ρ *
              Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))
          (fun σ : Cfg d r =>
            Kraus.evalWord A (List.ofFn σ) * ρ *
              (Kraus.evalWord A (List.ofFn σ))ᴴ) (fun μr => by
            simp [physicalSiteReverseConfigEquiv, Equiv.arrowCongr,
              Function.comp_def, List.ofFn_reverse, Kraus.evalWord_conjTranspose])
      _ = ρ := hpow
  rw [fnwLeftOverlapAggregate]
  simp only [fnwLeftFullGroundFamily_apply]
  calc
    ∑ μr : Cfg d r,
        (B * (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ) * ρ *
            Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr) * ρ⁻¹ =
        B * (∑ μr : Cfg d r,
          (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr))ᴴ * ρ *
            Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr)) * ρ⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_sum, Finset.sum_mul]
    _ = B * (ρ * ρ⁻¹) := by rw [hsum, Matrix.mul_assoc]
    _ = B := by rw [(fnwPosDef_nonsingInverse_mul ρ hρ).1, Matrix.mul_one]

/-- Word unitality collapses the special right aggregate to its full-chain
virtual boundary. -/
theorem fnwRightOverlapAggregate_fullGroundFamily
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hA : IsLeftCanonical A) (ℓ : ℕ) (B : Mat) :
    weighted_matrix_instances ρ hρ in
    fnwRightOverlapAggregate A ℓ (fnwRightFullGroundFamily A ℓ B) = B := by
  weighted_matrix_instances ρ hρ
  have hword :
      ∑ μℓ : Cfg d ℓ,
        Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ) *
          (Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ))ᴴ = 1 := by
    have hpow := fnwTransferMap_pow_one A hA ℓ
    rw [fnwTransferMap, Kraus.mapLM_pow_apply] at hpow
    simpa only [Matrix.mul_one] using hpow
  rw [fnwRightOverlapAggregate]
  simp only [fnwRightFullGroundFamily_apply, ← Matrix.mul_assoc,
    ← Finset.sum_mul, hword, Matrix.one_mul]

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

/-- The rho-weighted norm of the special right-spectator family equals the norm
of its full-chain virtual boundary. -/
theorem norm_fnwLeftFullGroundFamily
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (r : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    ‖fnwLeftFullGroundFamily A r B‖ = ‖B‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg B)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact sum_norm_sq_mul_conjTranspose_evalWord ρ hρ A hρfix r B

/-- The rho-weighted norm of the special left-spectator family equals the norm
of its full-chain virtual boundary. -/
theorem norm_fnwRightFullGroundFamily
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hA : IsLeftCanonical A) (ℓ : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    ‖fnwRightFullGroundFamily A ℓ B‖ = ‖B‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg B)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact sum_norm_sq_conjTranspose_evalWord_mul ρ hρ A hA ℓ B

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

end

end MPSTensor
