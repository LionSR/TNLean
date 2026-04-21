/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Channel.POVM
import TNLean.Channel.KrausFreedom

/-!
# Uniqueness properties of concrete Naimark dilations

This file provides additional API around `TNLean.Channel.POVM`.

## Main definitions

- `POVM.IsNaimarkDilation` — a packaged predicate for a Naimark dilation.

## Main results

- `POVM.isNaimarkDilation_naimark` — the explicit dilation from `POVM.lean`
  satisfies the packaged `IsNaimarkDilation` predicate.
- `POVM.exists_isometry_mul_naimarkIsometry_of_recovery` — any dilation matrix
  recovering the POVM through the canonical projectors factors through the
  canonical Naimark isometry via an isometry on the dilated space.

## References

- [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Ch. 2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
open Matrix Finset BigOperators

variable {D n : ℕ}

namespace POVM

set_option maxHeartbeats 1600000 in
-- The partial-isometry extension proof drives higher-order typeclass search in Lean 4.29.
/-- If two square matrices have the same Gram matrix, then they differ by left
multiplication by a unitary matrix. -/
private theorem exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (B A : Matrix (Fin D) (Fin D) ℂ)
    (hGram : Bᴴ * B = Aᴴ * A) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      B = (U : Matrix (Fin D) (Fin D) ℂ) * A := by
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin D)) :=
    PiLp.innerProductSpace (fun _ : Fin D => ℂ)
  letI : FiniteDimensional ℂ (EuclideanSpace ℂ (Fin D)) :=
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis.finiteDimensional_of_finite
  let fB : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D) :=
    Matrix.toEuclideanLin B
  let fA : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D) :=
    Matrix.toEuclideanLin A
  have hinner : ∀ v w : EuclideanSpace ℂ (Fin D),
      ⟪fB v, fB w⟫_ℂ = ⟪fA v, fA w⟫_ℂ := by
    intro v w
    rw [← LinearMap.adjoint_inner_right fB v (fB w),
        ← LinearMap.adjoint_inner_right fA v (fA w)]
    congr 1
    show fB.adjoint (fB w) = fA.adjoint (fA w)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
    change (Bᴴ.toEuclideanLin.comp B.toEuclideanLin) w =
      (Aᴴ.toEuclideanLin.comp A.toEuclideanLin) w
    rw [← toLpLin_mul_same, ← toLpLin_mul_same, hGram]
  have hker : LinearMap.ker fA ≤ LinearMap.ker fB := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h0 := hinner v v
    simp only [hv, inner_zero_left] at h0
    exact inner_self_eq_zero.mp h0
  let L_lm : LinearMap.range fA →ₗ[ℂ] EuclideanSpace ℂ (Fin D) :=
    ((LinearMap.ker fA).liftQ fB hker).comp
      fA.quotKerEquivRange.symm.toLinearMap
  have hL_apply : ∀ v, L_lm ⟨fA v, LinearMap.mem_range_self fA v⟩ = fB v := by
    intro v
    change ((LinearMap.ker fA).liftQ fB hker)
        (fA.quotKerEquivRange.symm ⟨fA v, LinearMap.mem_range_self fA v⟩) =
      fB v
    rw [fA.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  have hL_inner : ∀ x y : LinearMap.range fA,
      ⟪L_lm x, L_lm y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    rw [hL_apply, hL_apply, hinner, Submodule.coe_inner]
  let L_iso : LinearMap.range fA →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D) :=
    LinearMap.isometryOfInner L_lm hL_inner
  let U := L_iso.extend
  have hU_eq : ∀ v, U (fA v) = fB v := by
    intro v
    have : U (fA v) = L_iso ⟨fA v, LinearMap.mem_range_self fA v⟩ :=
      LinearIsometry.extend_apply L_iso ⟨fA v, LinearMap.mem_range_self fA v⟩
    rw [this]
    simpa [L_iso] using hL_apply v
  let U_mat : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.toEuclideanLin.symm U.toLinearMap
  have h_U_lin : Matrix.toEuclideanLin U_mat = U.toLinearMap :=
    LinearEquiv.apply_symm_apply Matrix.toEuclideanLin U.toLinearMap
  have hU_unitary : U_matᴴ * U_mat = 1 := by
    apply Matrix.toEuclideanLin.injective
    ext1 v
    have hadj : U.toLinearMap.adjoint (U.toLinearMap v) = v :=
      ext_inner_right ℂ fun y => by
        rw [LinearMap.adjoint_inner_left]
        exact LinearIsometry.inner_map_map U v y
    rw [toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, h_U_lin, hadj]
    simp only [toLpLin_one, LinearMap.id_apply]
  have hU_mat_eq : U_mat * A = B := by
    apply Matrix.toEuclideanLin.injective
    ext1 v
    rw [toLpLin_mul_same, LinearMap.comp_apply, h_U_lin]
    exact hU_eq v
  refine ⟨⟨U_mat, Matrix.mem_unitaryGroup_iff'.2 hU_unitary⟩, ?_⟩
  exact hU_mat_eq.symm

/-- Packaged predicate saying that `V` together with the projective measurement `P`
realizes `E` as a Naimark dilation. -/
def IsNaimarkDilation {r : ℕ}
    (E : POVM D n)
    (V : Matrix (Fin D × Fin r) (Fin D) ℂ)
    (P : Fin n → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) : Prop :=
  Vᴴ * V = 1 ∧
  (∀ i, P i * P i = P i) ∧
  (∀ i, (P i)ᴴ = P i) ∧
  (∀ i j, i ≠ j → P i * P j = 0) ∧
  (∑ i, P i = 1) ∧
  (∀ i, Vᴴ * P i * V = E.ops i)

/-- The canonical dilation from `POVM.exists_naimark_dilation` satisfies
`POVM.IsNaimarkDilation`. -/
theorem isNaimarkDilation_naimark (E : POVM D n) :
    IsNaimarkDilation E E.naimarkIsometry (naimarkProjection (D := D)) := by
  refine ⟨E.naimarkIsometry_isometry, naimarkProjection_mul_self,
    naimarkProjection_hermitian, naimarkProjection_orthogonal,
    naimarkProjection_sum_eq_one, E.naimark_recovers_povm⟩

/-- The `i`-th system block of a dilation matrix `V : ℂ^D → ℂ^D ⊗ ℂ^n`. -/
def naimarkBlock (V : Matrix (Fin D × Fin n) (Fin D) ℂ) (i : Fin n) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun a b => V (a, i) b

@[simp]
theorem naimarkBlock_apply (V : Matrix (Fin D × Fin n) (Fin D) ℂ)
    (i : Fin n) (a b : Fin D) :
    naimarkBlock (D := D) (n := n) V i a b = V (a, i) b := rfl

/-- Reassembling the blocks of a dilation matrix via `stinespringV` recovers the
original matrix. -/
theorem stinespringV_naimarkBlock (V : Matrix (Fin D × Fin n) (Fin D) ℂ) :
    stinespringV (naimarkBlock (D := D) (n := n) V) = V := by
  ext ⟨a, i⟩ b
  simp [naimarkBlock, stinespringV_apply]

/-- The generic Stinespring matrix built from `K` recovers the block Gram matrix
when compressed by the `i`-th Naimark projector. -/
private theorem stinespring_conjTranspose_mul_naimarkProjection_mul
    (K : Fin n → Matrix (Fin D) (Fin D) ℂ) (i : Fin n) :
    (stinespringV K)ᴴ * naimarkProjection (D := D) i * stinespringV K = (K i)ᴴ * K i := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stinespringV_apply, naimarkProjection_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro q1 _
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single q1]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro p2 _ hp2
        simp [hp2]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · intro p1 _ hp1
      refine Finset.sum_eq_zero fun p2 _ => ?_
      simp [hp1]
    · intro h
      exact absurd (Finset.mem_univ q1) h
  · intro q2 _ hq2
    have hinner :
        (∑ p1 : Fin D, ∑ p2 : Fin n,
            star (K p2 p1 k) *
              (if p1 = q1 ∧ p2 = i ∧ q2 = i then (1 : ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun p1 _ => ?_
      refine Finset.sum_eq_zero fun p2 _ => ?_
      rw [if_neg (fun h => hq2 h.2.2)]
      ring
    rw [hinner, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Compressing a dilation matrix by the `i`-th canonical Naimark projector yields
its `i`-th block Gram matrix. -/
theorem naimarkBlock_conjTranspose_mul_naimarkProjection_mul
    (V : Matrix (Fin D × Fin n) (Fin D) ℂ) (i : Fin n) :
    Vᴴ * naimarkProjection (D := D) i * V =
      (naimarkBlock (D := D) (n := n) V i)ᴴ * naimarkBlock V i := by
  simpa [stinespringV_naimarkBlock, naimarkBlock] using
    stinespring_conjTranspose_mul_naimarkProjection_mul
      (D := D) (n := n) (K := naimarkBlock (D := D) (n := n) V) i

/-- The block-diagonal dilation isometry built from a family of unitary matrices
acting independently on each ancilla sector. -/
def sectorwiseUnitary (U : Fin n → Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix (Fin D × Fin n) (Fin D × Fin n) ℂ :=
  fun p q => if p.2 = q.2 then (U p.2 : Matrix (Fin D) (Fin D) ℂ) p.1 q.1 else 0

@[simp]
theorem sectorwiseUnitary_apply_same (U : Fin n → Matrix.unitaryGroup (Fin D) ℂ)
    (a b : Fin D) (i : Fin n) :
    sectorwiseUnitary (D := D) U (a, i) (b, i) = (U i : Matrix (Fin D) (Fin D) ℂ) a b := by
  simp [sectorwiseUnitary]

@[simp]
theorem sectorwiseUnitary_apply_ne (U : Fin n → Matrix.unitaryGroup (Fin D) ℂ)
    (a b : Fin D) {i j : Fin n} (hij : i ≠ j) :
    sectorwiseUnitary (D := D) U (a, i) (b, j) = 0 := by
  simp [sectorwiseUnitary, hij]

/-- `sectorwiseUnitary U` is an isometry on the dilated space. -/
theorem sectorwiseUnitary_isometry (U : Fin n → Matrix.unitaryGroup (Fin D) ℂ) :
    (sectorwiseUnitary (D := D) U)ᴴ * sectorwiseUnitary U = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sectorwiseUnitary,
    Fintype.sum_prod_type, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have hcollapse : ∀ c : Fin D,
        (∑ k : Fin n,
            star (if k = i then (U k : Matrix (Fin D) (Fin D) ℂ) c a else 0) *
              if k = i then (U k : Matrix (Fin D) (Fin D) ℂ) c b else 0) =
          star ((U i : Matrix (Fin D) (Fin D) ℂ) c a) *
            (U i : Matrix (Fin D) (Fin D) ℂ) c b := by
      intro c
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki]
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp_rw [hcollapse]
    have hU := congr_fun (congr_fun (Matrix.mem_unitaryGroup_iff'.mp (U i).prop) a) b
    simp only [Matrix.mul_apply, Matrix.one_apply] at hU
    simpa using hU
  · have hneq : (a, i) ≠ (b, j) := by
      intro h
      exact hij (by simpa using congrArg Prod.snd h)
    have hcollapse : ∀ c : Fin D,
        (∑ k : Fin n,
            star (if k = i then (U k : Matrix (Fin D) (Fin D) ℂ) c a else 0) *
              if k = j then (U k : Matrix (Fin D) (Fin D) ℂ) c b else 0) = 0 := by
      intro c
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hki : k = i
      · have hkj : k ≠ j := by
          intro hk
          exact hij (hki.symm.trans hk)
        have hij' : i ≠ j := by
          intro h
          exact hkj (hki.trans h)
        simp [hki, hij']
      · simp [hki]
    simp_rw [hcollapse]
    simp [hneq]

/-- Left-multiplying a Stinespring-style Naimark isometry by a sectorwise unitary
amounts to left-multiplying each Kraus block by the corresponding unitary. -/
theorem sectorwiseUnitary_mul_stinespringV
    (U : Fin n → Matrix.unitaryGroup (Fin D) ℂ)
    (K : Fin n → Matrix (Fin D) (Fin D) ℂ) :
    sectorwiseUnitary (D := D) U * stinespringV K =
      stinespringV (fun i => (U i : Matrix (Fin D) (Fin D) ℂ) * K i) := by
  ext ⟨a, i⟩ b
  simp only [Matrix.mul_apply, sectorwiseUnitary, stinespringV_apply,
    Fintype.sum_prod_type]
  have hcollapse : ∀ c : Fin D,
      (∑ j : Fin n,
          (if i = j then (U i : Matrix (Fin D) (Fin D) ℂ) a c else 0) * K j c b) =
        (U i : Matrix (Fin D) (Fin D) ℂ) a c * K i c b := by
    intro c
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hij : i ≠ j := by
        intro h
        exact hji h.symm
      simp [hij]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp_rw [hcollapse]

/-- If a dilation matrix `V` recovers the POVM effects via the canonical Naimark
projectors, then it differs from the canonical Naimark isometry by an isometry on the
larger space. -/
theorem exists_isometry_mul_naimarkIsometry_of_recovery
    (E : POVM D n)
    {V : Matrix (Fin D × Fin n) (Fin D) ℂ}
    (hV : ∀ i, Vᴴ * naimarkProjection (D := D) i * V = E.ops i) :
    ∃ W : Matrix (Fin D × Fin n) (Fin D × Fin n) ℂ,
      Wᴴ * W = 1 ∧
      V = W * E.naimarkIsometry := by
  have hGram : ∀ i : Fin n,
      (naimarkBlock (D := D) (n := n) V i)ᴴ * naimarkBlock V i =
        (E.naimarkKraus i)ᴴ * E.naimarkKraus i := by
    intro i
    calc
      (naimarkBlock (D := D) (n := n) V i)ᴴ * naimarkBlock V i
          = Vᴴ * naimarkProjection (D := D) i * V :=
            (naimarkBlock_conjTranspose_mul_naimarkProjection_mul
              (D := D) (n := n) V i).symm
      _ = E.ops i := hV i
      _ = (E.naimarkKraus i)ᴴ * E.naimarkKraus i := E.naimarkKraus_spec i
  choose U hU using fun i : Fin n =>
    exists_unitary_mul_eq_of_conjTranspose_mul_eq
      (B := naimarkBlock (D := D) (n := n) V i) (A := E.naimarkKraus i) (hGram i)
  refine ⟨sectorwiseUnitary (D := D) U, sectorwiseUnitary_isometry (D := D) U, ?_⟩
  calc
    V = stinespringV (naimarkBlock (D := D) (n := n) V) :=
      (stinespringV_naimarkBlock (D := D) (n := n) V).symm
    _ = stinespringV (fun i => (U i : Matrix (Fin D) (Fin D) ℂ) * E.naimarkKraus i) := by
      congr 1
      funext i
      exact hU i
    _ = sectorwiseUnitary (D := D) U * E.naimarkIsometry := by
      symm
      simpa [POVM.naimarkIsometry] using
        sectorwiseUnitary_mul_stinespringV (D := D) (n := n) U E.naimarkKraus

end POVM
