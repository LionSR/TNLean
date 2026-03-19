/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.LindbladForm
import TNLean.Channel.Semigroup.Kernel
import TNLean.Channel.FixedPoint.Algebra

/-!
# Kernel of the Liouvillian — Wolf Theorem 7.2

This file begins the formalization of Wolf Theorem 7.2 on the kernel of the
Liouvillian. For a Lindblad form

$$
L(\rho) = i(\rho H - H \rho) + \sum_j \left(L_j \rho L_j^\dagger -
  \frac{1}{2} L_j^\dagger L_j \rho - \frac{1}{2} \rho L_j^\dagger L_j\right),
$$

we define the adjoint / Heisenberg generator `L*` by the trace-pairing identity

$$
\operatorname{tr}(\rho \, L^*(A)) = \operatorname{tr}(L(\rho) \, A).
$$

With the Schrödinger-picture sign convention used in `LindbladForm.toLinearMap`,
the Hamiltonian term in `L*` is `i (H A - A H)`.

## Main results

* `LindbladForm.toAdjointLinearMap` — the adjoint / Heisenberg generator.
* `LindbladForm.trace_mul_toAdjointLinearMap_eq_trace_toLinearMap_mul` — the
  trace-pairing identity characterizing `L*`.
* `LindbladForm.mem_adjointKernel_of_mem_commutant` — if `A` commutes with the
  Hamiltonian, the Lindblad operators, and their adjoints, then `L*(A) = 0`
  (Wolf Theorem 7.2, easy direction).
* `LindbladForm.adjointKernel_eq_commutant_of_hasFaithfulStationaryState` — the
  Wolf Theorem 7.2, faithful direction.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix Finset

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

namespace LindbladForm

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The dissipative part of the adjoint / Heisenberg generator for a single
Lindblad operator. -/
def adjointDissipator (Lop : Mat) (A : Mat) : Mat :=
  Lopᴴ * A * Lop -
  (1 / 2 : ℂ) • (Lopᴴ * Lop * A) -
  (1 / 2 : ℂ) • (A * (Lopᴴ * Lop))

theorem adjointDissipator_add (Lop : Mat) (A B : Mat) :
    adjointDissipator Lop (A + B) = adjointDissipator Lop A + adjointDissipator Lop B := by
  simp only [adjointDissipator, mul_add, add_mul, smul_add]
  abel

theorem adjointDissipator_smul (Lop : Mat) (c : ℂ) (A : Mat) :
    adjointDissipator Lop (c • A) = c • adjointDissipator Lop A := by
  simp only [adjointDissipator, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
  rw [mul_comm ((1 : ℂ) / 2) c]

@[simp] theorem adjointDissipator_conjTranspose (Lop : Mat) (A : Mat) :
    adjointDissipator Lop Aᴴ = (adjointDissipator Lop A)ᴴ := by
  simp only [adjointDissipator, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    one_div, star_inv₀, star_ofNat, Matrix.mul_assoc]
  abel_nf

/-- The adjoint / Heisenberg generator attached to a Lindblad form.

It is characterized below by the trace-pairing identity
`trace (ρ * F.toAdjointLinearMap A) = trace (F.toLinearMap ρ * A)`. -/
def toAdjointLinearMap (F : LindbladForm D) :
    Mat →ₗ[ℂ] Mat :=
  Kraus.adjointMapLM F.L - LinearMap.mulRight ℂ F.toGeneratorDecomp.κ -
    LinearMap.mulLeft ℂ F.toGeneratorDecomp.κᴴ

@[simp] theorem toAdjointLinearMap_apply_raw (F : LindbladForm D) (A : Mat) :
    F.toAdjointLinearMap A =
      Kraus.adjointMap F.L A - A * F.toGeneratorDecomp.κ - F.toGeneratorDecomp.κᴴ * A := by
  simp only [toAdjointLinearMap, LinearMap.sub_apply, Kraus.adjointMapLM_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply]

/-- Explicit Heisenberg-picture formula for the adjoint generator. -/
theorem toAdjointLinearMap_apply (F : LindbladForm D) (A : Mat) :
    F.toAdjointLinearMap A =
      Complex.I • (F.H * A - A * F.H) + ∑ j : Fin F.r, adjointDissipator (F.L j) A := by
  rw [toAdjointLinearMap_apply_raw]
  simp only [Kraus.adjointMap, LindbladForm.toGeneratorDecomp]
  set S : Mat := ∑ j : Fin F.r, (F.L j)ᴴ * F.L j with hS_def
  have hS_herm : Sᴴ = S := by
    rw [hS_def, Matrix.conjTranspose_sum]
    congr 1
    ext j
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hκ_conj :
      (Complex.I • F.H + (1 / 2 : ℂ) • S)ᴴ =
        (-Complex.I) • F.H + (1 / 2 : ℂ) • S := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      F.H_hermitian, hS_herm]
    congr 1
    · change star Complex.I • F.H = (-Complex.I) • F.H
      rw [Complex.star_def, Complex.conj_I, neg_smul]
    · change star (1 / 2 : ℂ) • S = (1 / 2 : ℂ) • S
      simp only [one_div, star_inv₀, star_ofNat]
  have hsum :
      (∑ j : Fin F.r, adjointDissipator (F.L j) A) =
        (∑ j : Fin F.r, (F.L j)ᴴ * A * F.L j) -
          (1 / 2 : ℂ) • (S * A) -
          (1 / 2 : ℂ) • (A * S) := by
    simp only [adjointDissipator, Finset.sum_sub_distrib]
    congr 1
    · congr 1
      rw [← Finset.smul_sum]
      congr 1
      rw [hS_def, Finset.sum_mul]
    · rw [← Finset.smul_sum]
      congr 1
      rw [hS_def, Finset.mul_sum]
  rw [hS_def] at hsum
  rw [show (Complex.I • F.H + (1 / 2 : ℂ) • ∑ j : Fin F.r, (F.L j)ᴴ * F.L j)ᴴ =
      (-Complex.I) • F.H + (1 / 2 : ℂ) • S by simpa [hS_def] using hκ_conj]
  rw [hsum]
  rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
    smul_sub]
  simp only [sub_eq_add_neg, neg_smul]
  abel

/-- The trace-pairing identity characterizing `toAdjointLinearMap`. -/
theorem trace_mul_toAdjointLinearMap_eq_trace_toLinearMap_mul
    (F : LindbladForm D) (ρ A : Mat) :
    Matrix.trace (ρ * F.toAdjointLinearMap A) = Matrix.trace (F.toLinearMap ρ * A) := by
  rw [F.toLinearMap_eq_generatorDecomp]
  have hcp :
      Matrix.trace (ρ * Kraus.adjointMap F.L A) =
        Matrix.trace ((∑ j : Fin F.r, F.L j * ρ * (F.L j)ᴴ) * A) := by
    simpa [Kraus.map, Kraus.adjointMap, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using
        (Kraus.trace_mul_map_eq_trace_adjointMap_mul
          (K := fun j : Fin F.r => (F.L j)ᴴ) ρ A)
  have hright :
      Matrix.trace (ρ * (A * F.toGeneratorDecomp.κ)) =
        Matrix.trace ((F.toGeneratorDecomp.κ * ρ) * A) := by
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle ρ A F.toGeneratorDecomp.κ)
  have hleft :
      Matrix.trace (ρ * (F.toGeneratorDecomp.κᴴ * A)) =
        Matrix.trace ((ρ * F.toGeneratorDecomp.κᴴ) * A) := by
    simp only [Matrix.mul_assoc]
  calc
    Matrix.trace (ρ * F.toAdjointLinearMap A)
        = Matrix.trace (ρ * Kraus.adjointMap F.L A) -
            Matrix.trace (ρ * (A * F.toGeneratorDecomp.κ)) -
            Matrix.trace (ρ * (F.toGeneratorDecomp.κᴴ * A)) := by
          rw [toAdjointLinearMap_apply_raw, Matrix.mul_sub, Matrix.mul_sub,
            Matrix.trace_sub, Matrix.trace_sub]
    _ = Matrix.trace ((∑ j : Fin F.r, F.L j * ρ * (F.L j)ᴴ) * A) -
          Matrix.trace ((F.toGeneratorDecomp.κ * ρ) * A) -
          Matrix.trace ((ρ * F.toGeneratorDecomp.κᴴ) * A) := by
        rw [hcp, hright, hleft]
    _ = Matrix.trace (F.toGeneratorDecomp.toLinearMap ρ * A) := by
        rw [GeneratorDecomp.toLinearMap_apply, Matrix.sub_mul, Matrix.sub_mul,
          Matrix.trace_sub, Matrix.trace_sub]
        rfl

@[simp] theorem toAdjointLinearMap_conjTranspose (F : LindbladForm D) (A : Mat) :
    F.toAdjointLinearMap Aᴴ = (F.toAdjointLinearMap A)ᴴ := by
  rw [toAdjointLinearMap_apply, toAdjointLinearMap_apply]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_sum, adjointDissipator_conjTranspose]
  rw [F.H_hermitian]
  congr 1
  calc
    Complex.I • (F.H * Aᴴ - Aᴴ * F.H)
        = Complex.I • (-(Aᴴ * F.H - F.H * Aᴴ)) := by
            congr 1
            abel
    _ = -(Complex.I • (Aᴴ * F.H - F.H * Aᴴ)) := by
            rw [smul_neg]
    _ = (-Complex.I) • (Aᴴ * F.H - F.H * Aᴴ) := by
            rw [← neg_smul]
    _ = star Complex.I • (Aᴴ * F.H - F.H * Aᴴ) := by
            simp

/-- The commutant of the Hamiltonian, the Lindblad operators, and their adjoints. -/
def commutant (F : LindbladForm D) : Set Mat :=
  {A | A * F.H = F.H * A ∧
      ∀ j : Fin F.r, A * F.L j = F.L j * A ∧ A * (F.L j)ᴴ = (F.L j)ᴴ * A}

@[simp] theorem mem_commutant (F : LindbladForm D) (A : Mat) :
    A ∈ F.commutant ↔
      A * F.H = F.H * A ∧
      ∀ j : Fin F.r, A * F.L j = F.L j * A ∧ A * (F.L j)ᴴ = (F.L j)ᴴ * A :=
  Iff.rfl

/-- The kernel of the adjoint generator, viewed as a set. -/
def adjointKernel (F : LindbladForm D) : Set Mat :=
  {A | F.toAdjointLinearMap A = 0}

@[simp] theorem mem_adjointKernel (F : LindbladForm D) (A : Mat) :
    A ∈ F.adjointKernel ↔ F.toAdjointLinearMap A = 0 :=
  Iff.rfl

private theorem adjointDissipator_eq_zero_of_commute {Lop A : Mat}
    (hL : A * Lop = Lop * A) (hLstar : A * Lopᴴ = Lopᴴ * A) :
    adjointDissipator Lop A = 0 := by
  unfold adjointDissipator
  have h1 : Lopᴴ * A * Lop = Lopᴴ * Lop * A := by
    calc
      Lopᴴ * A * Lop = Lopᴴ * (A * Lop) := by simp [Matrix.mul_assoc]
      _ = Lopᴴ * (Lop * A) := by rw [hL]
      _ = Lopᴴ * Lop * A := by simp [Matrix.mul_assoc]
  have h2 : A * (Lopᴴ * Lop) = Lopᴴ * Lop * A := by
    calc
      A * (Lopᴴ * Lop) = (A * Lopᴴ) * Lop := by simp [Matrix.mul_assoc]
      _ = (Lopᴴ * A) * Lop := by rw [hLstar]
      _ = Lopᴴ * (A * Lop) := by simp [Matrix.mul_assoc]
      _ = Lopᴴ * (Lop * A) := by rw [hL]
      _ = Lopᴴ * Lop * A := by simp [Matrix.mul_assoc]
  rw [h1, h2]
  let M : Mat := Lopᴴ * Lop * A
  change M - (1 / 2 : ℂ) • M - (1 / 2 : ℂ) • M = 0
  calc
    M - (1 / 2 : ℂ) • M - (1 / 2 : ℂ) • M
        = ((1 : ℂ) • M - (1 / 2 : ℂ) • M) - (1 / 2 : ℂ) • M := by simp
    _ = (((1 : ℂ) - (1 / 2 : ℂ)) • M) - (1 / 2 : ℂ) • M := by
          rw [← sub_smul]
    _ = (((1 : ℂ) - (1 / 2 : ℂ) - (1 / 2 : ℂ)) • M) := by
          rw [← sub_smul]
    _ = 0 := by
          norm_num

/-- Wolf Theorem 7.2, easy direction: the commutant lies in the kernel of the
adjoint generator. -/
theorem mem_adjointKernel_of_mem_commutant (F : LindbladForm D) {A : Mat}
    (hA : A ∈ F.commutant) :
    A ∈ F.adjointKernel := by
  rcases hA with ⟨hH, hL⟩
  rw [adjointKernel, Set.mem_setOf_eq, toAdjointLinearMap_apply]
  have hHterm : Complex.I • (F.H * A - A * F.H) = 0 := by
    rw [← hH]
    simp
  have hsum : ∑ j : Fin F.r, adjointDissipator (F.L j) A = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _hj
    exact adjointDissipator_eq_zero_of_commute (hL j).1 (hL j).2
  rw [hHterm, hsum]
  simp

/-- Wolf Theorem 7.2, easy direction as a set inclusion. -/
theorem commutant_subset_adjointKernel (F : LindbladForm D) :
    F.commutant ⊆ F.adjointKernel := by
  intro A hA
  exact F.mem_adjointKernel_of_mem_commutant hA

/-- `κ + κ† = Σⱼ Lⱼ†Lⱼ` for the generator decomposition of a Lindblad form.
This follows from `κ = iH + ½S` and `κ† = −iH + ½S` with `S = Σⱼ Lⱼ†Lⱼ`. -/
private theorem κ_add_conjTranspose_κ (F : LindbladForm D) :
    F.toGeneratorDecomp.κ + F.toGeneratorDecomp.κᴴ =
      ∑ j : Fin F.r, (F.L j)ᴴ * F.L j := by
  set S : Mat := ∑ j : Fin F.r, (F.L j)ᴴ * F.L j with hS_def
  have hS_herm : Sᴴ = S := by
    rw [hS_def, Matrix.conjTranspose_sum]
    congr 1; ext j
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  change Complex.I • F.H + (1 / 2 : ℂ) • S +
    (Complex.I • F.H + (1 / 2 : ℂ) • S)ᴴ = S
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    F.H_hermitian, hS_herm]
  simp only [Complex.star_def, Complex.conj_I, one_div, star_inv₀, star_ofNat]
  have h1 : (-(Complex.I : ℂ)) • F.H = -Complex.I • F.H := rfl
  rw [h1, neg_smul]
  have h2 : Complex.I • F.H + (2 : ℂ)⁻¹ • S + (-(Complex.I • F.H) + (2 : ℂ)⁻¹ • S) =
      (2 : ℂ)⁻¹ • S + (2 : ℂ)⁻¹ • S := by abel
  rw [h2, ← two_smul ℂ ((2 : ℂ)⁻¹ • S), smul_smul]
  norm_num

/-- **Lindblad identity** (Wolf Eq. 7.27 variant).

For any `A` in the adjoint kernel of a Lindblad form `F`, we have
`F.toAdjointLinearMap (Aᴴ * A) = ∑ⱼ (A * F.L j − F.L j * A)ᴴ * (A * F.L j − F.L j * A)`.

The proof uses `L*(A) = 0`, hence `φ*(A) = A κ + κ† A`, and expands both sides
to verify they coincide. -/
private theorem toAdjointLinearMap_conjTranspose_mul_self_eq_sum_commutator
    (F : LindbladForm D) {A : Mat}
    (hA : F.toAdjointLinearMap A = 0) :
    F.toAdjointLinearMap (Aᴴ * A) =
      ∑ j : Fin F.r,
        (A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A) := by
  -- Set up notation
  set κ := F.toGeneratorDecomp.κ
  set φ := Kraus.adjointMap F.L
  set S := ∑ j : Fin F.r, (F.L j)ᴴ * F.L j with hS_def
  -- Key fact: κ + κ† = S
  have hκS : κ + κᴴ = S := F.κ_add_conjTranspose_κ
  -- From L*(A) = 0: φ(A) = Aκ + κ†A
  have hφA : φ A = A * κ + κᴴ * A := by
    have h := hA
    rw [toAdjointLinearMap_apply_raw] at h
    have hsub : φ A - A * κ - κᴴ * A = 0 := h
    have : φ A = φ A - A * κ - κᴴ * A + (A * κ + κᴴ * A) := by abel
    rw [this, hsub, zero_add]
  -- From L*(A†) = 0: φ(A†) = A†κ + κ†A†
  have hφAstar : φ Aᴴ = Aᴴ * κ + κᴴ * Aᴴ := by
    have hAstar_ker : F.toAdjointLinearMap Aᴴ = 0 := by
      rw [toAdjointLinearMap_conjTranspose]; simp [hA]
    rw [toAdjointLinearMap_apply_raw] at hAstar_ker
    have hsub : φ Aᴴ - Aᴴ * κ - κᴴ * Aᴴ = 0 := hAstar_ker
    have : φ Aᴴ = φ Aᴴ - Aᴴ * κ - κᴴ * Aᴴ + (Aᴴ * κ + κᴴ * Aᴴ) := by abel
    rw [this, hsub, zero_add]
  -- Strategy: show LHS = φ(A†A) - φ(A†)·A - A†·φ(A) + A†·S·A = RHS
  -- where the middle identity uses hφA, hφAstar, hκS.
  -- Part 1: Expand the RHS into sums
  have hRHS_expand : ∀ j : Fin F.r,
      (A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A) =
      (F.L j)ᴴ * (Aᴴ * A) * F.L j - ((F.L j)ᴴ * Aᴴ * F.L j) * A -
      Aᴴ * ((F.L j)ᴴ * A * F.L j) + Aᴴ * ((F.L j)ᴴ * F.L j) * A := by
    intro j
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  -- Part 2: Sum the expansion and factor into φ, S
  have hRHS_sum :
      (∑ j, (A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A)) =
      φ (Aᴴ * A) - φ Aᴴ * A - Aᴴ * φ A + Aᴴ * S * A := by
    simp_rw [hRHS_expand]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      · congr 1
        -- ∑ (F.L j)ᴴ * Aᴴ * F.L j * A = φ(A†) · A
        exact (Finset.sum_mul _ _ _).symm
      -- A† · ∑ (F.L j)ᴴ * A * F.L j = A† · φ(A)
      exact (Finset.mul_sum _ _ _).symm
    -- ∑ A† · ((F.L j)ᴴ * F.L j) * A = A† · S · A
    rw [← Finset.sum_mul, ← Finset.mul_sum, hS_def]
  -- Part 3: Connect LHS to the same expression
  rw [toAdjointLinearMap_apply_raw, hRHS_sum]
  -- Goal: φ(A†A) - A†A·κ - κ†·A†A = φ(A†A) - φ(A†)·A - A†·φ(A) + A†·S·A
  -- Substitute φ(A) and φ(A†) and use κ + κ† = S
  rw [hφA, hφAstar]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  -- Cancel using κ + κ† = S
  -- Goal should now be a pure matrix additive identity with φ(A†A), κ, κᴴ, S
  -- The key cancellation: A†κA + A†κ†A = A†SA (since κ + κ† = S)
  rw [show S = κ + κᴴ from hκS.symm]
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

/-- Sum of `[A, Lⱼ]ᴴ [A, Lⱼ]` is positive semidefinite. -/
private theorem posSemidef_sum_commutator_conjTranspose_mul_self
    (F : LindbladForm D) (A : Mat) :
    (∑ j : Fin F.r,
      (A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A)).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ =>
    Matrix.posSemidef_conjTranspose_mul_self _

/-- Each commutator `[A, Lⱼ] = 0` when the sum of squares vanishes. -/
private theorem each_commutator_eq_zero_of_sum_eq_zero
    (F : LindbladForm D) (A : Mat)
    (h : ∑ j : Fin F.r,
      (A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A) = 0) :
    ∀ j : Fin F.r, A * F.L j = F.L j * A := by
  intro j
  have hj : A * F.L j - F.L j * A = 0 := by
    have h_psd_j := Matrix.posSemidef_conjTranspose_mul_self (A * F.L j - F.L j * A)
    have h_each_nonneg : ∀ k : Fin F.r,
        0 ≤ ((A * F.L k - F.L k * A)ᴴ * (A * F.L k - F.L k * A)).trace.re :=
      fun k => (Complex.le_def.mp
        (Matrix.posSemidef_conjTranspose_mul_self (A * F.L k - F.L k * A)).trace_nonneg).1
    have h_tr_sum_re :
        (∑ k : Fin F.r,
          ((A * F.L k - F.L k * A)ᴴ * (A * F.L k - F.L k * A)).trace.re) = 0 := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, h]; simp
    have h_tr_re :
        ((A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A)).trace.re = 0 :=
      le_antisymm
        (by linarith [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h_each_nonneg k)
            |>.mp h_tr_sum_re j (Finset.mem_univ j)])
        (h_each_nonneg j)
    have h_tr_zero :
        ((A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A)).trace = 0 :=
      Complex.ext h_tr_re (Complex.le_def.mp h_psd_j.trace_nonneg).2.symm
    exact Matrix.conjTranspose_mul_self_eq_zero.mp (h_psd_j.trace_eq_zero_iff.mp h_tr_zero)
  exact sub_eq_zero.mp hj

/-- Wolf Theorem 7.2, faithful direction.

The proof uses the direct algebraic approach (Wolf Eq. 7.27):

1. From `L*(A) = 0`, derive `L*(Aᴴ) = 0` (conjugation property).
2. Prove the **Lindblad identity**: `L*(Aᴴ A) = Σⱼ [A, Lⱼ]ᴴ [A, Lⱼ]`.
3. The RHS is PSD (sum of `X†X`), hence `L*(Aᴴ A) ≥ 0`.
4. By the trace pairing: `tr(ρ · L*(Aᴴ A)) = tr(L(ρ) · Aᴴ A) = 0`.
5. By faithfulness of ρ: `L*(Aᴴ A) = 0`, hence `Σⱼ [A, Lⱼ]ᴴ [A, Lⱼ] = 0`.
6. Each `[A, Lⱼ] = 0` (sum of PSD = 0 ⇒ each = 0).
7. Similarly, `[Aᴴ, Lⱼ] = 0` implies `[A, Lⱼᴴ] = 0`.
8. From `L*(A) = 0` and `[A, Lⱼ] = [A, Lⱼᴴ] = 0`, get `[H, A] = 0`. -/
theorem mem_commutant_of_mem_adjointKernel_of_hasFaithfulStationaryState
    (F : LindbladForm D)
    (hstat : HasFaithfulStationaryState (D := D) F.toLinearMap)
    {A : Mat} (hA : A ∈ F.adjointKernel) :
    A ∈ F.commutant := by
  -- Extract the faithful stationary state
  obtain ⟨ρ, hρ_dm, hρ_pd, hρ_ker⟩ := hstat
  -- Extract L*(A) = 0
  have hLA : F.toAdjointLinearMap A = 0 := hA
  -- Step 1: L*(A†) = 0
  have hLAstar : F.toAdjointLinearMap Aᴴ = 0 := by
    rw [toAdjointLinearMap_conjTranspose, hLA]; simp
  -- Step 2: L*(A†A) = Σⱼ [A,Lⱼ]†[A,Lⱼ]
  have hid := toAdjointLinearMap_conjTranspose_mul_self_eq_sum_commutator F hLA
  -- Step 3: L*(A†A) is PSD
  have hpsd : (F.toAdjointLinearMap (Aᴴ * A)).PosSemidef := by
    rw [hid]; exact posSemidef_sum_commutator_conjTranspose_mul_self F A
  -- Step 4: trace(ρ · L*(A†A)) = 0
  have htr : Matrix.trace (ρ * F.toAdjointLinearMap (Aᴴ * A)) = 0 := by
    rw [trace_mul_toAdjointLinearMap_eq_trace_toLinearMap_mul, hρ_ker, Matrix.zero_mul,
      Matrix.trace_zero]
  -- Step 5: L*(A†A) = 0
  have hLAA : F.toAdjointLinearMap (Aᴴ * A) = 0 :=
    Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hpsd hρ_pd htr
  -- Step 6: Each [A, Lⱼ] = 0
  have hcomm_sum_zero : ∑ j : Fin F.r,
      (A * F.L j - F.L j * A)ᴴ * (A * F.L j - F.L j * A) = 0 := by
    rw [← hid, hLAA]
  have hAL : ∀ j : Fin F.r, A * F.L j = F.L j * A :=
    each_commutator_eq_zero_of_sum_eq_zero F A hcomm_sum_zero
  -- Step 7: Similarly for A†, get [A†, Lⱼ] = 0, hence [A, Lⱼ†] = 0
  have hid' := toAdjointLinearMap_conjTranspose_mul_self_eq_sum_commutator F hLAstar
  simp only [Matrix.conjTranspose_conjTranspose] at hid'
  have hpsd' : (F.toAdjointLinearMap (A * Aᴴ)).PosSemidef := by
    rw [hid']; exact posSemidef_sum_commutator_conjTranspose_mul_self F Aᴴ
  have htr' : Matrix.trace (ρ * F.toAdjointLinearMap (A * Aᴴ)) = 0 := by
    rw [trace_mul_toAdjointLinearMap_eq_trace_toLinearMap_mul, hρ_ker, Matrix.zero_mul,
      Matrix.trace_zero]
  have hLAAstar : F.toAdjointLinearMap (A * Aᴴ) = 0 :=
    Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hpsd' hρ_pd htr'
  have hcomm_sum_zero' : ∑ j : Fin F.r,
      (Aᴴ * F.L j - F.L j * Aᴴ)ᴴ * (Aᴴ * F.L j - F.L j * Aᴴ) = 0 := by
    rw [← hid', hLAAstar]
  have hAstarL : ∀ j : Fin F.r, Aᴴ * F.L j = F.L j * Aᴴ :=
    each_commutator_eq_zero_of_sum_eq_zero F Aᴴ hcomm_sum_zero'
  -- From [A†, Lⱼ] = 0, take conjugate transpose to get [Lⱼ†, A] = 0
  have hALstar : ∀ j : Fin F.r, A * (F.L j)ᴴ = (F.L j)ᴴ * A := by
    intro j
    have h := congrArg Matrix.conjTranspose (hAstarL j)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
    exact h.symm
  -- Step 8: [H, A] = 0
  have hHA : A * F.H = F.H * A := by
    have hLAexp := hLA
    rw [toAdjointLinearMap_apply] at hLAexp
    have hsum_zero : ∑ j : Fin F.r, adjointDissipator (F.L j) A = 0 :=
      Finset.sum_eq_zero fun j _ => adjointDissipator_eq_zero_of_commute (hAL j) (hALstar j)
    rw [hsum_zero, add_zero] at hLAexp
    -- hLAexp : Complex.I • (F.H * A - A * F.H) = 0
    have h : F.H * A - A * F.H = 0 := by
      rwa [smul_eq_zero, or_iff_right Complex.I_ne_zero] at hLAexp
    exact eq_of_sub_eq_zero h |>.symm
  -- Assemble the commutant membership
  rw [mem_commutant]
  exact ⟨hHA, fun j => ⟨hAL j, hALstar j⟩⟩

/-- Wolf Theorem 7.2 with the current formalization status: under a faithful
stationary state, the adjoint kernel equals the commutant. -/
theorem adjointKernel_eq_commutant_of_hasFaithfulStationaryState
    (F : LindbladForm D)
    (hstat : HasFaithfulStationaryState (D := D) F.toLinearMap) :
    F.adjointKernel = F.commutant := by
  ext A
  constructor
  · intro hA
    exact F.mem_commutant_of_mem_adjointKernel_of_hasFaithfulStationaryState hstat hA
  · intro hA
    exact F.mem_adjointKernel_of_mem_commutant hA

end LindbladForm
