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
  faithful-direction statement, presently reduced to one remaining sorry.
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

/-- Wolf Theorem 7.2, faithful direction.

The intended proof is the standard argument from Wolf:

1. choose a generic time `t > 0` with `Fix (exp (t L*)) = ker L*`,
2. use `FixedPoint.Algebra` to obtain a `*`-algebra structure on that fixed-point set,
3. deduce that `Aᴴ * A` and `A * Aᴴ` are again fixed,
4. combine this with the Lindblad identity analogous to Wolf Eq. (7.27) to show
   that `A` commutes with each Lindblad operator and its adjoint,
5. use the Hamiltonian part of `L*(A) = 0` to conclude that `A` also commutes
   with `H`.

The remaining gap is the current semigroup-to-channel interface for the generic-time
fixed-point algebra argument. -/
theorem mem_commutant_of_mem_adjointKernel_of_hasFaithfulStationaryState
    (F : LindbladForm D)
    (hstat : HasFaithfulStationaryState (D := D) F.toLinearMap)
    {A : Mat} (hA : A ∈ F.adjointKernel) :
    A ∈ F.commutant := by
  sorry

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
