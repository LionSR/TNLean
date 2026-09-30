/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ThreeFormSpan

/-!
# Projector insertion on the three-form span

This file proves the two identities satisfied by the three-form span of an
idempotent `E` and a nonunital algebra `A` with `E A E = 0`: products of two
elements of the span admit an insertion of `E`, and every element has zero
trace against `E`.  Applied to the blocked residual slices of an MPU, these give
the contractions `simple1` and `simple2` of arXiv:1703.09188, Proposition
`blockingsimple`, lines 415--427.

## Main statements

* `MPOTensor.mul_eq_mul_projector_mul_of_mem_threeFormSubmodule`
* `MPOTensor.trace_mul_projector_eq_zero_of_mem_threeFormSubmodule`
* `MPOTensor.IsMPU.blockTensor_sq_isMPUSimple_of_normalizedDiagonal_eq_vecMulVec`
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ}

section ThreeFormInsertion

variable {n : Type*} [Fintype n] [DecidableEq n]

private def threeFormGeneratorSet (E : Matrix n n ℂ)
    (A : NonUnitalSubalgebra ℂ (Matrix n n ℂ)) : Set (Matrix n n ℂ) :=
  {x | ∃ a : A, x = E * (a : Matrix n n ℂ)} ∪
    {x | ∃ a : A, x = (a : Matrix n n ℂ) * E} ∪
      {x | ∃ a b : A, x = (a : Matrix n n ℂ) * E * (b : Matrix n n ℂ)}

private theorem threeFormSubmodule_eq_span_generatorSet
    (E : Matrix n n ℂ) (A : NonUnitalSubalgebra ℂ (Matrix n n ℂ)) :
    threeFormSubmodule E A = Submodule.span ℂ (threeFormGeneratorSet E A) := by
  simp only [threeFormSubmodule, projectorMulResidualSubmodule,
    residualMulProjectorSubmodule, residualMulProjectorMulResidualSubmodule,
    threeFormGeneratorSet, Submodule.span_union]

omit [DecidableEq n] in
private theorem threeForm_generator_mul_eq_mul_projector_mul
    (E : Matrix n n ℂ) (A : NonUnitalSubalgebra ℂ (Matrix n n ℂ))
    (hE : E * E = E) (hEAE : ∀ a : A, E * (a : Matrix n n ℂ) * E = 0)
    {x y : Matrix n n ℂ} (hx : x ∈ threeFormGeneratorSet E A)
    (hy : y ∈ threeFormGeneratorSet E A) : x * y = x * E * y := by
  classical
  have hcollapse (X : Matrix n n ℂ) : X * E * E = X * E := by
    rw [Matrix.mul_assoc, hE]
  rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, b, rfl⟩ <;>
    rcases hy with (⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, e, rfl⟩
  · simp only [← mul_assoc, hEAE, zero_mul]
  · have hac : E * ((a : Matrix n n ℂ) * c : Matrix n n ℂ) * E = 0 :=
      hEAE ⟨(a : Matrix n n ℂ) * c, A.mul_mem a.property c.property⟩
    rw [show (E * (a : Matrix n n ℂ)) * ((c : Matrix n n ℂ) * E) =
      E * ((a : Matrix n n ℂ) * c) * E by simp [mul_assoc], hac]
    simp only [← mul_assoc, hEAE, zero_mul]
  · have hac : E * ((a : Matrix n n ℂ) * c : Matrix n n ℂ) * E = 0 :=
      hEAE ⟨(a : Matrix n n ℂ) * c, A.mul_mem a.property c.property⟩
    rw [show (E * (a : Matrix n n ℂ)) * ((c : Matrix n n ℂ) * E * e) =
      (E * ((a : Matrix n n ℂ) * c) * E) * e by simp [mul_assoc], hac, zero_mul]
    simp only [← mul_assoc, hEAE, zero_mul]
  · symm
    rw [hcollapse]
  · rw [show ((a : Matrix n n ℂ) * E) * ((c : Matrix n n ℂ) * E) =
      (a : Matrix n n ℂ) * (E * c * E) by simp [mul_assoc], hEAE, mul_zero]
    rw [hcollapse]
    rw [show ((a : Matrix n n ℂ) * E) * ((c : Matrix n n ℂ) * E) =
      (a : Matrix n n ℂ) * (E * c * E) by simp [mul_assoc], hEAE, mul_zero]
  · rw [show ((a : Matrix n n ℂ) * E) * ((c : Matrix n n ℂ) * E * e) =
      (a : Matrix n n ℂ) * (E * c * E) * e by simp [mul_assoc], hEAE, mul_zero,
      zero_mul]
    rw [hcollapse]
    rw [show ((a : Matrix n n ℂ) * E) * ((c : Matrix n n ℂ) * E * e) =
      (a : Matrix n n ℂ) * (E * c * E) * e by simp [mul_assoc], hEAE, mul_zero,
      zero_mul]
  · rw [show ((a : Matrix n n ℂ) * E * b) * (E * (c : Matrix n n ℂ)) =
      (a : Matrix n n ℂ) * (E * b * E) * c by simp [mul_assoc], hEAE, mul_zero,
      zero_mul]
    rw [show ((a : Matrix n n ℂ) * E * b) * E * (E * (c : Matrix n n ℂ)) =
      (a : Matrix n n ℂ) * (E * b * E) * (E * c) by simp [mul_assoc], hEAE,
      mul_zero, zero_mul]
  · have hbc : E * ((b : Matrix n n ℂ) * c : Matrix n n ℂ) * E = 0 :=
      hEAE ⟨(b : Matrix n n ℂ) * c, A.mul_mem b.property c.property⟩
    rw [show ((a : Matrix n n ℂ) * E * b) * ((c : Matrix n n ℂ) * E) =
      (a : Matrix n n ℂ) * (E * ((b : Matrix n n ℂ) * c) * E) by simp [mul_assoc],
      hbc, mul_zero]
    rw [show ((a : Matrix n n ℂ) * E * b) * E * ((c : Matrix n n ℂ) * E) =
      (a : Matrix n n ℂ) * (E * b * E) * c * E by simp [mul_assoc], hEAE,
      mul_zero, zero_mul]
    simp
  · have hbc : E * ((b : Matrix n n ℂ) * c : Matrix n n ℂ) * E = 0 :=
      hEAE ⟨(b : Matrix n n ℂ) * c, A.mul_mem b.property c.property⟩
    rw [show ((a : Matrix n n ℂ) * E * b) * ((c : Matrix n n ℂ) * E * e) =
      (a : Matrix n n ℂ) * (E * ((b : Matrix n n ℂ) * c) * E) * e by
        simp [mul_assoc], hbc, mul_zero, zero_mul]
    rw [show ((a : Matrix n n ℂ) * E * b) * E * ((c : Matrix n n ℂ) * E * e) =
      (a : Matrix n n ℂ) * (E * b * E) * c * E * e by simp [mul_assoc], hEAE,
      mul_zero, zero_mul]
    simp

/-- Bilinear insertion identity on the basis-invariant three-form residual
subspace.

Source: arXiv:1703.09188, equation `simple2` and the paragraph following
`sprimeforms`, lines 419--426. -/
theorem mul_eq_mul_projector_mul_of_mem_threeFormSubmodule
    (E : Matrix n n ℂ) (A : NonUnitalSubalgebra ℂ (Matrix n n ℂ))
    (hE : E * E = E) (hEAE : ∀ a : A, E * (a : Matrix n n ℂ) * E = 0)
    {x y : Matrix n n ℂ} (hx : x ∈ threeFormSubmodule E A)
    (hy : y ∈ threeFormSubmodule E A) : x * y = x * E * y := by
  classical
  rw [threeFormSubmodule_eq_span_generatorSet] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact threeForm_generator_mul_eq_mul_projector_mul E A hE hEAE hx hy
      | zero => simp
      | add y z _ _ hy hz => simp [Matrix.mul_add, hy, hz]
      | smul c y _ hy => simp [hy]
  | zero => simp
  | add x z _ _ hx hz => simp [Matrix.add_mul, hx, hz]
  | smul c x _ hx => simp [hx]

omit [DecidableEq n] in
private theorem trace_mul_projector_eq_zero_generator
    (E : Matrix n n ℂ) (A : NonUnitalSubalgebra ℂ (Matrix n n ℂ))
    (hE : E * E = E) (hEAE : ∀ a : A, E * (a : Matrix n n ℂ) * E = 0)
    {x : Matrix n n ℂ} (hx : x ∈ threeFormGeneratorSet E A) :
    Matrix.trace (x * E) = 0 := by
  classical
  rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, b, rfl⟩
  · simp [hEAE]
  · have htr : Matrix.trace ((a : Matrix n n ℂ) * E) = 0 := by
      calc
        Matrix.trace ((a : Matrix n n ℂ) * E) =
            Matrix.trace (E * (a : Matrix n n ℂ)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (E * E * (a : Matrix n n ℂ)) := by rw [hE]
        _ = Matrix.trace (E * (a : Matrix n n ℂ) * E) :=
          (Matrix.trace_mul_cycle E (a : Matrix n n ℂ) E).symm
        _ = 0 := by rw [hEAE, Matrix.trace_zero]
    rw [Matrix.mul_assoc, hE, htr]
  · rw [show ((a : Matrix n n ℂ) * E * b) * E =
      (a : Matrix n n ℂ) * (E * b * E) by simp [mul_assoc], hEAE, mul_zero,
      Matrix.trace_zero]

/-- Every three-form residual has zero contraction between the rank-one
projector witnesses.

Source: arXiv:1703.09188, equation `simple1`, lines 423--426. -/
theorem trace_mul_projector_eq_zero_of_mem_threeFormSubmodule
    (E : Matrix n n ℂ) (A : NonUnitalSubalgebra ℂ (Matrix n n ℂ))
    (hE : E * E = E) (hEAE : ∀ a : A, E * (a : Matrix n n ℂ) * E = 0)
    {x : Matrix n n ℂ} (hx : x ∈ threeFormSubmodule E A) :
    Matrix.trace (x * E) = 0 := by
  classical
  rw [threeFormSubmodule_eq_span_generatorSet] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact trace_mul_projector_eq_zero_generator E A hE hEAE hx
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_mul, Matrix.trace_add, hx, hy]
  | smul c x _ hx => simp [Matrix.trace_smul, hx]

/-- A first-block MPU whose normalized double-layer diagonal is a normalized
rank-one projector becomes MPU-simple after the corrected second blocking of
exact length \(D^2\).

Source: arXiv:1703.09188, Proposition III.3(ii), lines 405--427.

**Local fix (nil-matrix length):** the second blocking uses \(D^2\), replacing the
unsupported strict intermediate bound; see <https://sirui-lu.com/QICLean/paper-gaps/mpu_nil_matrix_bound.pdf>. -/
theorem IsMPU.blockTensor_sq_simple_contractions_of_normalizedDiagonal_eq_vecMulVec
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ Φ : Fin (D * D) → ℂ) (hpair : Φ ⬝ᵥ ρ = 1)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ) :
    (∀ i j,
      Φ ⬝ᵥ (doubleLayerTensor (MPOTensor.blockTensor U (D * D)) i j *ᵥ ρ) =
        if i = j then 1 else 0) ∧
    (∀ i j k l,
      doubleLayerTensor (MPOTensor.blockTensor U (D * D)) i j *
          doubleLayerTensor (MPOTensor.blockTensor U (D * D)) k l =
        doubleLayerTensor (MPOTensor.blockTensor U (D * D)) i j *
          Matrix.vecMulVec ρ Φ *
            doubleLayerTensor (MPOTensor.blockTensor U (D * D)) k l) := by
  classical
  let E := normalizedDiagonal (doubleLayerTensor U)
  let A := residualAlgebra U
  have hEouter : E = Matrix.vecMulVec ρ Φ := by simpa [E] using hE
  have hEidem : E * E = E := by
    rw [hEouter, Matrix.vecMulVec_mul_vecMulVec, hpair, one_smul]
  have hEAE : ∀ a : A, E * (a : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * E = 0 :=
    hU.normalizedDiagonal_mul_mem_residualAlgebra_mul_normalizedDiagonal_eq_zero ρ Φ hE
  let V := MPOTensor.blockTensor U (D * D)
  have hEV : normalizedDiagonal (doubleLayerTensor V) = E := by
    dsimp [V, E]
    rw [doubleLayerTensor_blockTensor, normalizedDiagonal_blockTensor,
      IsIdempotentElem.pow_eq hEidem (Nat.mul_pos (NeZero.pos D) (NeZero.pos D)).ne']
  constructor
  · intro i j
    let R := residualSlice (doubleLayerTensor V) (Matrix.single j i 1)
    have hR : R ∈ threeFormSubmodule E A :=
      hU.residualSlice_doubleLayerTensor_blockTensor_single_mem_threeFormSubmodule
        ρ Φ hE hEidem i j
    have hRtrace : Matrix.trace (R * E) = 0 :=
      trace_mul_projector_eq_zero_of_mem_threeFormSubmodule E A hEidem hEAE hR
    have hRpair : Φ ⬝ᵥ (R *ᵥ ρ) = 0 := by
      calc
        Φ ⬝ᵥ (R *ᵥ ρ) = Matrix.trace (Matrix.vecMulVec (R *ᵥ ρ) Φ) := by
          rw [Matrix.trace_vecMulVec, dotProduct_comm]
        _ = Matrix.trace (R * Matrix.vecMulVec ρ Φ) := by rw [Matrix.mul_vecMulVec]
        _ = Matrix.trace (R * E) := by
          rw [hEouter]
        _ = 0 := hRtrace
    rw [entry_eq_diagonal_add_residual (doubleLayerTensor V) i j, hEV]
    change Φ ⬝ᵥ (((if i = j then (1 : ℂ) else 0) • E + R) *ᵥ ρ) = _
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      hRpair, add_zero]
    rw [hEouter, Matrix.vecMulVec_mulVec]
    simp [hpair]
  · intro i j k l
    let Rij := residualSlice (doubleLayerTensor V) (Matrix.single j i 1)
    let Rkl := residualSlice (doubleLayerTensor V) (Matrix.single l k 1)
    have hRij : Rij ∈ threeFormSubmodule E A :=
      hU.residualSlice_doubleLayerTensor_blockTensor_single_mem_threeFormSubmodule
        ρ Φ hE hEidem i j
    have hRkl : Rkl ∈ threeFormSubmodule E A :=
      hU.residualSlice_doubleLayerTensor_blockTensor_single_mem_threeFormSubmodule
        ρ Φ hE hEidem k l
    have hRR : Rij * Rkl = Rij * E * Rkl :=
      mul_eq_mul_projector_mul_of_mem_threeFormSubmodule E A hEidem hEAE hRij hRkl
    rw [entry_eq_diagonal_add_residual (doubleLayerTensor V) i j,
      entry_eq_diagonal_add_residual (doubleLayerTensor V) k l, hEV]
    change _ = _ * Matrix.vecMulVec ρ Φ * _
    rw [← hEouter]
    change ((if i = j then (1 : ℂ) else 0) • E + Rij) *
      ((if k = l then (1 : ℂ) else 0) • E + Rkl) =
      ((if i = j then (1 : ℂ) else 0) • E + Rij) * E *
        ((if k = l then (1 : ℂ) else 0) • E + Rkl)
    simp [Matrix.add_mul, Matrix.mul_add, hEidem, hRR, mul_assoc]

/-- A first-block MPU with supplied normalized rank-one fixed witnesses becomes
MPU-simple after the corrected second blocking of exact length \(D^2\).

Source: arXiv:1703.09188, Proposition III.3(ii), lines 405--427.

**Local fix (nil-matrix length):** the second blocking uses \(D^2\), replacing the
unsupported strict intermediate bound; see <https://sirui-lu.com/QICLean/paper-gaps/mpu_nil_matrix_bound.pdf>. -/
theorem IsMPU.blockTensor_sq_isMPUSimple_of_normalizedDiagonal_eq_vecMulVec
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ Φ : Fin (D * D) → ℂ) (hpair : Φ ⬝ᵥ ρ = 1)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ) :
    IsMPUSimple (MPOTensor.blockTensor U (D * D)) := by
  exact ⟨Φ, ρ,
    hU.blockTensor_sq_simple_contractions_of_normalizedDiagonal_eq_vecMulVec ρ Φ hpair hE⟩

end ThreeFormInsertion

end MPOTensor
