/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.MPU.ThreeFormSpan

/-!
# Bounded blocking to a simple matrix product unitary

This file completes the algebraic contraction step in arXiv:1703.09188,
Proposition `blockingsimple`, lines 415--427.  It turns the basis-invariant
three-form residual classification into the exact `simple1` and `simple2`
identities.
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

set_option linter.unusedDecidableInType false in
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

set_option linter.unusedDecidableInType false in
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

private theorem entry_eq_diagonal_add_residual
    (W : MPOTensor d D) (i j : Fin d) :
    W i j = (if i = j then (1 : ℂ) else 0) • normalizedDiagonal W +
      residualSlice W (Matrix.single j i 1) := by
  rw [residualSlice, contractPhysical_single]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Matrix.trace_single_eq_same]
    simp
  · rw [if_neg hij, Matrix.trace_single_eq_of_ne j i (1 : ℂ) (Ne.symm hij)]
    simp

private theorem pow_eq_self_of_pos_local {m : Type*} [Fintype m] [DecidableEq m]
    {E : Matrix m m ℂ} (hE : E * E = E) {N : ℕ} (hN : 0 < N) : E ^ N = E := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction N with
  | zero => simp
  | succ N ih => rw [pow_succ, ih (by omega), hE]

/-- A first-block MPU whose normalized double-layer diagonal is a normalized
rank-one projector becomes MPU-simple after the corrected second blocking of
exact length `D²`.

Source: arXiv:1703.09188, Proposition III.3(ii), lines 405--427.

**Local fix:** the second blocking uses `D²`, replacing the unsupported strict
intermediate bound; see `docs/paper-gaps/mpu_nil_matrix_bound.tex`. -/
theorem IsMPU.blockTensor_sq_isMPUSimple_of_normalizedDiagonal_eq_vecMulVec
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ Φ : Fin (D * D) → ℂ) (hpair : Φ ⬝ᵥ ρ = 1)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ) :
    IsMPUSimple (MPOTensor.blockTensor U (D * D)) := by
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
      pow_eq_self_of_pos_local hEidem (Nat.mul_pos (NeZero.pos D) (NeZero.pos D))]
  refine ⟨Φ, ρ, ?_, ?_⟩
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

end ThreeFormInsertion

section BlockingAssembly

private theorem sandwich_mul_rankOne_mul_local {n : Type*} [Fintype n]
    (a b : n → ℂ) (A X : Matrix n n ℂ) :
    a ⬝ᵥ ((A * Matrix.vecMulVec b a * X) *ᵥ b) =
      (a ⬝ᵥ (A *ᵥ b)) * (a ⬝ᵥ (X *ᵥ b)) := by
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec]
  simp [dotProduct, Finset.mul_sum, Finset.sum_mul]

private theorem sandwich_listProd_local {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (P : Matrix n n ℂ → Prop)
    (hpair : ∀ A B, P A → P B →
      A * B = A * Matrix.vecMulVec b a * B) :
    ∀ l : List (Matrix n n ℂ), l ≠ [] → (∀ A ∈ l, P A) →
      a ⬝ᵥ (l.prod *ᵥ b) =
        (l.map fun A ↦ a ⬝ᵥ (A *ᵥ b)).prod := by
  intro l hl hP
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
      cases l with
      | nil => simp
      | cons B l =>
          have hA : P A := hP A (by simp)
          have hB : P B := hP B (by simp)
          have htail : ∀ X ∈ B :: l, P X := by
            intro X hX
            exact hP X (by simp [hX])
          rw [List.prod_cons, List.prod_cons, ← Matrix.mul_assoc,
            hpair A B hA hB, Matrix.mul_assoc, sandwich_mul_rankOne_mul_local]
          change (a ⬝ᵥ (A *ᵥ b)) * (a ⬝ᵥ ((B :: l).prod *ᵥ b)) = _
          rw [ih (by simp) htail]
          simp

private theorem listProd_mul_eq_listProd_mul_rankOne_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (P : Matrix n n ℂ → Prop)
    (hpair : ∀ A B, P A → P B →
      A * B = A * Matrix.vecMulVec b a * B) :
    ∀ l r : List (Matrix n n ℂ), l ≠ [] → r ≠ [] →
      (∀ A ∈ l, P A) → (∀ B ∈ r, P B) →
      l.prod * r.prod = l.prod * Matrix.vecMulVec b a * r.prod := by
  intro l r hl hr hlP hrP
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
      cases l with
      | nil =>
          obtain ⟨B, r, rfl⟩ := List.exists_cons_of_ne_nil hr
          simp only [List.prod_cons, List.prod_nil, mul_one]
          rw [← Matrix.mul_assoc, hpair A B (hlP A (by simp))
            (hrP B (by simp)), Matrix.mul_assoc]
      | cons B l =>
          have htail : ∀ X ∈ B :: l, P X := by
            intro X hX
            exact hlP X (by simp [hX])
          have hih := ih (by simp) htail
          simpa only [List.prod_cons, Matrix.mul_assoc] using
            congrArg (fun X ↦ A * X) hih

/-- MPU simplicity is preserved by every positive further physical blocking.

Source: arXiv:1703.09188, Corollary `simple1`, lines 429--432. -/
theorem IsMPUSimple.blockTensor {U : MPOTensor d D} (hU : IsMPUSimple U)
    (L : ℕ) (hL : 0 < L) : IsMPUSimple (MPOTensor.blockTensor U L) := by
  classical
  obtain ⟨a, b, h₁, h₂⟩ := hU
  let P : Matrix (Fin (D * D)) (Fin (D * D)) ℂ → Prop :=
    fun A ↦ ∃ i j, A = doubleLayerTensor U i j
  have hpair : ∀ A B, P A → P B →
      A * B = A * Matrix.vecMulVec b a * B := by
    rintro A B ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact h₂ i j k l
  refine ⟨a, b, ?_, ?_⟩
  · intro I J
    rw [doubleLayerTensor_blockTensor, blockTensor_apply]
    simp only [MPSTensor.wordOfBlock]
    rw [evalWord_ofFn]
    let l := List.ofFn (fun k : Fin L ↦
      doubleLayerTensor U (MPSTensor.decodeBlock d L I k)
        (MPSTensor.decodeBlock d L J k))
    have hl : l ≠ [] := by simp [l, Nat.ne_of_gt hL]
    have hlP : ∀ A ∈ l, P A := by
      intro A hA
      simp only [l, List.mem_ofFn] at hA
      obtain ⟨k, rfl⟩ := hA
      exact ⟨_, _, rfl⟩
    rw [sandwich_listProd_local a b P hpair l hl hlP]
    simp only [l, List.map_ofFn, List.prod_ofFn, Function.comp_apply, h₁]
    by_cases hIJ : I = J
    · subst J
      simp
    · rw [if_neg hIJ]
      have hpoint : ∃ k : Fin L,
          MPSTensor.decodeBlock d L I k ≠ MPSTensor.decodeBlock d L J k := by
        by_contra h
        apply hIJ
        exact (MPSTensor.decodeBlockEquiv d L).injective
          (funext fun k ↦ not_ne_iff.mp (not_exists.mp h k))
      obtain ⟨k, hk⟩ := hpoint
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [hk]
  · intro I J K M
    rw [doubleLayerTensor_blockTensor, blockTensor_apply, blockTensor_apply]
    simp only [MPSTensor.wordOfBlock]
    rw [evalWord_ofFn, evalWord_ofFn]
    apply listProd_mul_eq_listProd_mul_rankOne_mul a b P hpair
    · simp [Nat.ne_of_gt hL]
    · simp [Nat.ne_of_gt hL]
    · intro A hA
      simp only [List.mem_ofFn] at hA
      obtain ⟨k, rfl⟩ := hA
      exact ⟨_, _, rfl⟩
    · intro A hA
      simp only [List.mem_ofFn] at hA
      obtain ⟨k, rfl⟩ := hA
      exact ⟨_, _, rfl⟩

private theorem IsMPU.simple1_of_normalizedTransferStabilization
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    {bound : ℕ}
    (data : Matrix.StabilizedRankOneData
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) bound) :
    ∃ a b : Fin (D * D) → ℂ, ∀ i j : Fin d,
      a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0 := by
  classical
  let J := data.exponent
  let E := normalizedDiagonal (doubleLayerTensor U)
  let ρ : Fin (D * D) → ℂ := fun i ↦ data.right (finProdFinEquiv.symm i)
  let Φ : Fin (D * D) → ℂ := fun i ↦ data.left (finProdFinEquiv.symm i)
  let P := Matrix.vecMulVec ρ Φ
  have hEPow : E ^ J = P := by
    calc
      E ^ J = normalizedDiagonal
          (doubleLayerTensor (MPOTensor.blockTensor U J)) := by
        simp only [E, doubleLayerTensor_blockTensor, normalizedDiagonal_blockTensor]
      _ = P := by
        rw [normalizedDiagonal_doubleLayerTensor_blockTensor, data.power_eq]
        rfl
  have hpair : Φ ⬝ᵥ ρ = 1 := by
    change (∑ i : Fin (D * D),
      data.left (finProdFinEquiv.symm i) * data.right (finProdFinEquiv.symm i)) = 1
    calc
      _ = ∑ ij : Fin D × Fin D, data.left ij * data.right ij := by
        symm
        simpa using Equiv.sum_comp
          (finProdFinEquiv : Fin D × Fin D ≃ Fin (D * D))
          (fun i ↦ data.left (finProdFinEquiv.symm i) *
            data.right (finProdFinEquiv.symm i))
      _ = 1 := by simpa [dotProduct, mul_comm] using data.pairing_eq_one
  have hErho : E *ᵥ ρ = ρ := by
    rw [show E = (transferMatrix
      (MPSTensor.transferMap U.normalizedFlattening)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm by
      exact normalizedDiagonal_doubleLayerTensor U]
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    have hρ : ρ ∘ finProdFinEquiv = data.right := by
      funext i
      change data.right (finProdFinEquiv.symm (finProdFinEquiv i)) = data.right i
      rw [Equiv.symm_apply_apply]
    rw [hρ, data.right_fixed]
    rfl
  have hEP : E * P = P := by
    rw [show P = Matrix.vecMulVec ρ Φ by rfl, Matrix.mul_vecMulVec, hErho]
  have htraceP : Matrix.trace P = 1 := by
    rw [show P = Matrix.vecMulVec ρ Φ by rfl, Matrix.trace_vecMulVec,
      dotProduct_comm, hpair]
  refine ⟨Φ, ρ, ?_⟩
  intro i j
  let R := residualSlice (doubleLayerTensor U) (Matrix.single j i 1)
  have hRtrace : Matrix.trace (R * P) = 0 := by
    let isResidual : Fin (J + 1) → Bool := Fin.cases true (fun _ ↦ false)
    let X : Fin (J + 1) → Matrix (Fin d) (Fin d) ℂ :=
      Fin.cases (Matrix.single j i 1) (fun _ ↦ 0)
    have hmixed : ∃ k, isResidual k = true := ⟨0, rfl⟩
    have htrace := hU.trace_prod_mixedResidualFactor_doubleLayerTensor_eq_zero_of_pos
      (Nat.succ_pos J) isResidual X hmixed
    rw [← hEPow]
    simpa [R, E, isResidual, X, mixedResidualFactor, List.ofFn_succ,
      List.ofFn_const, List.prod_replicate] using htrace
  have hscalar (M : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) :
      Φ ⬝ᵥ (M *ᵥ ρ) = Matrix.trace (M * P) := by
    rw [show P = Matrix.vecMulVec ρ Φ by rfl, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec, dotProduct_comm]
  rw [entry_eq_diagonal_add_residual (doubleLayerTensor U) i j]
  change Φ ⬝ᵥ (((if i = j then (1 : ℂ) else 0) • E + R) *ᵥ ρ) = _
  rw [hscalar, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, hEP, htraceP, hRtrace]
  simp

/-- The source `simple1` contraction holds for every MPU, without requiring
the unblocked tensor itself to satisfy `simple2`.

Source: arXiv:1703.09188, Corollary `simple1`, lines 429--438. -/
theorem IsMPU.simple1 [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : IsMPU U) :
    ∃ a b : Fin (D * D) → ℂ, ∀ i j : Fin d,
      a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0 := by
  by_cases hD : D = 1
  · subst D
    exact hU.simple1_of_normalizedTransferStabilization
      hU.normalizedTransferStabilization_fin_one
  · have hDpos : 0 < D := NeZero.pos D
    have hDgt : 1 < D := by omega
    exact hU.simple1_of_normalizedTransferStabilization
      (hU.normalizedTransferStabilization hDgt)

/-- Reindex both physical legs of an MPO tensor by the same equivalence. -/
noncomputable def reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d)
    (U : MPOTensor d D) : MPOTensor d' D :=
  fun i j ↦ U (e i) (e j)

private theorem doubleLayerTensor_reindexPhysical {d' : ℕ}
    (e : Fin d' ≃ Fin d) (U : MPOTensor d D) (i j : Fin d') :
    doubleLayerTensor (reindexPhysical e U) i j = doubleLayerTensor U (e i) (e j) := by
  classical
  simp only [doubleLayerTensor_apply, reindexPhysical]
  rw [← e.sum_comp]
  rfl

/-- MPU simplicity is invariant under a bijective relabeling of the physical
basis.

Source: arXiv:1703.09188, Proposition III.3, where physical blocking indices
are identified canonically. -/
theorem IsMPUSimple.reindexPhysical {d' : ℕ} {U : MPOTensor d D}
    (hU : IsMPUSimple U) (e : Fin d' ≃ Fin d) :
    IsMPUSimple (reindexPhysical e U) := by
  obtain ⟨a, b, h₁, h₂⟩ := hU
  refine ⟨a, b, ?_, ?_⟩
  · intro i j
    rw [doubleLayerTensor_reindexPhysical]
    simpa [e.injective.eq_iff] using h₁ (e i) (e j)
  · intro i j k l
    simp only [doubleLayerTensor_reindexPhysical]
    exact h₂ (e i) (e j) (e k) (e l)

private theorem evalWord_blockTensor_ofFn_local
    (U : MPOTensor d D) (L : ℕ) {N : ℕ}
    (s t : Fin N → Fin (MPSTensor.blockPhysDim d L)) :
    evalWord (MPOTensor.blockTensor U L) (List.ofFn s) (List.ofFn t) =
      evalWord U (MPSTensor.flattenBlockedWord d L (List.ofFn s))
        (MPSTensor.flattenBlockedWord d L (List.ofFn t)) := by
  induction N with
  | zero => simp [MPSTensor.flattenBlockedWord]
  | succ N ih =>
      simp only [List.ofFn_succ, evalWord_cons, blockTensor_apply,
        MPSTensor.flattenBlockedWord_cons]
      rw [ih]
      rw [evalWord_append U _ _ _ _ (by simp)]

/-- Iterated MPO blocking, reindexed by the canonical grouping equivalence,
agrees with direct blocking at the product length.

Source: arXiv:1703.09188, Proposition III.3, lines 405--426. -/
theorem reindexPhysical_blockTensor_blockTensor
    (U : MPOTensor d D) (m n : ℕ) :
    reindexPhysical (MPSTensor.directIteratedBlockEquiv d m n)
        (MPOTensor.blockTensor (MPOTensor.blockTensor U m) n) =
      MPOTensor.blockTensor U (m * n) := by
  funext i j
  simp only [reindexPhysical, blockTensor_apply, MPSTensor.wordOfBlock]
  rw [evalWord_blockTensor_ofFn_local]
  change evalWord U
      (MPSTensor.flattenBlockedWord d m
        (MPSTensor.wordOfBlock (MPSTensor.blockPhysDim d m) n
          (MPSTensor.directToIteratedBlockIndex d m n i)))
      (MPSTensor.flattenBlockedWord d m
        (MPSTensor.wordOfBlock (MPSTensor.blockPhysDim d m) n
          (MPSTensor.directToIteratedBlockIndex d m n j))) =
    evalWord U (MPSTensor.wordOfBlock d (m * n) i)
      (MPSTensor.wordOfBlock d (m * n) j)
  rw [MPSTensor.flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex,
    MPSTensor.flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex]

/-- For bond dimension greater than one, an MPU has a strictly sub-`D⁴`
positive direct blocking that is MPU-simple.

Source: arXiv:1703.09188, Proposition III.3(ii), lines 397--427.

**Local fix:** the first exponent satisfies `J ≤ D² - 1` and the second length
is exactly `D²`, still giving `J D² < D⁴`; see
`docs/paper-gaps/mpu_nil_matrix_bound.tex`. -/
theorem IsMPU.exists_blockTensor_isMPUSimple_of_one_lt
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    ∃ k : ℕ, 0 < k ∧ k < D ^ 4 ∧ IsMPUSimple (MPOTensor.blockTensor U k) := by
  classical
  let data := hU.normalizedTransferStabilization hD
  let J := data.exponent
  let V := MPOTensor.blockTensor U J
  let ρ : Fin (D * D) → ℂ := fun i ↦ data.right (finProdFinEquiv.symm i)
  let Φ : Fin (D * D) → ℂ := fun i ↦ data.left (finProdFinEquiv.symm i)
  have hpair : Φ ⬝ᵥ ρ = 1 := by
    change (∑ i : Fin (D * D),
      data.left (finProdFinEquiv.symm i) * data.right (finProdFinEquiv.symm i)) = 1
    calc
      _ = ∑ ij : Fin D × Fin D, data.left ij * data.right ij := by
        symm
        simpa using Equiv.sum_comp
          (finProdFinEquiv : Fin D × Fin D ≃ Fin (D * D))
          (fun i ↦ data.left (finProdFinEquiv.symm i) *
            data.right (finProdFinEquiv.symm i))
      _ = 1 := by simpa [dotProduct, mul_comm] using data.pairing_eq_one
  have hVmpu : IsMPU V := hU.blockTensor J data.exponent_pos
  have hVE : normalizedDiagonal (doubleLayerTensor V) = Matrix.vecMulVec ρ Φ := by
    change normalizedDiagonal (doubleLayerTensor (MPOTensor.blockTensor U J)) = _
    rw [hU.normalizedDiagonal_doubleLayerTensor_blockTensor_eq_vecMulVec hD]
    rfl
  letI : NeZero (MPSTensor.blockPhysDim d J) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero J (NeZero.ne d)⟩
  have hsimpleIterated : IsMPUSimple (MPOTensor.blockTensor V (D * D)) :=
    hVmpu.blockTensor_sq_isMPUSimple_of_normalizedDiagonal_eq_vecMulVec ρ Φ hpair hVE
  have hsimple : IsMPUSimple (MPOTensor.blockTensor U (J * (D * D))) := by
    rw [← reindexPhysical_blockTensor_blockTensor U J (D * D)]
    exact hsimpleIterated.reindexPhysical (MPSTensor.directIteratedBlockEquiv d J (D * D))
  have hJpos : 0 < J := data.exponent_pos
  have hDDpos : 0 < D * D := Nat.mul_pos (NeZero.pos D) (NeZero.pos D)
  have hJlt : J < D * D := lt_of_le_of_lt data.exponent_le (Nat.sub_lt hDDpos Nat.zero_lt_one)
  refine ⟨J * (D * D), Nat.mul_pos hJpos hDDpos, ?_, hsimple⟩
  calc
    J * (D * D) < (D * D) * (D * D) := Nat.mul_lt_mul_of_pos_right hJlt hDDpos
    _ = D ^ 4 := by ring

/-- In bond dimension one, one-site blocking is already MPU-simple.

Source: arXiv:1703.09188, Proposition III.3(ii), specialized to `D=1`. -/
theorem IsMPU.blockTensor_one_isMPUSimple_fin_one
    [NeZero d] {U : MPOTensor d 1} (hU : IsMPU U) :
    IsMPUSimple (MPOTensor.blockTensor U 1) := by
  let ρ : Fin (1 * 1) → ℂ := fun _ ↦ 1
  let Φ : Fin (1 * 1) → ℂ := fun _ ↦ 1
  have hpair : Φ ⬝ᵥ ρ = 1 := by
    simp [dotProduct, Φ, ρ]
  have hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ := by
    rw [normalizedDiagonal_doubleLayerTensor, hU.normalized_transfer_matrix_eq_one_fin_one]
    ext i j
    fin_cases i
    fin_cases j
    simp [ρ, Φ, Matrix.vecMulVec_apply]
  simpa using hU.blockTensor_sq_isMPUSimple_of_normalizedDiagonal_eq_vecMulVec ρ Φ hpair hE

/-- Every positive-bond-dimension MPU has a positive MPU-simple blocking of
length at most `D⁴`.

Source: arXiv:1703.09188, Proposition III.3(ii), lines 378--427. -/
theorem IsMPU.exists_blockTensor_isMPUSimple
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ D ^ 4 ∧ IsMPUSimple (MPOTensor.blockTensor U k) := by
  by_cases hD : D = 1
  · subst D
    exact ⟨1, by simp, by simp, hU.blockTensor_one_isMPUSimple_fin_one⟩
  · have hDpos : 0 < D := NeZero.pos D
    have hDgt : 1 < D := by omega
    obtain ⟨k, hk, hklt, hsimple⟩ := hU.exists_blockTensor_isMPUSimple_of_one_lt hDgt
    exact ⟨k, hk, hklt.le, hsimple⟩

end BlockingAssembly

end MPOTensor
