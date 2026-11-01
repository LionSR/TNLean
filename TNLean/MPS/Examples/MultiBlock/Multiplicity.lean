/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Running
import TNLean.MPS.FundamentalTheorem.Reduction.RingEmbedding

/-!
# Two copies of one block

The block `C = (σ_x, E₁₁)` on `ℂ²` (*The asymmetric fundamental theorem of matrix product states*,
Example 6.13) is normal: its words of length `3` span `M₂(ℂ)`. The tensor `B = 1₂ ⊗ C` on
`ℂ⁴ = ℂ² ⊗ ℂ²` contains two copies of `C`, and for every nonzero `u ∈ ℂ²` the subspace `ℂ u ⊗ ℂ²` is
invariant, different lines giving different subspaces: `B` has infinitely many invariant subspaces
carrying `C`.

The bond index of `ℂ⁴` is `2a + b`, with `a` the index of the first factor (the copy) and `b` the
index of the second factor (the block).

## Main results

* `MultiBlockExamples.Multiplicity.wordSpan_tensorC_three_eq_top_and_isNormal`: the words of length
  `3` span `M₂(ℂ)`, so `C` is normal.
* `MultiBlockExamples.Multiplicity.tensorB_eq_kronecker`: `B = 1₂ ⊗ C`.
* `MultiBlockExamples.Multiplicity.isInvariantSubmodule_lineTensor`, `span_eq_of_lineTensor_eq`: the
  invariant subspaces `ℂ u ⊗ ℂ²`.
* `MultiBlockExamples.Multiplicity.commute_tensorB_iff_eq_kronMat`,
  `exists_split_multiBlockCompression_kronRow`, `exists_left_eq_kronRow_of_remainder_eq_zero`: the
  split reductions of `B` onto two copies of `C` are exactly `A ⊗ 1₂`.
* `MultiBlockExamples.Multiplicity.exists_left_mul_evalWord_eq_smul_iff`: proportional reading maps.
* `MultiBlockExamples.Multiplicity.matching_left_splitRed_of_span_ne`: *Two compressions with
  different flags* for any two split reductions `A ⊗ 1₂`, `Ã ⊗ 1₂` with `ℂ u₁ ≠ ℂ u_tilde₁`.
* `MultiBlockExamples.Multiplicity.matching_left_redOne_redAt`: the instance `A = 1`,
  `Ã = [[1, 0], [1, 1]]`.

## References

*The asymmetric fundamental theorem of matrix product states*, Example 6.13.
-/

open scoped Matrix Kronecker

namespace MultiBlockExamples

namespace Multiplicity

open MPSTensor

/-- `σ_x`. -/
noncomputable abbrev σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- **The block `C = (σ_x, E₁₁)`** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.13). -/
noncomputable def tensorC : MPSTensor 2 2 := ![σx, E 0 0]

/-- The integer letters of `C`. -/
def tensorCInt : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ := ![!![0, 1; 1, 0], !![1, 0; 0, 0]]

theorem tensorC_eq_complexOfRing (a : Fin 2) :
    tensorC a = complexOfRing (Int.castRingHom ℂ) (tensorCInt a) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [tensorC, tensorCInt, complexOfRing_apply]

/-- The words of length three writing the matrix units: `E₁₁ = PPP`, `E₁₂ = PPX`, `E₂₁ = XPP`,
`E₂₂ = XPX`, with `X = σ_x`, `P = E₁₁`. -/
def unitWord : Fin 2 → Fin 2 → Unit → Fin 3 → Fin 2
  | 0, 0, _ => ![1, 1, 1]
  | 0, 1, _ => ![1, 1, 0]
  | 1, 0, _ => ![0, 1, 1]
  | 1, 1, _ => ![0, 1, 0]

/-- **The block is normal** (*The asymmetric fundamental theorem of matrix product states*, Example
6.13): the words of length `3` of `C` span `M₂(ℂ)`, so `C` is normal. -/
theorem wordSpan_tensorC_three_eq_top_and_isNormal :
    Kraus.wordSpan tensorC 3 = ⊤ ∧ Kraus.IsNormal tensorC := by
  have h : Kraus.IsNBlkInjective tensorC 3 :=
    isNBlkInjective_of_complexOfRing_smul_single (Int.castRingHom ℂ) tensorCInt
      tensorC_eq_complexOfRing unitWord (fun _ _ _ => 1) (c := 1) (by simp) (by decide)
  exact ⟨h, ⟨3, by norm_num, h⟩⟩

theorem isNormal_tensorC : Kraus.IsNormal tensorC := wordSpan_tensorC_three_eq_top_and_isNormal.2

/-- **The tensor `B = 1₂ ⊗ C`** on `ℂ⁴`, bond index `2a + b` (*The asymmetric fundamental theorem of
matrix product states*, Example 6.13). -/
noncomputable def tensorB : MPSTensor 2 4 :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]]

/-- `B = 1₂ ⊗ C`, read on `ℂ⁴` through the bond index `2a + b` (*The asymmetric fundamental theorem
of matrix product states*, Example 6.13). -/
theorem tensorB_eq_kronecker (i : Fin 2) :
    tensorB i = Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ tensorC i) := by
  ext x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    simp [tensorB, tensorC, Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- The vector `u ⊗ v` of `ℂ⁴`. -/
def kron (u v : Fin 2 → ℂ) : Fin 4 → ℂ := ![u 0 * v 0, u 0 * v 1, u 1 * v 0, u 1 * v 1]

/-- `v ↦ u ⊗ v` as a linear map. -/
def kronLeft (u : Fin 2 → ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := kron u v
  map_add' v w := by ext k; fin_cases k <;> simp [kron] <;> ring
  map_smul' c v := by ext k; fin_cases k <;> simp [kron] <;> ring

/-- The subspace `ℂ u ⊗ ℂ²`. -/
def lineTensor (u : Fin 2 → ℂ) : Submodule ℂ (Fin 4 → ℂ) := LinearMap.range (kronLeft u)

theorem tensorB_mulVec_kron (i : Fin 2) (u v : Fin 2 → ℂ) :
    tensorB i *ᵥ kron u v = kron u (tensorC i *ᵥ v) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [tensorB, tensorC, kron, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]

/-- **The invariant subspaces `ℂ u ⊗ ℂ²`** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.13): for every `u ∈ ℂ²` the subspace `ℂ u ⊗ ℂ²` is invariant under both letters
of `B`. -/
theorem isInvariantSubmodule_lineTensor (u : Fin 2 → ℂ) :
    Matrix.IsInvariantSubmodule tensorB (lineTensor u) := by
  rintro i _ ⟨v, rfl⟩
  exact ⟨tensorC i *ᵥ v, (tensorB_mulVec_kron i u v).symm⟩

/-- **Different lines give different subspaces** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.13): different lines give different subspaces: `ℂ u ⊗ ℂ² = ℂ u' ⊗ ℂ²` for
nonzero `u` only if `ℂ u = ℂ u'`. -/
theorem span_eq_of_lineTensor_eq {u u' : Fin 2 → ℂ} (hu : u ≠ 0)
    (h : lineTensor u = lineTensor u') : Submodule.span ℂ {u} = Submodule.span ℂ {u'} := by
  have hmem : kron u (e 0) ∈ lineTensor u' := h ▸ ⟨e 0, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  have h0 : u 0 = u' 0 * v 0 := by
    have := congrFun hv 0; simp [kronLeft, kron] at this; exact this.symm
  have h2 : u 1 = u' 1 * v 0 := by
    have := congrFun hv 2; simp [kronLeft, kron] at this; exact this.symm
  have hv0 : v 0 ≠ 0 := fun hv0 => hu (by ext i; fin_cases i <;> simp [h0, h2, hv0])
  refine span_singleton_eq_of_eq_smul hv0 ?_
  ext i; fin_cases i <;> simp [h0, h2, mul_comm]

/-! ### Split reductions onto two copies -/

/-- `A ⊗ 1₂` on `ℂ⁴`. -/
def kronMat (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![A 0 0, 0, A 0 1, 0; 0, A 0 0, 0, A 0 1; A 1 0, 0, A 1 1, 0; 0, A 1 0, 0, A 1 1]

/-- `a ⊗ 1₂` for a row `a`, a `2 × 4` matrix. -/
def kronRow (a : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 4) ℂ := !![a 0, 0, a 1, 0; 0, a 0, 0, a 1]

/-- `u ⊗ 1₂` for a column `u`, a `4 × 2` matrix. -/
def kronCol (u : Fin 2 → ℂ) : Matrix (Fin 4) (Fin 2) ℂ := !![u 0, 0; 0, u 0; u 1, 0; 0, u 1]

/-- `a ⊗ M` for a row `a` and a `2 × 2` matrix `M`. -/
def kronRowMat (a : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![a 0 * M 0 0, a 0 * M 0 1, a 1 * M 0 0, a 1 * M 0 1;
    a 0 * M 1 0, a 0 * M 1 1, a 1 * M 1 0, a 1 * M 1 1]

/-- `1₂ ⊗ M`. -/
def oneKron (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 0 0, M 0 1; 0, 0, M 1 0, M 1 1]

/-- `kronMat A` is the Kronecker product `A ⊗ 1₂`, read through the bond index `2a + b`. -/
theorem kronMat_eq_kronecker (A : Matrix (Fin 2) (Fin 2) ℂ) :
    kronMat A = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [kronMat, Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem tensorB_eq_oneKron (i : Fin 2) : tensorB i = oneKron (tensorC i) := by
  ext x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;> simp [tensorB, tensorC, oneKron]

theorem oneKron_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    oneKron (M * N) = oneKron M * oneKron N := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [oneKron, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem evalWord_tensorB (w : List (Fin 2)) :
    Kraus.evalWord tensorB w = oneKron (Kraus.evalWord tensorC w) := by
  induction w with
  | nil =>
    ext x y
    fin_cases x <;> fin_cases y <;> simp [oneKron]
  | cons i w ih =>
    rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ih, tensorB_eq_oneKron, oneKron_mul]

theorem kronRow_mul_oneKron (a : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    kronRow a * oneKron M = kronRowMat a M := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [kronRow, oneKron, kronRowMat, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The commutant** (*The asymmetric fundamental theorem of matrix product states*, Example 6.13):
a `4 × 4` matrix commutes with both letters of `B = 1₂ ⊗ C` iff it is `A ⊗ 1₂`. -/
theorem commute_tensorB_iff_eq_kronMat (X : Matrix (Fin 4) (Fin 4) ℂ) :
    (∀ i, X * tensorB i = tensorB i * X) ↔ ∃ A : Matrix (Fin 2) (Fin 2) ℂ, X = kronMat A := by
  constructor
  · intro h
    have e0 : ∀ a b, (X * tensorB 0) a b = (tensorB 0 * X) a b := fun a b => by rw [h 0]
    have e1 : ∀ a b, (X * tensorB 1) a b = (tensorB 1 * X) a b := fun a b => by rw [h 1]
    have z : ∀ a b : Fin 4, a.val % 2 ≠ b.val % 2 → X a b = 0 := by
      intro a b hab
      have := e1 a b
      fin_cases a <;> fin_cases b <;>
        simp only [tensorB, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val',
          Matrix.cons_val, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, mul_zero,
          zero_mul, mul_one, one_mul, add_zero, zero_add, Nat.zero_mod, Nat.mod_succ, Nat.mod_self,
          Nat.reduceMod, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, not_true_eq_false]
          at this hab ⊢ <;>
        first | exact this | exact this.symm
    have s11 := e0 0 1
    have s13 := e0 0 3
    have s31 := e0 2 1
    have s33 := e0 2 3
    simp only [tensorB, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.cons_val, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, mul_one, mul_zero, zero_mul, one_mul, add_zero,
      zero_add] at s11 s13 s31 s33
    refine ⟨!![X 0 0, X 0 2; X 2 0, X 2 2], ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [kronMat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Matrix.cons_val] <;>
      first
        | exact z _ _ (by decide)
        | exact s11.symm | exact s13.symm | exact s31.symm | exact s33.symm
  · rintro ⟨A, rfl⟩ i
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [kronMat, tensorB, Matrix.mul_apply, Fin.sum_univ_four]

/-- A `2 × 4` matrix with `W Bⁱ = Cⁱ W` is `a ⊗ 1₂`. -/
theorem eq_kronRow_of_intertwines (W : Matrix (Fin 2) (Fin 4) ℂ)
    (h : ∀ i, W * tensorB i = tensorC i * W) : W = kronRow ![W 0 0, W 0 2] := by
  have e0 : ∀ a b, (W * tensorB 0) a b = (tensorC 0 * W) a b := fun a b => by rw [h 0]
  have e1 : ∀ a b, (W * tensorB 1) a b = (tensorC 1 * W) a b := fun a b => by rw [h 1]
  have h01 := e1 0 1
  have h03 := e1 0 3
  have h10 := e1 1 0
  have h12 := e1 1 2
  have h11 := e0 0 1
  have h13 := e0 0 3
  simp only [tensorB, tensorC, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val', Matrix.cons_val, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.single_apply_same, Matrix.single_apply_of_ne,
    Finset.sum_const_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, zero_ne_one,
    and_false, false_and, not_false_eq_true] at h01 h03 h10 h12 h11 h13
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [kronRow, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    first
      | exact h01.symm | exact h03.symm | exact h10 | exact h12 | exact h11.symm
      | exact h13.symm

/-- A `4 × 2` matrix with `Bⁱ V = V Cⁱ` is `u ⊗ 1₂`. -/
theorem eq_kronCol_of_intertwines (V : Matrix (Fin 4) (Fin 2) ℂ)
    (h : ∀ i, tensorB i * V = V * tensorC i) : V = kronCol ![V 0 0, V 2 0] := by
  have e0 : ∀ a b, (tensorB 0 * V) a b = (V * tensorC 0) a b := fun a b => by rw [h 0]
  have e1 : ∀ a b, (tensorB 1 * V) a b = (V * tensorC 1) a b := fun a b => by rw [h 1]
  have h01 := e1 0 1
  have h21 := e1 2 1
  have h10 := e1 1 0
  have h30 := e1 3 0
  have h11 := e0 1 0
  have h31 := e0 3 0
  simp only [tensorB, tensorC, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val', Matrix.cons_val, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.single_apply_same, Matrix.single_apply_of_ne,
    Finset.sum_const_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, zero_ne_one,
    and_false, and_true, not_false_eq_true] at h01 h21 h10 h30 h11 h31
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [kronCol, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    first
      | exact h01.symm | exact h21.symm | exact h10 | exact h30 | exact h11.symm
      | exact h31.symm | exact h01 | exact h21 | exact h10.symm | exact h30.symm

/-- The two copies of `C` as a family. -/
abbrev labels : Finset (Fin 2) := Finset.univ

/-- Both copies have bond dimension `2`. -/
abbrev dims : Fin 2 → ℕ := fun _ => 2

/-- The family `(C, C)`. -/
noncomputable def blocks : ∀ s : Fin 2, MPSTensor 2 (dims s) := fun _ => tensorC

/-- The integer letters of `B`. -/
def tensorBInt : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]]

theorem tensorB_eq_complexOfRing (i : Fin 2) :
    tensorB i = complexOfRing (Int.castRingHom ℂ) (tensorBInt i) := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [tensorB, tensorBInt, complexOfRing_apply]

/-- The order of the two copies: copy `j` at position `j`. -/
def ordM : BlockIndex labels 0 ≃ Fin 2 where
  toFun
    | Sum.inl s => s.1
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨n, Finset.mem_univ n⟩
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates: copy `j`, block index `b` at `2j + b`. -/
def tauM : BlockSpace dims labels 0 ≃ Fin 4 where
  toFun
    | ⟨Sum.inl s, p⟩ => ⟨(2 * s.1.val + p.val) % 4, Nat.mod_lt _ (by norm_num)⟩
    | ⟨Sum.inr t, _⟩ => t.elim0
  invFun
    | 0 => ⟨Sum.inl ⟨0, Finset.mem_univ _⟩, ⟨0, by decide⟩⟩
    | 1 => ⟨Sum.inl ⟨0, Finset.mem_univ _⟩, ⟨1, by decide⟩⟩
    | 2 => ⟨Sum.inl ⟨1, Finset.mem_univ _⟩, ⟨0, by decide⟩⟩
    | 3 => ⟨Sum.inl ⟨1, Finset.mem_univ _⟩, ⟨1, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

theorem kronMat_mul (A A' : Matrix (Fin 2) (Fin 2) ℂ) :
    kronMat (A * A') = kronMat A * kronMat A' := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [kronMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem kronMat_one : kronMat 1 = 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [kronMat]

theorem tensorBInt_offDiag (i : Fin 2) (x y : BlockSpace dims labels 0) (h : x.1 ≠ y.1) :
    tensorBInt i (tauM x) (tauM y) = 0 := by
  revert i x y; decide

theorem kronMat_inv {A Ainv : Matrix (Fin 2) (Fin 2) ℂ} (h1 : A * Ainv = 1) :
    kronMat A * kronMat Ainv = 1 := by
  rw [← kronMat_mul, h1, kronMat_one]

theorem kronMat_conj {A Ainv : Matrix (Fin 2) (Fin 2) ℂ} (h1 : A * Ainv = 1) (i : Fin 2) :
    kronMat A * tensorB i * kronMat Ainv = tensorB i := by
  have hc := (commute_tensorB_iff_eq_kronMat (kronMat A)).2 ⟨A, rfl⟩
  rw [hc i, Matrix.mul_assoc, ← kronMat_mul, h1, kronMat_one, Matrix.mul_one]

/-- **The split reduction `g = A ⊗ 1₂`** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.13), for an invertible `A`: `g B g⁻¹ = B = C ⊕ C`. -/
noncomputable def splitRed (A Ainv : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * Ainv = 1)
    (h2 : Ainv * A = 1) : MultiBlockCompression tensorB labels blocks where
  z := 0
  ord := ordM
  gauge := gaugeOfMatrix tauM (kronMat A) (kronMat Ainv)
    (kronMat_inv h1) (kronMat_inv h2)
  triangular i := by
    rw [conjMatrix_gaugeOfMatrix, kronMat_conj h1, tensorB_eq_complexOfRing]
    refine MultiBlockCompression.triangular_of_offDiag fun x y hxy => ?_
    rw [Matrix.submatrix_apply, complexOfRing_apply]
    have : tensorBInt i (tauM x) (tauM y) = 0 := by
      revert i x y; decide
    rw [this, map_zero]
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, kronMat_conj h1,
      tensorB_eq_complexOfRing, Matrix.submatrix_apply, complexOfRing_apply]
    change _ = tensorC i p q
    rw [tensorC_eq_complexOfRing, complexOfRing_apply]
    congr 1
    obtain ⟨s, hs⟩ := s
    obtain rfl : hs = Finset.mem_univ s := rfl
    revert p q
    fin_cases s <;> fin_cases i <;> intro p q <;> fin_cases p <;> fin_cases q <;> decide
  unmatched _ t := t.elim0

theorem kronMat_tauM_row (A : Matrix (Fin 2) (Fin 2) ℂ) (s : {s // s ∈ labels})
    (p : Fin (dims s.1)) (k : Fin 4) : kronMat A (tauM ⟨Sum.inl s, p⟩) k = kronRow (A s.1) p k := by
  obtain ⟨s, hs⟩ := s
  fin_cases s <;> fin_cases p <;> fin_cases k <;> rfl

theorem kronMat_tauM_col (A : Matrix (Fin 2) (Fin 2) ℂ) (s : {s // s ∈ labels})
    (p : Fin (dims s.1)) (k : Fin 4) :
    kronMat A k (tauM ⟨Sum.inl s, p⟩) = kronCol (fun a => A a s.1) k p := by
  obtain ⟨s, hs⟩ := s
  fin_cases s <;> fin_cases p <;> fin_cases k <;> rfl

/-- **The split reductions `A ⊗ 1₂`** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.13): for every invertible `A`, `g = A ⊗ 1₂` is a split reduction of `B` onto two
copies of `C`, with `W_j = a_j ⊗ 1₂` (`a_j` the rows of `A`) and `V_j = u_j ⊗ 1₂` (`u_j` the columns
of `A⁻¹`). -/
theorem exists_split_multiBlockCompression_kronRow (A Ainv : Matrix (Fin 2) (Fin 2) ℂ)
    (h1 : A * Ainv = 1) (h2 : Ainv * A = 1) :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧ P.remainder = 0 ∧
      ∀ j : Fin 2, P.left ⟨j, Finset.mem_univ j⟩ = kronRow (A j) ∧
        P.right ⟨j, Finset.mem_univ j⟩ = kronCol fun a => Ainv a j := by
  refine ⟨splitRed A Ainv h1 h2, rfl, ?_, fun j => ⟨?_, ?_⟩⟩
  · funext i
    refine MultiBlockCompression.remainder_eq_zero_of_offDiag _ i fun x y hxy => ?_
    change conjMatrix (gaugeOfMatrix tauM _ _ (kronMat_inv h1) (kronMat_inv h2)) (tensorB i) x y =
      0
    rw [conjMatrix_gaugeOfMatrix, kronMat_conj h1, tensorB_eq_complexOfRing]
    change complexOfRing (Int.castRingHom ℂ) (tensorBInt i) (tauM x) (tauM y) = 0
    rw [complexOfRing_apply]
    have : tensorBInt i (tauM x) (tauM y) = 0 := tensorBInt_offDiag i x y hxy
    rw [this, map_zero]
  · rw [MultiBlockCompression.left_gaugeOfMatrix (splitRed A Ainv h1 h2) (τ := tauM)
      (hG := kronMat_inv h1) (hG' := kronMat_inv h2) rfl]
    ext b k
    exact kronMat_tauM_row A _ _ _
  · rw [MultiBlockCompression.right_gaugeOfMatrix (splitRed A Ainv h1 h2) (τ := tauM)
      (hG := kronMat_inv h1) (hG' := kronMat_inv h2) rfl]
    ext k b
    exact kronMat_tauM_col Ainv _ _ _

theorem kronRow_mul_kronCol_apply (a u : Fin 2 → ℂ) :
    (kronRow a * kronCol u) 0 0 = a 0 * u 0 + a 1 * u 1 := by
  simp [kronRow, kronCol, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Every split reduction is `A ⊗ 1₂`** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.13): a split reduction of `B` onto two copies of `C` has no zero block and is
`A ⊗ 1₂` for an invertible `A`: `W_j = a_j ⊗ 1₂` with `a_j` the rows of `A`, `V_j = u_j ⊗ 1₂` with
`u_j` the columns of `A⁻¹`. A second split reduction `g_tilde` has `W_tilde_j = ã_j ⊗ 1₂`,
`V_tilde_j = u_tilde_j ⊗ 1₂` likewise. -/
theorem exists_left_eq_kronRow_of_remainder_eq_zero
    (P : MultiBlockCompression tensorB labels blocks) (hP : P.remainder = 0) :
    P.z = 0 ∧ ∃ A U : Matrix (Fin 2) (Fin 2) ℂ, A * U = 1 ∧ U * A = 1 ∧
      ∀ j : Fin 2, P.left ⟨j, Finset.mem_univ j⟩ = kronRow (A j) ∧
        P.right ⟨j, Finset.mem_univ j⟩ = kronCol fun a => U a j := by
  have hz : P.z = 0 := by
    have := P.dim_eq
    simp at this
    omega
  have hB : ∀ i, tensorB i = ∑ t : {s // s ∈ labels}, P.right t * tensorC i * P.left t := by
    intro i
    have := congrFun hP i
    rw [MultiBlockCompression.remainder, Pi.zero_apply, sub_eq_zero] at this
    exact this
  have hW : ∀ s : {s // s ∈ labels}, ∀ i, P.left s * tensorB i = tensorC i * P.left s := by
    intro s i
    rw [hB, Matrix.mul_sum, Finset.sum_eq_single s]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.left_mul_right_self, Matrix.one_mul]
    · intro t _ ht
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.left_mul_right_of_ne (Ne.symm ht),
        Matrix.zero_mul, Matrix.zero_mul]
    · intro h; exact absurd (Finset.mem_univ s) h
  have hV : ∀ s : {s // s ∈ labels}, ∀ i, tensorB i * P.right s = P.right s * tensorC i := by
    intro s i
    rw [hB, Matrix.sum_mul, Finset.sum_eq_single s]
    · rw [Matrix.mul_assoc, Matrix.mul_assoc, P.left_mul_right_self, Matrix.mul_one]
    · intro t _ ht
      rw [Matrix.mul_assoc, Matrix.mul_assoc, P.left_mul_right_of_ne ht, Matrix.mul_zero,
        Matrix.mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  have hWf : ∀ s : {s // s ∈ labels}, P.left s = kronRow ![P.left s 0 0, P.left s 0 2] :=
    fun s => eq_kronRow_of_intertwines (P.left s) (hW s)
  have hVf : ∀ s : {s // s ∈ labels}, P.right s = kronCol ![P.right s 0 0, P.right s 2 0] :=
    fun s => eq_kronCol_of_intertwines (P.right s) (hV s)
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun j a =>
    ![P.left ⟨j, Finset.mem_univ j⟩ 0 0, P.left ⟨j, Finset.mem_univ j⟩ 0 2] a
  let U : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun a j =>
    ![P.right ⟨j, Finset.mem_univ j⟩ 0 0, P.right ⟨j, Finset.mem_univ j⟩ 2 0] a
  have hAU : A * U = 1 := by
    ext j k
    have hjk : (P.left ⟨j, Finset.mem_univ j⟩ * P.right ⟨k, Finset.mem_univ k⟩) 0 0 =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
      by_cases h : j = k
      · subst h
        rw [P.left_mul_right_self]
        simp
      · rw [P.left_mul_right_of_ne (fun h' => h (congrArg Subtype.val h'))]
        simp [h]
    rw [hWf, hVf, kronRow_mul_kronCol_apply] at hjk
    rw [← hjk, Matrix.mul_apply, Fin.sum_univ_two]
    simp [A, U]
  refine ⟨hz, A, U, hAU, mul_eq_one_comm.1 hAU, fun j => ⟨?_, ?_⟩⟩
  · exact hWf _
  · exact hVf _

theorem kronRowMat_smul (c : ℂ) (a : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    kronRowMat (c • a) M = c • kronRowMat a M := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [kronRowMat] <;> ring

theorem kronRowMat_apply (a : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (p q a' : Fin 2) :
    kronRowMat a M p ⟨2 * a'.val + q.val, by omega⟩ = a a' * M p q := by
  fin_cases p <;> fin_cases q <;> fin_cases a' <;> simp [kronRowMat]

/-- **Proportional reading maps** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.13): for two reductions with `W_s = a ⊗ 1₂`, `W_tilde_s = ã ⊗ 1₂` (every split reduction,
by `exists_left_eq_kronRow_of_remainder_eq_zero`), `W_tilde_s B^w = λ W_s B^w` holds for some `λ`
and some word with `C^w ≠ 0` iff `ã` is proportional to `a`, and then it holds for every word. -/
theorem exists_left_mul_evalWord_eq_smul_iff (P Q : MultiBlockCompression tensorB labels blocks)
    (s : {s // s ∈ labels})
    {a ã : Fin 2 → ℂ} (hP : P.left s = kronRow a) (hQ : Q.left s = kronRow ã) :
    ((∃ c : ℂ, ∃ w : List (Fin 2), Kraus.evalWord tensorC w ≠ 0 ∧
        Q.left s * Kraus.evalWord tensorB w = c • (P.left s * Kraus.evalWord tensorB w)) ↔
      ∃ c : ℂ, ã = c • a) ∧
    ∀ c : ℂ, ã = c • a → ∀ w : List (Fin 2),
      Q.left s * Kraus.evalWord tensorB w = c • (P.left s * Kraus.evalWord tensorB w) := by
  have hall : ∀ c : ℂ, ã = c • a → ∀ w : List (Fin 2),
      Q.left s * Kraus.evalWord tensorB w = c • (P.left s * Kraus.evalWord tensorB w) := by
    intro c hc w
    rw [hP, hQ, evalWord_tensorB, kronRow_mul_oneKron, kronRow_mul_oneKron, hc, kronRowMat_smul]
  refine ⟨⟨?_, fun ⟨c, hc⟩ => ⟨c, [], by simp, hall c hc []⟩⟩, hall⟩
  rintro ⟨c, w, hw, h⟩
  rw [hP, hQ, evalWord_tensorB, kronRow_mul_oneKron, kronRow_mul_oneKron] at h
  obtain ⟨p, q, hpq⟩ : ∃ p q, Kraus.evalWord tensorC w p q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (Matrix.ext hcon)
  refine ⟨c, funext fun a' => ?_⟩
  have e := congrFun (congrFun h p) ⟨2 * a'.val + q.val, by omega⟩
  rw [Matrix.smul_apply, kronRowMat_apply, kronRowMat_apply, smul_eq_mul, ← mul_assoc] at e
  exact mul_right_cancel₀ hpq e

/-! ### The printed instance -/

theorem isNormal_blocks : ∀ s ∈ labels, Kraus.IsNormal (blocks s) := fun _ _ => isNormal_tensorC

theorem dims_pos : ∀ s ∈ labels, 0 < dims s := fun _ _ => Nat.two_pos

theorem gauge_splitRed (A Ainv : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * Ainv = 1)
    (h2 : Ainv * A = 1) : (splitRed A Ainv h1 h2).gauge =
      gaugeOfMatrix tauM (kronMat A) (kronMat Ainv) (kronMat_inv h1) (kronMat_inv h2) := rfl

/-- Membership in the flag of `A ⊗ 1₂`: the coordinates `(A ⊗ 1₂) v` at the positions `≥ k`
vanish. -/
theorem mem_flagVec_splitRed (A Ainv : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * Ainv = 1)
    (h2 : Ainv * A = 1) (k : Fin (labels.card + (splitRed A Ainv h1 h2).z + 1))
    (v : Fin 4 → ℂ) :
    v ∈ flagVec (splitRed A Ainv h1 h2) k ↔
      ∀ n : Fin 4, k.val ≤ (![0, 0, 1, 1] : Fin 4 → ℕ) n → (kronMat A *ᵥ v) n = 0 := by
  have hpos : ∀ n : Fin 4, (((splitRed A Ainv h1 h2).ord (tauM.symm n).1).castSucc).val =
      (![0, 0, 1, 1] : Fin 4 → ℕ) n := by
    intro n; fin_cases n <;> rfl
  rw [mem_flagVec_gaugeOfMatrix _ (gauge_splitRed A Ainv h1 h2)]
  constructor
  · intro h n hn
    have := h (tauM.symm n) (Fin.le_def.2 (by rw [hpos]; exact hn))
    erw [Equiv.apply_symm_apply] at this
    exact this
  · intro h y hy
    obtain ⟨n, rfl⟩ := tauM.symm.surjective y
    erw [Equiv.apply_symm_apply]
    exact h n (by rw [← hpos]; exact Fin.le_def.1 hy)

/-! ### Any two split reductions -/

/-- The first copy. -/
abbrev slot0 : {s // s ∈ labels} := ⟨0, Finset.mem_univ _⟩

/-- The second copy. -/
abbrev slot1 : {s // s ∈ labels} := ⟨1, Finset.mem_univ _⟩

/-- The four entries of `M N = 1` for `2 × 2` matrices. -/
theorem mul_eq_one_entries {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : M * N = 1) :
    M 0 0 * N 0 0 + M 0 1 * N 1 0 = 1 ∧ M 0 0 * N 0 1 + M 0 1 * N 1 1 = 0 ∧
      M 1 0 * N 0 0 + M 1 1 * N 1 0 = 0 ∧ M 1 0 * N 0 1 + M 1 1 * N 1 1 = 1 := by
  have e : ∀ a b, (M * N) a b = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := fun a b => by rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e 0 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e 0 1
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e 1 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e 1 1

/-- A vector killed by the second row of an invertible `M` is a multiple of the first column of
`M⁻¹`, the multiple being its pairing with the first row. -/
theorem eq_smul_col_of_row_one {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : N * M = 1)
    {y : Fin 2 → ℂ} (hy : M 1 0 * y 0 + M 1 1 * y 1 = 0) :
    y = (M 0 0 * y 0 + M 0 1 * y 1) • fun a => N a 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := mul_eq_one_entries h
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change y 0 = (M 0 0 * y 0 + M 0 1 * y 1) * N 0 0
    linear_combination (-y 0) * e00 - y 1 * e01 + N 0 1 * hy
  · change y 1 = (M 0 0 * y 0 + M 0 1 * y 1) * N 1 0
    linear_combination (-y 0) * e10 - y 1 * e11 + N 1 1 * hy

/-- The first member of the flag of `A ⊗ 1₂`: the second row of `A` kills both columns of the
`2 × 2` array of coordinates. -/
theorem mem_flagVec_splitRed_one (A Ainv : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * Ainv = 1)
    (h2 : Ainv * A = 1) (k : Fin (labels.card + (splitRed A Ainv h1 h2).z + 1)) (hk : k.val = 1)
    (v : Fin 4 → ℂ) :
    v ∈ flagVec (splitRed A Ainv h1 h2) k ↔
      A 1 0 * v 0 + A 1 1 * v 2 = 0 ∧ A 1 0 * v 1 + A 1 1 * v 3 = 0 := by
  rw [mem_flagVec_splitRed, hk]
  have c2 : (kronMat A *ᵥ v) 2 = A 1 0 * v 0 + A 1 1 * v 2 := by
    simp [kronMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have c3 : (kronMat A *ᵥ v) 3 = A 1 0 * v 1 + A 1 1 * v 3 := by
    simp [kronMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  constructor
  · intro h
    exact ⟨c2 ▸ h 2 (by decide), c3 ▸ h 3 (by decide)⟩
  · rintro ⟨h2, h3⟩ n hn
    fin_cases n
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · exact c2.trans h2
    · exact c3.trans h3

/-- The first member of the flag of `A ⊗ 1₂` is `ℂ u₁ ⊗ ℂ²`, `u₁` the first column of `A⁻¹`. -/
theorem flagVec_splitRed_one (A Ainv : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * Ainv = 1)
    (h2 : Ainv * A = 1) (k : Fin (labels.card + (splitRed A Ainv h1 h2).z + 1))
    (hk : k.val = 1) : flagVec (splitRed A Ainv h1 h2) k = lineTensor fun a => Ainv a 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := mul_eq_one_entries h1
  ext x
  rw [mem_flagVec_splitRed_one A Ainv h1 h2 k hk]
  constructor
  · rintro ⟨h02, h13⟩
    have y0 := eq_smul_col_of_row_one h2 (y := ![x 0, x 2]) h02
    have y1 := eq_smul_col_of_row_one h2 (y := ![x 1, x 3]) h13
    have a0 : x 0 = (A 0 0 * x 0 + A 0 1 * x 2) * Ainv 0 0 := congrFun y0 0
    have a1 : x 2 = (A 0 0 * x 0 + A 0 1 * x 2) * Ainv 1 0 := congrFun y0 1
    have b0 : x 1 = (A 0 0 * x 1 + A 0 1 * x 3) * Ainv 0 0 := congrFun y1 0
    have b1 : x 3 = (A 0 0 * x 1 + A 0 1 * x 3) * Ainv 1 0 := congrFun y1 1
    refine ⟨![A 0 0 * x 0 + A 0 1 * x 2, A 0 0 * x 1 + A 0 1 * x 3], funext fun i => ?_⟩
    fin_cases i
    · change Ainv 0 0 * (A 0 0 * x 0 + A 0 1 * x 2) = x 0
      linear_combination -a0
    · change Ainv 0 0 * (A 0 0 * x 1 + A 0 1 * x 3) = x 1
      linear_combination -b0
    · change Ainv 1 0 * (A 0 0 * x 0 + A 0 1 * x 2) = x 2
      linear_combination -a1
    · change Ainv 1 0 * (A 0 0 * x 1 + A 0 1 * x 3) = x 3
      linear_combination -b1
  · rintro ⟨w, rfl⟩
    constructor
    · change A 1 0 * (Ainv 0 0 * w 0) + A 1 1 * (Ainv 1 0 * w 0) = 0
      linear_combination w 0 * e10
    · change A 1 0 * (Ainv 0 0 * w 1) + A 1 1 * (Ainv 1 0 * w 1) = 0
      linear_combination w 1 * e10

/-- The reading map `ã ⊗ 1₂` on `u ⊗ v` is `(ã u) v`. -/
theorem kronRow_mulVec_kron (a u v : Fin 2 → ℂ) :
    kronRow a *ᵥ kron u v = (a 0 * u 0 + a 1 * u 1) • v := by
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    simp [kronRow, kron, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The reading map of the copy `j` of `A ⊗ 1₂` is `a_j ⊗ 1₂`. -/
theorem left_splitRed (A Ainv : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * Ainv = 1)
    (h2 : Ainv * A = 1) (j : Fin 2) :
    (splitRed A Ainv h1 h2).left ⟨j, Finset.mem_univ j⟩ = kronRow (A j) := by
  rw [MultiBlockCompression.left_gaugeOfMatrix (splitRed A Ainv h1 h2) (τ := tauM)
    (hG := kronMat_inv h1) (hG' := kronMat_inv h2) rfl]
  ext b c
  exact kronMat_tauM_row A _ _ _

/-- **Two split reductions with different flags** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.13), for any two split reductions `g = A ⊗ 1₂`, `g_tilde = Ã ⊗ 1₂` (every
split reduction, by `exists_left_eq_kronRow_of_remainder_eq_zero`) with `ℂ u₁ ≠ ℂ u_tilde₁` (`u_j`,
`u_tilde_j` the columns of `A⁻¹`, `Ã⁻¹`): the matching pairs position `1` of `g` with position `2`
of `g_tilde`; `U = ℂ u₁ ⊗ ℂ²`, `N = ℂ u_tilde₁ ⊗ ℂ²`; the intertwiner is the scalar `λ = ã₂ u₁ ≠ 0`
(`ã₂` the second row of `Ã`), that is `W_tilde₂ = λ W₁` on `U`, with `W_tilde₂ (u₁ ⊗ v) = λ v`; and
`u_tilde₂ - λ⁻¹ u₁ ∈ ℂ u_tilde₁`. -/
theorem matching_left_splitRed_of_span_ne (A Ainv At AtInv : Matrix (Fin 2) (Fin 2) ℂ)
    (h1 : A * Ainv = 1) (h2 : Ainv * A = 1) (h1' : At * AtInv = 1) (h2' : AtInv * At = 1)
    (hne : Submodule.span ℂ {fun a => Ainv a 0} ≠ Submodule.span ℂ {fun a => AtInv a 0}) :
    let P := splitRed A Ainv h1 h2
    let Q := splitRed At AtInv h1' h2'
    let π := P.matching Q isNormal_blocks dims_pos isNormal_blocks dims_pos
    let k := P.ord (Sum.inl slot0)
    let u₁ : Fin 2 → ℂ := fun a => Ainv a 0
    let u_tilde₁ : Fin 2 → ℂ := fun a => AtInv a 0
    let u_tilde₂ : Fin 2 → ℂ := fun a => AtInv a 1
    let lam : ℂ := At 1 0 * u₁ 0 + At 1 1 * u₁ 1
    π k = Q.ord (Sum.inl slot1) ∧ k.val = 0 ∧ (Q.ord (Sum.inl slot1)).val = 1 ∧
    ((P.flag k.succ ⊓ Q.flag (π k).succ).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = lineTensor u₁ ∧
    ((P.flag k.castSucc ⊔ Q.flag (π k).castSucc).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = lineTensor u_tilde₁ ∧
    lam ≠ 0 ∧
    (∀ x ∈ lineTensor u₁, Q.left slot1 *ᵥ x = lam • (P.left slot0 *ᵥ x)) ∧
    (∀ v : Fin 2 → ℂ, Q.left slot1 *ᵥ kron u₁ v = lam • v) ∧
    u_tilde₂ - lam⁻¹ • u₁ ∈ Submodule.span ℂ {u_tilde₁} := by
  intro P Q π k u₁ u_tilde₁ u_tilde₂ lam
  obtain ⟨e00, e01, e10, e11⟩ := mul_eq_one_entries h1
  obtain ⟨f00, f01, f10, f11⟩ := mul_eq_one_entries h1'
  have hu : u₁ ≠ 0 := by
    intro h
    have a : Ainv 0 0 = 0 := congrFun h 0
    have b : Ainv 1 0 = 0 := congrFun h 1
    rw [a, b] at e00
    simp at e00
  have hlam : lam ≠ 0 := by
    intro h0
    have hy : u₁ = (At 0 0 * u₁ 0 + At 0 1 * u₁ 1) • u_tilde₁ := eq_smul_col_of_row_one h2' h0
    have hc : At 0 0 * u₁ 0 + At 0 1 * u₁ 1 ≠ 0 := by
      intro hc
      rw [hc, zero_smul] at hy
      exact hu hy
    exact hne ((congrArg (fun y => Submodule.span ℂ {y}) hy).trans
      (Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc) _))
  have hWt : Q.left slot1 = kronRow (At 1) := left_splitRed At AtInv h1' h2' 1
  have hW : P.left slot0 = kronRow (A 0) := left_splitRed A Ainv h1 h2 0
  have hm : π k = Q.ord (Sum.inl slot1) := by
    refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨kron u₁ ![1, 0], ?_, ?_, ?_⟩ ?_
    · rw [flagVec_splitRed_one A Ainv h1 h2 _ rfl]
      exact ⟨![1, 0], rfl⟩
    · rw [flagVec_eq_top _ _ rfl]; exact Submodule.mem_top
    · rw [flagVec_eq_bot _ _ rfl, Submodule.mem_bot]
      intro h
      apply hu
      refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · have := congrFun h 0
        simpa [kron] using this
      · have := congrFun h 2
        simpa [kron] using this
    · intro j hj v hv1 hv2
      have hj0 : j.val = 0 := by
        have := Fin.lt_def.1 hj
        have h1 : (Q.ord (Sum.inl slot1)).val = 1 := rfl
        omega
      rw [flagVec_splitRed_one A Ainv h1 h2 _ rfl] at hv1
      rw [mem_flagVec_splitRed_one At AtInv h1' h2' _ (by rw [Fin.val_succ, hj0])] at hv2
      obtain ⟨w, rfl⟩ := hv1
      obtain ⟨c0, c1⟩ := hv2
      have hw0 : lam * w 0 = 0 := by
        change At 1 0 * (Ainv 0 0 * w 0) + At 1 1 * (Ainv 1 0 * w 0) = 0 at c0
        change (At 1 0 * Ainv 0 0 + At 1 1 * Ainv 1 0) * w 0 = 0
        linear_combination c0
      have hw1 : lam * w 1 = 0 := by
        change At 1 0 * (Ainv 0 0 * w 1) + At 1 1 * (Ainv 1 0 * w 1) = 0 at c1
        change (At 1 0 * Ainv 0 0 + At 1 1 * Ainv 1 0) * w 1 = 0
        linear_combination c1
      have hw : w = 0 := funext (Fin.forall_fin_two.2
        ⟨(mul_eq_zero.1 hw0).resolve_left hlam, (mul_eq_zero.1 hw1).resolve_left hlam⟩)
      rw [hw, map_zero]
      exact Submodule.zero_mem _
  have hkron : ∀ v, Q.left slot1 *ᵥ kron u₁ v = lam • v := by
    intro v
    rw [hWt, kronRow_mulVec_kron]
  refine ⟨hm, rfl, rfl, ?_, ?_, hlam, ?_, hkron, ?_⟩
  · rw [hm, map_toVec_inf]
    change flagVec P _ ⊓ flagVec Q _ = _
    rw [flagVec_eq_top Q _ rfl, inf_top_eq]
    exact flagVec_splitRed_one A Ainv h1 h2 _ rfl
  · rw [hm, map_toVec_sup]
    change flagVec P _ ⊔ flagVec Q _ = _
    rw [flagVec_eq_bot P _ rfl, bot_sup_eq]
    exact flagVec_splitRed_one At AtInv h1' h2' _ rfl
  · rintro x ⟨v, rfl⟩
    change Q.left slot1 *ᵥ kron u₁ v = lam • (P.left slot0 *ᵥ kron u₁ v)
    rw [hkron, hW, kronRow_mulVec_kron]
    change lam • v = lam • ((A 0 0 * Ainv 0 0 + A 0 1 * Ainv 1 0) • v)
    rw [e00, one_smul]
  · have hy : u_tilde₂ - lam⁻¹ • u₁ =
        (At 0 0 * (u_tilde₂ - lam⁻¹ • u₁) 0 + At 0 1 * (u_tilde₂ - lam⁻¹ • u₁) 1) • u_tilde₁ := by
      refine eq_smul_col_of_row_one h2' ?_
      change At 1 0 * (AtInv 0 1 - lam⁻¹ * Ainv 0 0) + At 1 1 * (AtInv 1 1 - lam⁻¹ * Ainv 1 0) = 0
      have hl : lam⁻¹ * (At 1 0 * Ainv 0 0 + At 1 1 * Ainv 1 0) = 1 := inv_mul_cancel₀ hlam
      linear_combination f11 - hl
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The matrix `Ã = [[1, 0], [1, 1]]`. -/
noncomputable def matAt : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 1]

/-- `Ã⁻¹ = [[1, 0], [-1, 1]]`. -/
noncomputable def matAtInv : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; -1, 1]

theorem matAt_mul : matAt * matAtInv = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [matAt, matAtInv, Matrix.mul_apply]

theorem matAtInv_mul : matAtInv * matAt = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [matAt, matAtInv, Matrix.mul_apply]

/-- The split reduction `g = 1`. -/
noncomputable abbrev redOne : MultiBlockCompression tensorB labels blocks :=
  splitRed 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)

/-- The split reduction `g_tilde = Ã ⊗ 1₂`. -/
noncomputable abbrev redAt : MultiBlockCompression tensorB labels blocks :=
  splitRed matAt matAtInv matAt_mul matAtInv_mul

/-- **The printed instance** (*The asymmetric fundamental theorem of matrix product states*, Example
6.13), for `A = 1` and `Ã = [[1, 0], [1, 1]]`, where `ℂ u₁ = ℂ e₁ ≠ ℂ u_tilde₁ = ℂ (1, -1)`: the
matching pairs position `1` of `g` with position `2` of `g_tilde`; `U = ℂ u₁ ⊗ ℂ²`,
`N = ℂ u_tilde₁ ⊗ ℂ²`; the intertwiner is the scalar `λ = ã₂ u₁ = 1`, with
`W_tilde₂ (u₁ ⊗ v) = λ v`; and `u_tilde₂ - λ⁻¹ u₁ = (-1, 1)ᵀ ∈ ℂ u_tilde₁`. The matching, `U`, `N`
and `W_tilde₂` are read off `matching_left_splitRed_of_span_ne`. -/
theorem matching_left_redOne_redAt :
    let π := redOne.matching redAt isNormal_blocks dims_pos isNormal_blocks dims_pos
    let k := redOne.ord (Sum.inl slot0)
    π k = redAt.ord (Sum.inl slot1) ∧ k.val = 0 ∧ (redAt.ord (Sum.inl slot1)).val = 1 ∧
    ((redOne.flag k.succ ⊓ redAt.flag (π k).succ).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = lineTensor ![1, 0] ∧
    ((redOne.flag k.castSucc ⊔ redAt.flag (π k).castSucc).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = lineTensor ![1, -1] ∧
    (fun a => matAtInv a 0) = ![1, -1] ∧
    matAt 1 0 * 1 + matAt 1 1 * 0 = (1 : ℂ) ∧
    (∀ v : Fin 2 → ℂ, redAt.left slot1 *ᵥ kron ![1, 0] v = (1 : ℂ) • v) ∧
    (fun a => matAtInv a 1) - (1 : ℂ)⁻¹ • ![1, 0] = ![-1, 1] ∧
    ![(-1 : ℂ), 1] ∈ Submodule.span ℂ {![(1 : ℂ), -1]} := by
  intro π k
  have hu1 : (fun a => (1 : Matrix (Fin 2) (Fin 2) ℂ) a 0) = ![1, 0] := by
    exact funext (Fin.forall_fin_two.2 ⟨by simp, by simp⟩)
  have hut : (fun a => matAtInv a 0) = ![1, -1] := by
    funext a; fin_cases a <;> simp [matAtInv]
  have hne : Submodule.span ℂ {fun a => (1 : Matrix (Fin 2) (Fin 2) ℂ) a 0} ≠
      Submodule.span ℂ {fun a => matAtInv a 0} := by
    rw [hu1, hut]
    intro h
    have hmem : ![(1 : ℂ), -1] ∈ Submodule.span ℂ {![(1 : ℂ), 0]} := by
      rw [h]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have := congrFun hc 1
    simp at this
  obtain ⟨hm, -, -, hU, hN, -, -, hkron, -⟩ := matching_left_splitRed_of_span_ne 1 1 matAt matAtInv
    (Matrix.mul_one 1) (Matrix.mul_one 1) matAt_mul matAtInv_mul hne
  rw [hu1] at hU hkron
  rw [hut] at hN
  refine ⟨hm, rfl, rfl, hU, hN, hut, by simp [matAt], fun v => (hkron v).trans ?_, ?_, ?_⟩
  · congr 1
    simp [matAt]
  · funext a; fin_cases a <;> simp [matAtInv]
  · exact Submodule.mem_span_singleton.2 ⟨-1, by ext i; fin_cases i <;> simp⟩

end Multiplicity

end MultiBlockExamples
