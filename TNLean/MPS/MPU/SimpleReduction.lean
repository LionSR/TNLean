/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleSupportCompression
import TNLean.MPS.MPU.RectangularSourceRanks

/-!
# Simplicity of a canonical rectangular reduction

An actual reduction contracts every open word, not only the one-site letters.
This carries the normalized-diagonal insertion identity through the doubled
network. A canonical target already has a rank-one normalized transfer power,
so that identity recovers simplicity at the original physical scale.

Source: arXiv:1703.09188, equations `simple1`, `simple2`, and `Erightleft`,
and the canonical-form discussion, lines 269--281 and 319--374.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D E : ℕ} {U : MPOTensor d D} {V : MPOTensor d E}
  {A : Matrix (Fin E) (Fin D) ℂ} {B : Matrix (Fin D) (Fin E) ℂ}

/-- A rectangular reduction contracts doubled open words with the doubled
reduction matrices. The full-word reduction identities, rather than just their
single-letter consequences, are essential.

Sources: arXiv:1706.07329v2, Definition following Proposition 20;
arXiv:1703.09188, the double-layer contractions of Definition III.2. -/
theorem doubleLayer_evalWord_of_isReduction
    (h : MPSTensor.IsReduction U.toMPSTensor V.toMPSTensor A B)
    {N : ℕ} (σ τ : Fin N → Fin d) :
    doubledBondMap A * evalWord (doubleLayerTensor U) (List.ofFn σ) (List.ofFn τ) *
        doubledBondMap B =
      evalWord (doubleLayerTensor V) (List.ofFn σ) (List.ofFn τ) := by
  let I := (Kraus.decodeBlockEquiv d N).symm σ
  let J := (Kraus.decodeBlockEquiv d N).symm τ
  have hblock := eq_rectangularSandwich_of_isReduction (isReduction_blockTensor h N)
  calc
    _ = doubleLayerTensor (fun i j ↦ A * blockTensor U N i j * B) I J := by
      rw [doubleLayer_rectangularSandwich]
      simp only [I, J, doubleLayerTensor_blockTensor_decodeBlockEquiv_symm]
    _ = doubleLayerTensor (blockTensor V N) I J := by rw [← hblock]
    _ = _ := doubleLayerTensor_blockTensor_decodeBlockEquiv_symm V N σ τ

/-- The normalized-diagonal insertion identity of a simple tensor descends
through a full-word rectangular reduction, without physically blocking the
target tensor.

Source: arXiv:1703.09188, equations `simple1`, `simple2`, and `Erightleft`,
lines 269--281 and 356--374. -/
theorem IsMPUSimple.normalizedDiagonal_insertion_of_isReduction
    [NeZero d] (hU : IsMPUSimple U)
    (h : MPSTensor.IsReduction U.toMPSTensor V.toMPSTensor A B)
    (i j k l : Fin d) :
    doubleLayerTensor V i j * normalizedDiagonal (doubleLayerTensor V) *
        doubleLayerTensor V k l =
      doubleLayerTensor V i j * doubleLayerTensor V k l := by
  classical
  have htwo : doubledBondMap A *
      (doubleLayerTensor U i j * doubleLayerTensor U k l) * doubledBondMap B =
      doubleLayerTensor V i j * doubleLayerTensor V k l := by
    simpa [List.ofFn_succ, List.ofFn_zero, evalWord] using
      doubleLayer_evalWord_of_isReduction h ![i, k] ![j, l]
  have hthree (q : Fin d) : doubledBondMap A *
      (doubleLayerTensor U i j * doubleLayerTensor U q q * doubleLayerTensor U k l) *
        doubledBondMap B =
      doubleLayerTensor V i j * doubleLayerTensor V q q * doubleLayerTensor V k l := by
    simpa [List.ofFn_succ, List.ofFn_zero, evalWord, Matrix.mul_assoc] using
      doubleLayer_evalWord_of_isReduction h ![i, q, k] ![j, q, l]
  have hLHS : doubleLayerTensor V i j * normalizedDiagonal (doubleLayerTensor V) *
        doubleLayerTensor V k l =
      (d : ℂ)⁻¹ • ∑ q : Fin d,
        doubleLayerTensor V i j * doubleLayerTensor V q q *
          doubleLayerTensor V k l := by
    rw [normalizedDiagonal_eq_smul_sum_diagonal, Matrix.mul_smul, Matrix.smul_mul,
      Finset.mul_sum, Finset.sum_mul]
  have hRHS : doubledBondMap A *
        (doubleLayerTensor U i j * normalizedDiagonal (doubleLayerTensor U) *
          doubleLayerTensor U k l) * doubledBondMap B =
      (d : ℂ)⁻¹ • ∑ q : Fin d,
        doubledBondMap A *
          (doubleLayerTensor U i j * doubleLayerTensor U q q *
            doubleLayerTensor U k l) * doubledBondMap B := by
    rw [normalizedDiagonal_eq_smul_sum_diagonal, Matrix.mul_smul, Matrix.smul_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul]
  calc doubleLayerTensor V i j * normalizedDiagonal (doubleLayerTensor V) *
          doubleLayerTensor V k l
      = (d : ℂ)⁻¹ • ∑ q : Fin d,
          doubleLayerTensor V i j * doubleLayerTensor V q q *
            doubleLayerTensor V k l := hLHS
    _ = (d : ℂ)⁻¹ • ∑ q : Fin d,
          doubledBondMap A *
            (doubleLayerTensor U i j * doubleLayerTensor U q q *
              doubleLayerTensor U k l) * doubledBondMap B := by
          congr 1
          exact Finset.sum_congr rfl fun q _ ↦ (hthree q).symm
    _ = doubledBondMap A *
          (doubleLayerTensor U i j * normalizedDiagonal (doubleLayerTensor U) *
            doubleLayerTensor U k l) * doubledBondMap B := hRHS.symm
    _ = doubledBondMap A *
          (doubleLayerTensor U i j * doubleLayerTensor U k l) * doubledBondMap B := by
          rw [hU.letter_mul_normalizedDiagonal_mul_letter]
    _ = doubleLayerTensor V i j * doubleLayerTensor V k l := htwo

/-- A canonical-form-II target of an actual rectangular reduction of a simple
tensor is simple at the same physical scale. The target's canonical transfer
power supplies the rank-one insertion; no further physical blocking is used.

Source: arXiv:1703.09188, canonical-form discussion and Definition III.2,
lines 269--281 and 319--374. -/
theorem IsMPUCanonicalFormII.isMPUSimple_of_isReduction
    (hV : IsMPUCanonicalFormII V) (hU : IsMPUSimple U)
    (h : MPSTensor.IsReduction U.toMPSTensor V.toMPSTensor A B) :
    IsMPUSimple V := by
  let : NeZero d := hV.neZero_phys
  exact hV.isMPU.isMPUSimple_of_simple2 _ _
    (simple2_of_normalizedDiagonal_insertion
      (hU.normalizedDiagonal_insertion_of_isReduction h) _ _
      (max (E * E - 1) 1) (by omega) hV.normalizedDiagonal_pow_eq_vecMulVec)

end MPOTensor
