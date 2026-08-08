/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.DirectSumConditionalExpectation
import TNLean.Channel.PositiveConditionalExpectationDirectSum

/-!
# Trace-preserving conditional expectations onto matrix star subalgebras

Every star subalgebra of a full complex matrix algebra has unitary block coordinates in
which it is a direct sum of right matrix factors.  Transporting the normalized coordinate
expectation through this change of coordinates gives a trace-preserving completely positive
conditional expectation onto the original star subalgebra.

## Main result

* `StarSubalgebra.exists_krausCPTP_conditionalExpectation`: every matrix star subalgebra is
  the range of a trace-preserving completely positive conditional expectation.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5 and
  Equation (1.40)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace StarSubalgebra

/-- Every star subalgebra of a full complex matrix algebra admits a trace-preserving
completely positive conditional expectation.

The map is obtained from the coordinate direct-sum expectation by the unitary block
coordinates of Wolf, Equation (1.39).  This is the matrix-algebra codomain step in the
operator-system extension argument following Wolf, Proposition 1.5 and Equation (1.40);
it does not corestrict the codomain to the subtype of the star subalgebra. -/
theorem exists_krausCPTP_conditionalExpectation
    {n : Type*} [Fintype n] [DecidableEq n]
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    ∃ E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
      IsKrausCPTP E ∧ Kraus.IsConditionalExpectation E S := by
  classical
  obtain ⟨K, d, m, e, U, hU, hd, hm, hBlock⟩ :=
    S.exists_unitary_conj_blockDiagonal_iff
  let Φ := Matrix.unitaryReindexLinearEquiv e U hU
  let E₀ := Matrix.coordinateDirectSumConditionalExpectation (m := m) (d := d)
  let E := Φ.symm.toLinearMap ∘ₗ E₀ ∘ₗ Φ.toLinearMap
  obtain ⟨hE₀CPTP, hE₀⟩ :=
    Matrix.coordinateDirectSumConditionalExpectation_isKrausCPTP_and_isConditionalExpectation
      hm
  have hΦCPTP : IsKrausCPTP Φ.toLinearMap :=
    Matrix.unitaryReindexLinearEquiv_toLinearMap_isKrausCPTP e U hU
  have hΦsymmCPTP : IsKrausCPTP Φ.symm.toLinearMap :=
    Matrix.unitaryReindexLinearEquiv_symm_toLinearMap_isKrausCPTP e U hU
  have hECPTP : IsKrausCPTP E :=
    isKrausCPTP_comp (isKrausCPTP_comp hΦCPTP hE₀CPTP) hΦsymmCPTP
  have hSymmConj (A : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ) :
      star U * Φ.symm A * U = Matrix.reindex e e A := by
    rw [Matrix.unitaryReindexLinearEquiv_symm_apply]
    have hUstarU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    calc
      star U * (U * Matrix.reindex e e A * star U) * U =
          (star U * U) * Matrix.reindex e e A * (star U * U) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.reindex e e A := by rw [hUstarU, Matrix.one_mul, Matrix.mul_one]
  refine ⟨E, hECPTP, ?_⟩
  let hE₀' : Kraus.IsConditionalExpectation E₀
      (Matrix.coordinateRightFactorStarSubalgebra (m := m) (d := d)) := hE₀
  exact {
    positive := (isKrausCP_iff_isCPMap.mp hECPTP.isKrausCP).isPositiveMap
    idempotent := by
      intro A
      change Φ.symm (E₀ (Φ (Φ.symm (E₀ (Φ A))))) = Φ.symm (E₀ (Φ A))
      rw [Φ.apply_symm_apply, hE₀'.idempotent]
    unital := by
      change Φ.symm (E₀ (Φ 1)) = 1
      rw [Matrix.unitaryReindexLinearEquiv_one, hE₀'.unital,
        ← Matrix.unitaryReindexLinearEquiv_one e U hU, Φ.symm_apply_apply]
    range_subset := by
      intro A
      apply (hBlock (E A)).mpr
      obtain ⟨B, hB⟩ := (Matrix.mem_coordinateRightFactorStarSubalgebra
        (m := m) (d := d) (E₀ (Φ A))).mp (hE₀'.range_subset (Φ A))
      refine ⟨B, ?_⟩
      change star U * Φ.symm (E₀ (Φ A)) * U = _
      rw [hSymmConj, hB]
    fixes := by
      intro A hA
      obtain ⟨B, hB⟩ := (hBlock A).mp hA
      have hΦA : Φ A = Matrix.blockDiagonal' fun k ↦
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k := by
        rw [Matrix.unitaryReindexLinearEquiv_apply, hB]
        simpa only [Matrix.symm_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv] using
          (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply
            (Matrix.blockDiagonal' fun k ↦
              (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k)
      have hE₀Fix : E₀ (Φ A) = Φ A := hE₀'.fixes (Φ A)
        ((Matrix.mem_coordinateRightFactorStarSubalgebra
          (m := m) (d := d) (Φ A)).mpr ⟨B, hΦA⟩)
      change Φ.symm (E₀ (Φ A)) = A
      rw [hE₀Fix, Φ.symm_apply_apply]
  }

end StarSubalgebra
