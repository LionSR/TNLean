/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalSkewNormalForm
import TNLean.Algebra.UnitaryCongruence

/-!
# Unitary congruence to the interleaved skew form

The real orthogonal normal form, combined with the real skew-unitary reduction,
gives the direct complex skew-unitary congruence. The conclusion uses exactly
the source's `Y = !![0, 1; -1, 0]` blocks in interleaved order.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1703.09188, proof of
  `corconj`, lines 1129–1140. This is the matrix normal-form ingredient in that
  proof; it does not assert the full MPU classification corollary.
-/

open scoped Matrix

namespace Matrix

/-- The complex form of the source's interleaved sum of real `Y` blocks. -/
def complexInterleavedSkewFormFin (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  (interleavedSkewFormFin m).map Complex.ofReal

/-- A complex skew-symmetric unitary matrix of size `2*m` is unitarily
congruent to the standard interleaved skew form. This is the direct Youla
normal form used in arXiv:1703.09188, proof of `corconj`, lines 1129–1140.
There is no real-entry, determinant or supplied-basis hypothesis. -/
theorem exists_unitary_congruence_interleavedSkewForm
    (m : ℕ) (x : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ)
    (hx : x ∈ unitaryGroup (Fin (2 * m)) ℂ) (hskew : xᵀ = -x) :
    ∃ U : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ,
      U ∈ unitaryGroup (Fin (2 * m)) ℂ ∧
        x = Uᵀ * complexInterleavedSkewFormFin m * U := by
  classical
  obtain ⟨S, Λ, -, hS, hΛreal, hΛskew, hΛunitary, -, hfactor⟩ :=
    exists_skew_unitary_congruence x hx hskew
  let f : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ →+*
      Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := Complex.ofRealHom.mapMatrix
  have hf : Function.Injective f := Matrix.map_injective Complex.ofReal_injective
  have hftranspose (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
      f Mᵀ = (f M)ᵀ := rfl
  have hfstar (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
      f Mᵀ = (f M)ᴴ := by
    ext i j
    simp [f, Matrix.conjTranspose_apply]
  let A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := Λ.map Complex.re
  have hreal : f A = Λ := by
    ext i j
    have h := congrFun (congrFun hΛreal i) j
    change starRingEnd ℂ (Λ i j) = Λ i j at h
    exact Complex.conj_eq_iff_re.mp h
  have hA : A ∈ orthogonalGroup (Fin (2 * m)) ℝ := by
    rw [mem_orthogonalGroup_iff]
    apply hf
    rw [map_mul, hfstar, hreal, map_one]
    exact mem_unitaryGroup_iff.mp hΛunitary
  have hAskew : Aᵀ = -A := by
    apply hf
    rw [hftranspose, hreal, map_neg, hreal]
    exact hΛskew
  obtain ⟨O, hO, hnormal⟩ :=
    exists_orthogonal_congruence_interleavedSkewForm m A hA hAskew
  have hOc : f O ∈ unitaryGroup (Fin (2 * m)) ℂ := by
    rw [mem_unitaryGroup_iff]
    rw [← hfstar, ← map_mul, mem_orthogonalGroup_iff.mp hO, map_one]
  have hΛ : Λ = (f O)ᵀ * complexInterleavedSkewFormFin m * f O := by
    have h := congrArg f hnormal
    simpa only [map_mul, hftranspose, hreal] using h.symm
  refine ⟨f O * S, (unitaryGroup (Fin (2 * m)) ℂ).mul_mem hOc hS, ?_⟩
  rw [hfactor, hΛ, Matrix.transpose_mul]
  simp only [mul_assoc]

end Matrix
