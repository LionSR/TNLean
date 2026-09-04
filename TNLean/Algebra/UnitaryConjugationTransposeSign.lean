/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryEntrywiseConjugation
import TNLean.Algebra.UnitaryKronecker

/-!
# A common transpose sign for the two conjugation factors

Applying the conjugation relation of a matrix product unitary twice leaves the
single Kronecker identity `conj(x) x ⊗ conj(y) y = 𝟙` between the two virtual unitaries `x`
and `y`. This file isolates the purely algebraic consequence drawn from that
identity in arXiv:1703.09188, `paper_v2.tex` lines 1033--1038: the identity is
equivalent to `x = e^{iφ} xᵀ` and `y = e^{-iφ} yᵀ`, and unitarity of `x` forces
`e^{iφ} = ±1`. The two factors therefore carry one common transpose sign: either
both are symmetric, or both are skew-symmetric.

The conjugation appearing in the source relation is entrywise complex
conjugation, `Matrix.map (starRingEnd ℂ)`, not the conjugate transpose.

## Main results

- `Matrix.exists_common_transpose_sign_of_kronecker_map_star_mul_eq_one`: the
  Kronecker identity produces one sign `σ = ±1` with `x = σ • xᵀ` and
  `y = σ • yᵀ`.
- `Matrix.transpose_eq_self_or_transpose_eq_neg_of_kronecker_map_star_mul_eq_one`:
  the same conclusion in the form "both symmetric or both skew-symmetric".

## References

* [J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix product
  unitaries: structure, symmetries, and topological invariants*,
  arXiv:1703.09188, lines 1033--1038][Cirac2017MPU]
-/

open scoped Kronecker

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
  [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty m] in
/-- For a unitary matrix, the transpose is a left inverse of the entrywise
conjugate. It permits multiplying `conj(x)x = e^{iφ}𝟙` on the left by `xᵀ` in
arXiv:1703.09188, `paper_v2.tex` lines 1035--1036. -/
theorem transpose_mul_map_star_of_mem_unitaryGroup {x : Matrix m m ℂ}
    (hx : x ∈ unitaryGroup m ℂ) : xᵀ * x.map (starRingEnd ℂ) = 1 := by
  have hstar : xᴴ * x = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hx
  have h := congrArg Matrix.transpose hstar
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h
  have hc : (xᴴ)ᵀ = x.map (starRingEnd ℂ) := by ext i j; simp
  rwa [hc] at h

omit [Nonempty m] in
/-- A unitary matrix whose entrywise conjugate times itself is a scalar matrix
equals that scalar times its own transpose. This is the passage from
`conj(x) x = e^{iφ}𝟙` to `x = e^{iφ} xᵀ` in arXiv:1703.09188, `paper_v2.tex`
lines 1035--1036. -/
theorem eq_smul_transpose_of_map_star_mul_eq_smul_one {x : Matrix m m ℂ}
    (hx : x ∈ unitaryGroup m ℂ) {c : ℂ} (hc : x.map (starRingEnd ℂ) * x = c • 1) :
    x = c • xᵀ := by
  calc x = xᵀ * x.map (starRingEnd ℂ) * x := by
        rw [transpose_mul_map_star_of_mem_unitaryGroup hx, Matrix.one_mul]
    _ = xᵀ * (x.map (starRingEnd ℂ) * x) := Matrix.mul_assoc _ _ _
    _ = xᵀ * (c • (1 : Matrix m m ℂ)) := by rw [hc]
    _ = c • xᵀ := by rw [Matrix.mul_smul, Matrix.mul_one]

/-- **Common transpose sign of the two conjugation factors.** If the entrywise
conjugation relations of two unitary matrices assemble into the Kronecker
identity `conj(x) x ⊗ conj(y) y = 𝟙`, then one sign `σ = ±1` satisfies `x = σ • xᵀ` and
`y = σ • yᵀ`.

This is the algebraic tail of the conjugation-symmetry proposition in
arXiv:1703.09188, `paper_v2.tex` lines 1033--1038: the Kronecker identity splits
into reciprocal scalars `e^{iφ}` and `e^{-iφ}`, and `𝟙 = xx† = e^{2iφ}𝟙` forces
`e^{iφ} = ±1`, so the two reciprocal scalars coincide. -/
theorem exists_common_transpose_sign_of_kronecker_map_star_mul_eq_one
    {x : Matrix m m ℂ} {y : Matrix n n ℂ} (hx : x ∈ unitaryGroup m ℂ)
    (hy : y ∈ unitaryGroup n ℂ)
    (h : (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) = 1) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ x = σ • xᵀ ∧ y = σ • yᵀ := by
  obtain ⟨c, -, hcx, hcy⟩ := exists_eq_smul_one_of_kronecker_eq_one h
  have hxbar : x.map (starRingEnd ℂ) ∈ unitaryGroup m ℂ :=
    map_star_mem_unitaryGroup_iff.mpr hx
  have hdouble : (x.map (starRingEnd ℂ)).map (starRingEnd ℂ) = x := by ext i j; simp
  have hself : x.map (starRingEnd ℂ) * (x.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      c • 1 := by rw [hdouble]; exact hcx
  have hsign : c = 1 ∨ c = -1 :=
    scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one
      (⟨x.map (starRingEnd ℂ), hxbar⟩ : unitaryGroup m ℂ) c hself
  have hcinv : c⁻¹ = c := by rcases hsign with hc | hc <;> rw [hc] <;> norm_num
  exact ⟨c, hsign, eq_smul_transpose_of_map_star_mul_eq_smul_one hx hcx,
    eq_smul_transpose_of_map_star_mul_eq_smul_one hy (by rwa [hcinv] at hcy)⟩

/-- **Both factors symmetric or both skew-symmetric.** The Kronecker identity
`conj(x) x ⊗ conj(y) y = 𝟙` between two unitary matrices leaves exactly two possibilities:
both matrices are symmetric, or both are skew-symmetric. This is the form of
arXiv:1703.09188, `paper_v2.tex` lines 1033--1038 used in the structural
discussion of symmetric and skew-symmetric unitaries that follows it. -/
theorem transpose_eq_self_or_transpose_eq_neg_of_kronecker_map_star_mul_eq_one
    {x : Matrix m m ℂ} {y : Matrix n n ℂ} (hx : x ∈ unitaryGroup m ℂ)
    (hy : y ∈ unitaryGroup n ℂ)
    (h : (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) = 1) :
    (xᵀ = x ∧ yᵀ = y) ∨ (xᵀ = -x ∧ yᵀ = -y) := by
  obtain ⟨σ, hσ, hxσ, hyσ⟩ :=
    exists_common_transpose_sign_of_kronecker_map_star_mul_eq_one hx hy h
  have hxT : xᵀ = σ • x := by simpa using congrArg Matrix.transpose hxσ
  have hyT : yᵀ = σ • y := by simpa using congrArg Matrix.transpose hyσ
  rcases hσ with hσ | hσ
  · subst hσ
    exact Or.inl ⟨by simpa using hxT, by simpa using hyT⟩
  · subst hσ
    exact Or.inr ⟨by simpa using hxT, by simpa using hyT⟩

end Matrix
