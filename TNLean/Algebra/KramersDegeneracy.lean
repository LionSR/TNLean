/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Kramers degeneracy

Wolf, *Quantum Channels & Operations*, Chapter 3, states Kramers' theorem for a
Hermitian `H` commuting with an antiunitary `T` of square `-1`: every eigenvalue of
`H` is at least two-fold degenerate.  Wolf reduces the statement to matrices in the
same breath: writing `T = Γ V` with `Γ` complex conjugation and `V` unitary, the
commutation `[H, T] = 0` becomes `H Vᴴ = Vᴴ Hᵀ` and the condition `T² = -1` becomes
antisymmetry `Vᵀ = -V`.  This file formalizes Wolf's reduced matrix form, which is
what his printed proof actually manipulates.

Degeneracy is expressed as `2 ≤ Module.finrank ℂ (Module.End.eigenspace H.toLin' μ)`.
Wolf's proof exhibits two orthogonal eigenvectors for the same eigenvalue, so the
dimension of the eigenspace is the invariant his argument bounds; the geometric
multiplicity of a Hermitian matrix also agrees with the algebraic one, so nothing is
lost against the phrase "two-fold degenerate".

## Main declarations

* `Matrix.dotProduct_mulVec_self_eq_zero_of_transpose_eq_neg`: the quadratic form of an
  antisymmetric complex matrix vanishes identically.
* `Matrix.two_le_finrank_eigenspace_of_linearIndependent_pair`: two independent
  eigenvectors for one eigenvalue bound the eigenspace dimension below by two.
* `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antisymmetric_unitary`: Kramers'
  theorem in Wolf's matrix form.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 3, Kramers' theorem (§3, line 503 of
  `Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`).
-/

open scoped ComplexOrder Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The quadratic form of an antisymmetric complex matrix vanishes: if `Mᵀ = -M`, then
`x ⬝ᵥ M *ᵥ x = 0` for every vector `x`.  This is the mechanism behind the orthogonality
step of Kramers' theorem. -/
theorem dotProduct_mulVec_self_eq_zero_of_transpose_eq_neg {M : Matrix n n ℂ}
    (hM : Mᵀ = -M) (x : n → ℂ) : x ⬝ᵥ M *ᵥ x = 0 := by
  have hself : x ⬝ᵥ M *ᵥ x = -(x ⬝ᵥ M *ᵥ x) := by
    calc x ⬝ᵥ M *ᵥ x = x ᵥ* M ⬝ᵥ x := Matrix.dotProduct_mulVec x M x
      _ = Mᵀ *ᵥ x ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
      _ = (-M) *ᵥ x ⬝ᵥ x := by rw [hM]
      _ = -(M *ᵥ x ⬝ᵥ x) := by rw [Matrix.neg_mulVec, neg_dotProduct]
      _ = -(x ⬝ᵥ M *ᵥ x) := by rw [dotProduct_comm]
  have htwo : (2 : ℂ) * (x ⬝ᵥ M *ᵥ x) = 0 := by linear_combination hself
  simpa using htwo

/-- Two nonzero orthogonal vectors are linearly independent. -/
theorem linearIndependent_pair_of_dotProduct_star_eq_zero {u v : n → ℂ} (hu : u ≠ 0)
    (hv : v ≠ 0) (huv : star u ⬝ᵥ v = 0) : LinearIndependent ℂ ![u, v] := by
  rw [LinearIndependent.pair_iff' hu]
  intro a hav
  refine hv ?_
  have hself : star u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_star_self_eq_zero.mp h)
  have ha : a * (star u ⬝ᵥ u) = 0 := by
    have h : star u ⬝ᵥ (a • u) = 0 := by rw [hav]; exact huv
    rwa [dotProduct_smul, smul_eq_mul] at h
  rw [← hav, (mul_eq_zero.mp ha).resolve_right hself, zero_smul]

variable [DecidableEq n]

/-- Two linearly independent eigenvectors of `A` for the same eigenvalue `μ` force the
eigenspace of `μ` to have dimension at least two. -/
theorem two_le_finrank_eigenspace_of_linearIndependent_pair {A : Matrix n n ℂ} {μ : ℂ}
    {u v : n → ℂ} (hu : A *ᵥ u = μ • u) (hv : A *ᵥ v = μ • v)
    (hLI : LinearIndependent ℂ ![u, v]) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' A) μ) := by
  have hmem : ∀ i : Fin 2, ![u, v] i ∈ Module.End.eigenspace (Matrix.toLin' A) μ := by
    intro i
    fin_cases i <;> rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] <;>
      simpa using ‹_›
  have hLIsub : LinearIndependent ℂ fun i : Fin 2 => (⟨![u, v] i, hmem i⟩ :
      Module.End.eigenspace (Matrix.toLin' A) μ) :=
    LinearIndependent.of_comp (Module.End.eigenspace (Matrix.toLin' A) μ).subtype hLI
  simpa using hLIsub.fintype_card_le_finrank

end Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every eigenvalue of a Hermitian matrix is fixed by complex conjugation. -/
private theorem conj_eq_self_of_hasEigenvalue {H : Matrix n n ℂ} (hH : H.IsHermitian) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' H) μ) : (starRingEnd ℂ) μ = μ := by
  have hspec : μ ∈ spectrum ℂ H := by
    rw [← Matrix.spectrum_toLin']
    exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
  rw [hH.spectrum_eq_image_range] at hspec
  obtain ⟨r, -, rfl⟩ := hspec
  simp

/-- **Kramers' theorem** (Wolf, *Quantum Channels & Operations*, §3, line 503), in Wolf's own
matrix reduction of the antiunitary statement.

Wolf states the theorem for a Hermitian `H` and an antiunitary `T` with `[H, T] = 0` and
`T² = -1`, and immediately rewrites both hypotheses in matrix terms: with `T = Γ V` for `Γ`
complex conjugation and `V` unitary, commutation is `H Vᴴ = Vᴴ Hᵀ` and `T² = -1` is
antisymmetry `Vᵀ = -V`.  Those two matrix identities, together with `Vᴴ V = 1`, are the
hypotheses below, so the statement is Wolf's with the antiunitary rewritten exactly as he
rewrites it; no further hypothesis is imposed.

"At least two-fold degenerate" is `2 ≤ Module.finrank ℂ (Module.End.eigenspace H.toLin' μ)`:
Wolf's proof produces a second eigenvector orthogonal to the first, so the eigenspace
dimension is what the argument bounds.

The proof is Wolf's.  From `H ψ = μ ψ` the vector `φ = Vᴴ star ψ` satisfies
`H φ = Vᴴ Hᵀ star ψ = μ φ`; it is nonzero because `V` is unitary; and `⟨ψ, φ⟩ = 0` because
the quadratic form of the antisymmetric matrix `Vᴴ` vanishes. -/
theorem two_le_finrank_eigenspace_of_antisymmetric_unitary {H V : Matrix n n ℂ}
    (hH : H.IsHermitian) (hVunit : Vᴴ * V = 1) (hHV : H * Vᴴ = Vᴴ * Hᵀ) (hVanti : Vᵀ = -V)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' H) μ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) μ) := by
  obtain ⟨ψ, hψmem, hψne⟩ := hμ.exists_hasEigenvector
  have hψ : H *ᵥ ψ = μ • ψ := by
    have := Module.End.mem_eigenspace_iff.mp hψmem
    rwa [Matrix.toLin'_apply] at this
  -- Wolf's second eigenvector.
  set φ : n → ℂ := Vᴴ *ᵥ star ψ with hφdef
  have hconj : (starRingEnd ℂ) μ = μ := conj_eq_self_of_hasEigenvalue hH hμ
  have hHtrans : Hᵀ *ᵥ star ψ = μ • star ψ := by
    rw [Matrix.mulVec_transpose, ← hH.eq, ← Matrix.star_mulVec, hψ]
    ext i
    simp [Pi.star_apply, hconj]
  have hφ : H *ᵥ φ = μ • φ := by
    rw [hφdef, Matrix.mulVec_mulVec, hHV, ← Matrix.mulVec_mulVec, hHtrans,
      Matrix.mulVec_smul]
  have hφne : φ ≠ 0 := by
    intro hzero
    have hVVH : V * Vᴴ = 1 := mul_eq_one_comm.mp hVunit
    have : star ψ = 0 := by
      have := congrArg (fun w => V *ᵥ w) hzero
      rwa [hφdef, Matrix.mulVec_mulVec, hVVH, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact hψne (by simpa using congrArg star this)
  -- Wolf's orthogonality: `Vᴴ` is antisymmetric, so its quadratic form vanishes.
  have hVHanti : (Vᴴ)ᵀ = -Vᴴ := by
    ext i j
    have h : V j i = -V i j := by
      have hij : Vᵀ i j = (-V) i j := by rw [hVanti]
      simpa using hij
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.neg_apply, h]
  have horth : star ψ ⬝ᵥ φ = 0 :=
    Matrix.dotProduct_mulVec_self_eq_zero_of_transpose_eq_neg hVHanti (star ψ)
  exact Matrix.two_le_finrank_eigenspace_of_linearIndependent_pair hψ hφ
    (Matrix.linearIndependent_pair_of_dotProduct_star_eq_zero hψne hφne horth)

end Matrix.IsHermitian
