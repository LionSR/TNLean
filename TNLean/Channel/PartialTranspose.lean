/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.MaximallyEntangled
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.PosDef

/-!
# Bipartite partial transpose and the PPT property

Wolf's Chapter 3, Example 3.1 introduces the **partial transpose** `ρ^{T₁}` of a
bipartite operator `ρ ∈ M_d ⊗ M_{d'}` and the associated **PPT (positive partial
transpose)** property `ρ^{T₁} ≥ 0`.  The partial transpose transposes the first
tensor factor while leaving the second untouched:

  `(ρ^{T₁})_{(i,k),(j,l)} = ρ_{(j,k),(i,l)}`.

This file formalizes the separability-free content of the PPT material of
Wolf eq. (3.16)--(3.17): the partial transpose itself, its basic algebraic
properties (involution, trace preservation, Hermiticity preservation), the
second-factor variant and its relation to the first-factor one through a global
transposition, the PPT property as a predicate, its equivalence between the two
factors, and the transposition witnesses `W = (A ⊗ B) F (A ⊗ B)†` of
Wolf eq. (3.16).

## Main definitions

* `Matrix.partialTransposeLeft` (`ρ^{T₁}`): transpose of the first tensor factor.
* `Matrix.partialTransposeRight` (`ρ^{T₂}`): transpose of the second tensor
  factor.
* `Matrix.IsPPT`: the property that the first-factor partial transpose is
  positive semidefinite.
* `Matrix.transpositionWitness`: Wolf's witness `W = (A ⊗ B) F (A ⊗ B)†`.

## Main results

* `Matrix.partialTransposeLeft_partialTransposeLeft`: the first-factor partial
  transpose is an involution.
* `Matrix.trace_partialTransposeLeft`: the partial transpose preserves the trace.
* `Matrix.IsHermitian.partialTransposeLeft`: the partial transpose of a Hermitian
  matrix is Hermitian.
* `Matrix.partialTransposeRight_eq_transpose_partialTransposeLeft`: the two
  partial transposes differ by a global transposition,
  `ρ^{T₂} = (ρ^{T₁})ᵀ`.
* `Matrix.isPPT_iff_partialTransposeRight_posSemidef`: the PPT property is
  equivalent to positivity of the second-factor partial transpose (Wolf's
  remark that `ρ^{T₁} ≥ 0 ↔ ρ^{T₂} ≥ 0`).
* `Matrix.transpositionWitness_isHermitian`: the transposition witnesses are
  Hermitian.

## Scope

The **PPT criterion** as an *entanglement* criterion — that a separable state
has positive partial transpose, so a negative partial transpose certifies
entanglement — needs a separable-state predicate, which is absent from the
development.  This file formalizes the partial-transpose object, the PPT
property, and the witnesses; the separability implication is not formalized.
The same missing foundation blocks the reduction-criterion entanglement
implication, recorded in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equations (3.16)--(3.17)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder Kronecker
open Matrix

namespace Matrix

variable {d d' : ℕ}

/-! ## The partial transpose -/

/-- **Partial transpose over the first factor** (`ρ^{T₁}`).  For a bipartite
matrix `ρ` on `Fin d × Fin d'`, this transposes the first tensor factor while
fixing the second:

  `(partialTransposeLeft ρ) (i, k) (j, l) = ρ (j, k) (i, l)`.

This is Wolf's `ρ^{T₁} = (θ ⊗ id)(ρ)`, where `θ` is matrix transposition. -/
def partialTransposeLeft (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ :=
  fun p q => ρ (q.1, p.2) (p.1, q.2)

/-- **Partial transpose over the second factor** (`ρ^{T₂}`).  For a bipartite
matrix `ρ` on `Fin d × Fin d'`, this transposes the second tensor factor while
fixing the first:

  `(partialTransposeRight ρ) (i, k) (j, l) = ρ (i, l) (j, k)`.

This is Wolf's `ρ^{T₂} = (id ⊗ θ)(ρ)`. -/
def partialTransposeRight (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ :=
  fun p q => ρ (p.1, q.2) (q.1, p.2)

theorem partialTransposeLeft_apply (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ)
    (p q : Fin d × Fin d') :
    partialTransposeLeft ρ p q = ρ (q.1, p.2) (p.1, q.2) := rfl

theorem partialTransposeRight_apply (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ)
    (p q : Fin d × Fin d') :
    partialTransposeRight ρ p q = ρ (p.1, q.2) (q.1, p.2) := rfl

/-! ### Involution -/

/-- The first-factor partial transpose is an involution: `(ρ^{T₁})^{T₁} = ρ`. -/
@[simp]
theorem partialTransposeLeft_partialTransposeLeft
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeLeft (partialTransposeLeft ρ) = ρ := by
  ext p q
  simp only [partialTransposeLeft_apply]

/-- The second-factor partial transpose is an involution: `(ρ^{T₂})^{T₂} = ρ`. -/
@[simp]
theorem partialTransposeRight_partialTransposeRight
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeRight (partialTransposeRight ρ) = ρ := by
  ext p q
  simp only [partialTransposeRight_apply]

/-! ### Action on Kronecker products -/

/-- **The first-factor partial transpose realizes `θ ⊗ id`.** On a Kronecker
product it transposes the first factor and fixes the second:
`(A ⊗ B)^{T₁} = Aᵀ ⊗ B`. -/
@[simp]
theorem partialTransposeLeft_kronecker (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d') (Fin d') ℂ) :
    partialTransposeLeft (A ⊗ₖ B) = Aᵀ ⊗ₖ B := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  simp only [partialTransposeLeft_apply, kronecker_apply, Matrix.transpose_apply]

/-- **The second-factor partial transpose realizes `id ⊗ θ`.** On a Kronecker
product it transposes the second factor and fixes the first:
`(A ⊗ B)^{T₂} = A ⊗ Bᵀ`. -/
@[simp]
theorem partialTransposeRight_kronecker (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d') (Fin d') ℂ) :
    partialTransposeRight (A ⊗ₖ B) = A ⊗ₖ Bᵀ := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  simp only [partialTransposeRight_apply, kronecker_apply, Matrix.transpose_apply]

/-! ### Relation to the full transpose -/

/-- Transposing the first factor and then the second equals the full transpose:
`(ρ^{T₁})^{T₂} = ρᵀ`.  Equivalently, the two partial transposes differ by a
global transposition. -/
theorem partialTransposeRight_partialTransposeLeft
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeRight (partialTransposeLeft ρ) = ρᵀ := by
  ext p q
  simp only [partialTransposeRight_apply, partialTransposeLeft_apply, Matrix.transpose_apply]

/-- **Wolf eq. (3.17), `ρ^{T₂}` form.** The two partial transposes differ by a
global transposition: `ρ^{T₂} = (ρ^{T₁})ᵀ`. -/
theorem partialTransposeRight_eq_transpose_partialTransposeLeft
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeRight ρ = (partialTransposeLeft ρ)ᵀ := by
  ext p q
  simp only [partialTransposeRight_apply, partialTransposeLeft_apply, Matrix.transpose_apply]

/-- The two partial transposes differ by a global transposition, `ρ^{T₁}` form:
`ρ^{T₁} = (ρ^{T₂})ᵀ`. -/
theorem partialTransposeLeft_eq_transpose_partialTransposeRight
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeLeft ρ = (partialTransposeRight ρ)ᵀ := by
  rw [partialTransposeRight_eq_transpose_partialTransposeLeft, Matrix.transpose_transpose]

/-! ### Trace preservation -/

/-- The first-factor partial transpose preserves the trace. -/
@[simp]
theorem trace_partialTransposeLeft (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (partialTransposeLeft ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTransposeLeft_apply]

/-- The second-factor partial transpose preserves the trace. -/
@[simp]
theorem trace_partialTransposeRight (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (partialTransposeRight ρ).trace = ρ.trace := by
  rw [partialTransposeRight_eq_transpose_partialTransposeLeft, Matrix.trace_transpose,
    trace_partialTransposeLeft]

/-! ### Hermiticity preservation -/

/-- The first-factor partial transpose of a Hermitian matrix is Hermitian. -/
theorem IsHermitian.partialTransposeLeft {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.IsHermitian) : (partialTransposeLeft ρ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  rw [partialTransposeLeft_apply, partialTransposeLeft_apply]
  exact hρ.apply (q.1, p.2) (p.1, q.2)

/-- The second-factor partial transpose of a Hermitian matrix is Hermitian. -/
theorem IsHermitian.partialTransposeRight {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.IsHermitian) : (partialTransposeRight ρ).IsHermitian := by
  rw [partialTransposeRight_eq_transpose_partialTransposeLeft]
  exact (hρ.partialTransposeLeft).transpose

/-! ## The PPT property -/

/-- **Positive partial transpose (PPT)**.  A bipartite matrix `ρ` has the PPT
property when its first-factor partial transpose is positive semidefinite.  This
is Wolf's separability criterion `(θ ⊗ id)(ρ) = ρ^{T₁} ≥ 0`. -/
def IsPPT (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) : Prop :=
  (partialTransposeLeft ρ).PosSemidef

/-- **Wolf's remark after eq. (3.17).** The PPT property is equivalent to
positivity of the second-factor partial transpose, since `ρ^{T₁}` and `ρ^{T₂}`
differ only by a global transposition, which preserves positive
semidefiniteness:

  `ρ^{T₁} ≥ 0 ↔ ρ^{T₂} ≥ 0`. -/
theorem isPPT_iff_partialTransposeRight_posSemidef
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    IsPPT ρ ↔ (partialTransposeRight ρ).PosSemidef := by
  rw [IsPPT, partialTransposeRight_eq_transpose_partialTransposeLeft,
    Matrix.posSemidef_transpose_iff]

/-! ## Basis independence of the PPT property (Wolf eq. (3.16)--(3.17)) -/

/-- **Local-conjugation law for the partial transpose (Wolf eq. (3.17)).**
Conjugating the first factor by `C` on the left and `G` on the right and then
taking the first-factor partial transpose equals taking the partial transpose
first and conjugating by the transposed factors in the opposite order:

  `((C ⊗ 1) ρ (G ⊗ 1))^{T₁} = (Gᵀ ⊗ 1) ρ^{T₁} (Cᵀ ⊗ 1)`.

The second tensor factor is untouched throughout. -/
theorem partialTransposeLeft_conj_kronecker_one
    (C G : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeLeft ((C ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * ρ *
        (G ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)))
      = (Gᵀ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * partialTransposeLeft ρ *
          (Cᵀ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  -- Expand both sides into double sums over the first tensor factor and match.
  simp only [partialTransposeLeft_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    kronecker_apply, Matrix.one_apply, Matrix.transpose_apply]
  -- Collapse the Kronecker deltas on the second factor.
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  -- Push the outer column factor inside each inner sum, then swap the two sums.
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **Wolf eq. (3.16)--(3.17), basis-change form.** Take the partial transpose of
`ρ` in a different local basis on the first factor: conjugate by `V` on the left
and `U` on the right inside, take the first-factor partial transpose, then
conjugate by `U` on the left and `V` on the right outside.  The result is the
original partial transpose conjugated by `(U Uᵀ) ⊗ 1` and `(Vᵀ V) ⊗ 1`:

  `(U ⊗ 1) [((V ⊗ 1) ρ (U ⊗ 1))^{T₁}] (V ⊗ 1) = ((U Uᵀ) ⊗ 1) ρ^{T₁} ((Vᵀ V) ⊗ 1)`.

Specializing `V = Uᴴ` for a unitary basis change gives Wolf eq. (3.17); there the
conjugating factors are unitaries, so the eigenvalues of `ρ^{T₁}` — and hence the
positivity of the partial transpose — do not depend on the local basis. -/
theorem partialTransposeLeft_basis_change
    (U V : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) *
        partialTransposeLeft ((V ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * ρ *
          (U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))) *
        (V ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))
      = ((U * Uᵀ) ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * partialTransposeLeft ρ *
          ((Vᵀ * V) ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) := by
  rw [partialTransposeLeft_conj_kronecker_one V U ρ]
  have hUU : (U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * (Uᵀ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))
      = (U * Uᵀ) ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hVV : (Vᵀ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * (V ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))
      = (Vᵀ * V) ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  -- Fully right-associate both products, merge the two outer Kronecker pairs.
  simp only [Matrix.mul_assoc]
  rw [hVV, ← Matrix.mul_assoc (U ⊗ₖ _) (Uᵀ ⊗ₖ _), hUU]

/-- **Wolf eq. (3.17).** Taking the partial transpose in the basis changed by a
unitary `U` on the first factor — conjugating by `Uᴴ` inside, then by `U`
outside — yields the original partial transpose conjugated by `(U Uᵀ) ⊗ 1`:

  `(U ⊗ 1) [((Uᴴ ⊗ 1) ρ (U ⊗ 1))^{T₁}] (Uᴴ ⊗ 1)
     = ((U Uᵀ) ⊗ 1) ρ^{T₁} ((U Uᵀ)ᴴ ⊗ 1)`.

The conjugating matrix `M = (U Uᵀ) ⊗ 1` is the same on both ends, so the partial
transpose in the new basis is a similarity transform of `ρ^{T₁}` by `M`. -/
theorem partialTransposeLeft_unitary_basis_change
    (U : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) *
        partialTransposeLeft ((Uᴴ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * ρ *
          (U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))) *
        (Uᴴ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))
      = ((U * Uᵀ) ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * partialTransposeLeft ρ *
          ((U * Uᵀ)ᴴ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) := by
  rw [partialTransposeLeft_basis_change U Uᴴ ρ, Matrix.conjTranspose_mul]
  rfl

/-- **Basis independence of the PPT property (Wolf eq. (3.17)).** If a bipartite
matrix `ρ` is PPT, then the partial transpose taken in the local basis changed by
a unitary `U` on the first factor is again positive semidefinite.  By
`partialTransposeLeft_unitary_basis_change` the new-basis partial transpose is the
similarity transform `((U Uᵀ) ⊗ 1) ρ^{T₁} ((U Uᵀ)ᴴ ⊗ 1)`, and conjugation by a
matrix preserves positive semidefiniteness, so the positivity of the partial
transpose does not depend on the local basis. -/
theorem isPPT_basis_change {U : Matrix (Fin d) (Fin d) ℂ}
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : IsPPT ρ) :
    ((U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) *
        partialTransposeLeft ((Uᴴ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ)) * ρ *
          (U ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))) *
        (Uᴴ ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))).PosSemidef := by
  rw [partialTransposeLeft_unitary_basis_change U ρ]
  have hM := hρ.mul_mul_conjTranspose_same ((U * Uᵀ) ⊗ₖ (1 : Matrix (Fin d') (Fin d') ℂ))
  rwa [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one] at hM

/-! ## Transposition witnesses (Wolf eq. (3.16)) -/

/-- **Wolf's transposition witness** `W = (A ⊗ B) F (A ⊗ B)†`, where `F` is the
SWAP operator on `ℂ^d ⊗ ℂ^d` and `A, B` are arbitrary `d × d` matrices.  These
are exactly the witnesses that correspond to the transposition map. -/
noncomputable def transpositionWitness (A B : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (A ⊗ₖ B) * Matrix.swapMatrix d * (A ⊗ₖ B)ᴴ

/-- The transposition witnesses are Hermitian, since `F† = F`. -/
theorem transpositionWitness_isHermitian (A B : Matrix (Fin d) (Fin d) ℂ) :
    (transpositionWitness A B).IsHermitian := by
  unfold transpositionWitness Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.swapMatrix_conjTranspose, Matrix.mul_assoc]

end Matrix
