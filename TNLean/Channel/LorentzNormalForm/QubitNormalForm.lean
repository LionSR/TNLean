/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Basic

/-!
# Lorentz normal form: the qubit canonical-form predicates

This module collects the Pauli-basis definitions and the three canonical-form
predicates for qubit channels of Wolf Proposition 2.11
(`Notes/WolfNoteTexSource/ch02_representations.tex`, Section 2.3): the
diagonal, non-diagonal, and singular Lorentz normal forms.  The existence

theorem is pending; see
`docs/paper-gaps/wolf_prop2_11_lorentz_scalar_filtering_gap.tex`.

## Main definitions

* `Wolf.pauliMatrices` — the four Pauli matrices
* `Wolf.pauliTransferEntry` — Pauli-basis transfer matrix entry
* `Wolf.IsLorentzDiagonal` — diagonal Lorentz normal form (case 1)
* `Wolf.IsLorentzNonDiagonal` — non-diagonal Lorentz normal form (case 2)
* `Wolf.IsLorentzSingular` — singular Lorentz normal form (case 3)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

namespace Wolf

/-! ### Lorentz normal form for qubit channels (Wolf Proposition 2.11)

For `D = 2` (qubit channels), the doubly-stochastic normal form from
Proposition 2.9 is further simplified using the Lorentz group action on the
transfer matrix.  The result is a complete classification into three
canonical forms.

We work in the Pauli basis representation: let σ₀, …, σ₃ be the Pauli
matrices (σ₀ = 1, σ₁ = σₓ, σ₂ = σ_y, σ₃ = σ_z).  For a
Hermiticity-preserving TP qubit channel `T`, the Pauli-basis transfer
matrix
  `T̂_{ij} = (1/2) tr[σ_i T(σ_j)]`   (i, j ∈ {0,1,2,3})
has real entries and the block structure
  `T̂ = [1 0; v Δ]`
where `v ∈ ℝ³` and `Δ` is a 3×3 real matrix (the Bloch-ball affine map:
`x ↦ v + Δ x`).

After SL(2, ℂ) filtering (which acts on `T̂` as a Lorentz transformation
`L₂ T̂ L₁` with `L_i ∈ SO⁺(1,3)`), the transfer matrix can be brought to
one of three canonical forms (Wolf Proposition 2.11):

1. **Diagonal** (generic, full Kraus rank): `T̂` is diagonal —
   `v = 0` and `Δ = diag(λ₁, λ₂, λ₃)` with the CP condition
   `λ₁ + λ₂ ≤ 1 + λ₃`.  This is the doubly-stochastic case.

2. **Non-diagonal** (Kraus rank 3): `T̂` has
   `Δ = diag(x/√3, x/√3, 1/3)`, `v = (0, 0, 2/3)`, with
   `0 ≤ x ≤ 1`.

3. **Singular** (Kraus rank 2): `T̂` has `Δ = 0` and `v = (0, 0, 1)`;
   the channel maps every input to a single pure state. -/

section LorentzNormalFormQubit

/-- The four Pauli matrices as 2×2 complex matrices, indexed by `Fin 4`:
`σ₀ = [[1,0],[0,1]]`, `σ₁ = [[0,1],[1,0]]`, `σ₂ = [[0,-I],[I,0]]`,
`σ₃ = [[1,0],[0,-1]]`. -/

def pauliMatrices : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- The entry `(i,j)` of the **Pauli-basis transfer matrix** of a linear map
`T : M₂(ℂ) → M₂(ℂ)`:
  `T̂_{ij} = (1/2) tr[σ_i T(σ_j)]`.

This is the `4×4` matrix representing `T` in the Pauli basis
`{σ₀/√2, σ₁/√2, σ₂/√2, σ₃/√2}`, so that `T̂` has real entries for
Hermiticity-preserving `T`. -/

noncomputable def pauliTransferEntry
    (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 4) : ℂ :=
  ((1 : ℂ) / 2) * Matrix.trace (pauliMatrices i * T (pauliMatrices j))

/-- A Hermiticity-preserving TP qubit channel `T'` is in **diagonal Lorentz normal
form** (Wolf Proposition 2.11, case 1) if its Pauli-basis transfer matrix is diagonal:
`T'(1) = 1` (unital) and all off-diagonal entries of `T̂` vanish
(i.e., `v = 0` and `Δ = diag(λ₁, λ₂, λ₃)`).

Furthermore, the singular values satisfy the complete-positivity condition
`λ₁ + λ₂ ≤ 1 + λ₃` (not checked here; future refinement). -/

def IsLorentzDiagonal
    (T' : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsChannel T' ∧ T' 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    ∀ (i j : Fin 4), i ≠ j → pauliTransferEntry T' i j = 0

/-- A Hermiticity-preserving TP qubit channel `T'` is in **non-diagonal Lorentz
normal form** (Wolf Proposition 2.11, case 2) if its Pauli-basis transfer matrix has
`Δ = diag(x/√3, x/√3, 1/3)` and `v = (0, 0, 2/3)` for some `x ∈ [0, 1]`.

The channel condition supplies the trace-preserving first row. The predicate
records the non-trivial translation entry, the three diagonal entries, and the
vanishing of all off-diagonal entries except the allowed translation. -/

def IsLorentzNonDiagonal
    (T' : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsChannel T' ∧
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧
      pauliTransferEntry T' 3 0 = (2/3 : ℂ) ∧
      pauliTransferEntry T' 1 1 = ((x / Real.sqrt 3 : ℝ) : ℂ) ∧
      pauliTransferEntry T' 2 2 = ((x / Real.sqrt 3 : ℝ) : ℂ) ∧
      pauliTransferEntry T' 3 3 = (1/3 : ℂ) ∧
      ∀ (i j : Fin 4), i ≠ j → (i, j) ≠ ((3 : Fin 4), (0 : Fin 4)) →
        pauliTransferEntry T' i j = 0

/-- A Hermiticity-preserving TP qubit channel `T'` is in **singular Lorentz normal
form** (Wolf Proposition 2.11, case 3) if its Pauli-basis transfer matrix has
`Δ = 0` and `v = (0, 0, 1)`.  That is, only `T̂_{00} = 1` and
`T̂_{30} = 1` are nonzero; the channel maps every input to the pure state
`(1 + σ_z)/2`. -/

def IsLorentzSingular
    (T' : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsChannel T' ∧
    pauliTransferEntry T' 3 0 = 1 ∧
    ∀ (i j : Fin 4), (i, j) ≠ (0, 0) ∧ (i, j) ≠ (3, 0) → pauliTransferEntry T' i j = 0

/- **Pending: Lorentz normal form for qubit channels (Wolf Proposition 2.11).**

Wolf's theorem says that every qubit channel can be brought to one of the three
Lorentz normal forms above by invertible completely positive maps of Kraus rank
one. These filtering maps come from general invertible matrices and therefore
include scalar freedom; they are not, in general, `SLFiltering`s with determinant
one.

A former declaration in this file incorrectly restricted both filters to
`SLFiltering 2` while also requiring the filtered map to remain a normalized
channel. That statement is false: determinant-one filters cannot supply the
scalar normalization required for all channels, so the declaration was removed.
The correctly formulated theorem remains to be formalized. Its proof will need:
- A type for general invertible Kraus-rank-one CP filters, including scalar freedom;
- The compactness and minimization results above, with the required normalization;
- The Lorentz group classification of the filtering orbits;
- The complete-positivity condition `λ₁ + λ₂ ≤ 1 + λ₃`.

See Wolf Section 2.3 for the complete proof. -/

end LorentzNormalFormQubit

/-
## Connection to transfer-matrix normal forms (Wolf Section 2.3)

The results above are stated at the level of CP maps.  The corresponding
transfer-matrix formulation (Propositions 2.7-2.8 in the blueprint / TransferMatrix.lean)
is obtained by applying `transferMatrix` to both sides.  The SVD normal form
(`Matrix.svd_of_isUnit`, `transferMatrix_svd_of_isUnit`) provides the
algebraic engine: after SL-filterings, the transfer matrix of the doubly-stochastic
map admits an SVD, which for D = 2 yields the Lorentz normal form decomposition.
-/


end Wolf
