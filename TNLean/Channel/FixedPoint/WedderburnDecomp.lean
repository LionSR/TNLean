/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Artinian.Module

/-!
# Wedderburn decomposition of fixed-point `*`-subalgebra (Wolf Theorem 6.14)

This file states the Wedderburn--Artin decomposition for the fixed-point
`*`-subalgebra established in `TNLean.Channel.FixedPoint.Algebra`.

Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` decomposes as a direct sum
of full matrix algebras (over ℂ, since ℂ is algebraically closed). Concretely,
Wolf Eq. (1.39) gives the embedding

    B = U (0 ⊕ ⊕_k M_{d_k} ⊗ 1_{m_k}) U†

inside the ambient matrix algebra, for some unitary `U` and a Hilbert space
decomposition `ℂ^D = ℂ^{d₀} ⊕ ⊕_k ℂ^{d_k} ⊗ ℂ^{m_k}`.

## Main results

* `Kraus.fixedPointAlgebra_isSemisimpleRing`: the carrier type of the
  adjoint-fixed-point `StarSubalgebra` is a semisimple ring. (sorry — requires
  showing that `*`-subalgebras over ℂ have trivial Jacobson radical.)
* `Kraus.fixedPointAlgebra_wedderburnArtin`: there exist `n : ℕ` and
  `dims : Fin n → ℕ` such that the fixed-point algebra is algebra-isomorphic
  to `Π i, Matrix (Fin (dims i)) (Fin (dims i)) ℂ`.

## Strategy and gaps

The proof chain is:
1. `StarSubalgebra ℂ Mat` is finite-dimensional (subalgebra of `M_D(ℂ)`).
2. Finite-dimensional ⟹ `IsArtinianRing` — available in Mathlib.
3. `*`-subalgebra over ℂ ⟹ `IsSemisimpleRing` — **Gap 1** (need to show
   the Jacobson radical vanishes for `*`-algebras over ℂ).
4. `IsSemisimpleRing` + `FiniteDimensional ℂ` + `IsAlgClosed ℂ` ⟹
   Wedderburn--Artin decomposition — available in Mathlib via
   `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`.

The concrete unitary block-diagonal embedding (Wolf Eq. 1.39) and the
conditional expectation form with density operators ρ_k (Wolf Eq. 1.40)
require additional representation-theoretic infrastructure and are deferred
to future work.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 6.14, §6.4]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Eq. 1.39–1.40, §1]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Abstract Wedderburn--Artin decomposition -/

section AbstractDecomp

variable (K : Fin d → Mat) (h_tp : IsTP K)
  {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)

/-- The carrier type of the adjoint-fixed-point `StarSubalgebra` is a
finite-dimensional ℂ-algebra, being a subalgebra of `M_D(ℂ)`.

This is a type alias for the subtype
`↥(adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix)`. -/
abbrev FixedPointAlgebra :=
  ↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)

-- TODO: Gap 1 — Prove that `*`-subalgebras of `M_D(ℂ)` are semisimple.
--
-- Mathematical argument: In a `*`-algebra over ℂ, the Jacobson radical is
-- zero. This follows because:
-- (a) For an Artinian ring, J(R) is nilpotent.
-- (b) J(R) is a `*`-ideal in a `*`-algebra (since the Jacobson radical is
--     the intersection of maximal left ideals, and the star-involution
--     exchanges left and right ideals).
-- (c) Every nilpotent self-adjoint element in a `*`-subalgebra of `M_D(ℂ)`
--     is zero (since `x^n = 0` and `x = x*` implies `tr(x^*x) = 0`
--     implies `x = 0` over ℂ).
-- (d) Therefore J(R) = 0, and by the Artinian characterization,
--     `IsSemisimpleRing R`.
--
-- The Mathlib route: `isSemisimpleRing_iff_jacobson` (for Artinian rings,
-- semisimplicity ⟺ Jacobson radical = ⊥). This works for noncommutative
-- rings.

/-- The adjoint-fixed-point `*`-subalgebra is a semisimple ring.

This is the key algebraic input for the Wedderburn--Artin decomposition.
The proof requires showing that the Jacobson radical of a finite-dimensional
`*`-subalgebra of `M_D(ℂ)` is trivial.

Note: This is stated as a `theorem` rather than an `instance` because the
proof is currently sorry'd. Registering a sorry'd instance would pollute
typeclass synthesis. Once proved, this should be promoted to an `instance`. -/
theorem fixedPointAlgebra_isSemisimpleRing
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    IsSemisimpleRing
      (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)) :=
  sorry

/-- **Abstract Wedderburn--Artin decomposition** of the fixed-point algebra.

There exist `n : ℕ` and dimensions `dims : Fin n → ℕ` such that the
adjoint-fixed-point `*`-subalgebra is ℂ-algebra isomorphic to
`Π i, Matrix (Fin (dims i)) (Fin (dims i)) ℂ`.

This follows from `fixedPointAlgebra_isSemisimpleRing` and the Mathlib
theorem `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`. -/
-- TODO: Once `fixedPointAlgebra_isSemisimpleRing` is proved, apply
-- `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`.
-- The carrier type is finite-dimensional over ℂ as a subalgebra of M_D(ℂ).
theorem fixedPointAlgebra_wedderburnArtin
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    ∃ (n : ℕ) (dims : Fin n → ℕ),
      (∀ i, NeZero (dims i)) ∧
        Nonempty
          (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix) ≃ₐ[ℂ]
            Π i : Fin n, Matrix (Fin (dims i)) (Fin (dims i)) ℂ) :=
  sorry

end AbstractDecomp

/-! ## Concrete block-diagonal embedding (Wolf Eq. 1.39) -/

section ConcreteDecomp

/-- Bundled data for a **Wedderburn block decomposition** of a `*`-subalgebra
of `M_D(ℂ)`: a number of blocks `n` and dimension pairs `(d_k, m_k)` intended
to witness that the algebra is unitarily conjugate to
`0 ⊕ ⊕_k M_{d_k} ⊗ 1_{m_k}`
inside the ambient matrix algebra.

This corresponds to Wolf Eq. (1.39). Since this declaration is a `structure`,
it stores decomposition data; the proposition asserting existence of such a
decomposition is `Nonempty (IsWedderburnBlockDecomp S)`.

The `algEquiv` field ties the decomposition to the subalgebra `S` by
providing a ℂ-algebra isomorphism between `↥S` and a product of matrix
algebras `Π i, M_{d_i}(ℂ)`.

**Status**: Partial formalization only. The full concrete embedding data
(such as the unitary intertwiner `U` and the multiplicities `m_k` in the
ambient embedding) are deferred to future work. -/
structure IsWedderburnBlockDecomp
    (S : StarSubalgebra ℂ Mat) where
  /-- Number of simple summands. -/
  numBlocks : ℕ
  /-- Dimension of each matrix block (the `d_k`). -/
  blockDim : Fin numBlocks → ℕ
  /-- Multiplicity of each block (the `m_k`). -/
  multDim : Fin numBlocks → ℕ
  /-- The blocks are nondegenerate. -/
  blockDim_pos : ∀ i, 0 < blockDim i
  /-- The multiplicities are nondegenerate. -/
  multDim_pos : ∀ i, 0 < multDim i
  /-- The total size of the matrix blocks does not exceed `D`
  (equivalently, there is some complementary dimension not recorded here). -/
  dim_le : ∑ i : Fin numBlocks, blockDim i * multDim i ≤ D
  /-- The subalgebra is ℂ-algebra isomorphic to the product of matrix blocks.
  This field ties the decomposition data to `S`. -/
  algEquiv : ↥S ≃ₐ[ℂ] Π i : Fin numBlocks,
    Matrix (Fin (blockDim i)) (Fin (blockDim i)) ℂ

-- TODO: The full structure should additionally include:
-- * A unitary `U : Mat` witnessing the conjugation
-- * A proof that `S.carrier` equals the image of the block-diagonal embedding
--   under conjugation by `U`
-- * Compatibility with the star structure
--
-- This requires:
-- (1) Central projection decomposition of a semisimple algebra
-- (2) Spectral theorem on the center to extract orthogonal projections
-- (3) Construction of the unitary intertwiner U

-- TODO: This theorem is a general fact about arbitrary `StarSubalgebra ℂ Mat`,
-- not specific to quantum channels or fixed-point algebras. It should
-- eventually be moved to `TNLean/Algebra/WedderburnArtin.lean` or similar.

/-- Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` admits a Wedderburn
block decomposition (Wolf Eq. 1.39).

**Status**: sorry — requires bridging abstract Wedderburn--Artin to concrete
block-diagonal embedding. See `fixedPointAlgebra_wedderburnArtin` for the
abstract version. -/
theorem starSubalgebra_hasWedderburnBlockDecomp
    (S : StarSubalgebra ℂ Mat) :
    Nonempty (IsWedderburnBlockDecomp S) :=
  sorry

/-- **Wolf Theorem 6.14** (Heisenberg picture, abstract form).

The adjoint-fixed-point `*`-subalgebra `Fix(T*) = {X | T*(X) = X}` admits a
Wedderburn block decomposition.

Combined with `fixedPointAlgebra_wedderburnArtin`, this gives:
`Fix(T*) ≅ ⊕_k M_{d_k}(ℂ)` (abstract) and `Fix(T*) = U(⊕_k M_{d_k} ⊗ 1_{m_k})U†`
(concrete).

**Status**: sorry — follows from `starSubalgebra_hasWedderburnBlockDecomp`. -/
theorem adjointFixedPoints_wedderburnDecomp
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    Nonempty
      (IsWedderburnBlockDecomp
        (adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)) :=
  starSubalgebra_hasWedderburnBlockDecomp _

end ConcreteDecomp

/-! ## Dimension constraints -/

section DimConstraints

/-- In any Wedderburn block decomposition of the fixed-point algebra, the
weighted sum of block dimensions and multiplicities is at most `D`.

Concretely, if the decomposition has simple summands `M_{d_k}(ℂ)` with
multiplicities `m_k`, then the parameters satisfy `Σ_k d_k * m_k ≤ D`. This
is exactly the ambient-dimension constraint recorded in
`IsWedderburnBlockDecomp.dim_le`.

This is a convenience accessor for `IsWedderburnBlockDecomp.dim_le`. -/
theorem wedderburnBlockDims_sum_le
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    ∀ (w : IsWedderburnBlockDecomp
        (adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)),
      ∑ i : Fin w.numBlocks, w.blockDim i * w.multDim i ≤ D :=
  fun w => w.dim_le

end DimConstraints

end Kraus
