/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Pre-bialgebras

A `PreBialgebra R A` structure on an `R`-algebra `A` is a coalgebra structure on `A`, in the
sense of Mathlib's `Coalgebra` (a coassociative comultiplication `Δ` with a counit `ε`
satisfying `(ε ⊗ id) ∘ Δ = (id ⊗ ε) ∘ Δ = id`), whose comultiplication is multiplicative,
`Δ(xy) = Δ(x) Δ(y)`.  This is the pre-bialgebra of Molnár et al., arXiv:2204.05940, `mpo.tex`,
Definition 4.1 (lines 1409--1414), with the coalgebra of Definition 3.1 (lines 866--875).

No compatibility of the counit with the unit or the product is imposed (line 1407), and
`Δ(1)` need not be `1 ⊗ 1` (lines 1421 and 1708, equation `eq:delta_epsilon`); multiplicativity
only makes `Δ(1)` an idempotent.  Mathlib's `Bialgebra` requires both a multiplicative unital
counit and `Δ(1) = 1 ⊗ 1`; the second condition fails for the fusion coproduct of a family of
matrix product operators.  Every bialgebra is a pre-bialgebra (`Bialgebra.toPreBialgebra`).

The source works over `ℂ` with finite-dimensional spaces; the structure here is stated over any
commutative semiring.

## Main definitions

* `PreBialgebra R A`: a coalgebra structure on the algebra `A` with multiplicative
  comultiplication.

## References

* Molnár, Ruiz-de-Alarcón, Garre-Rubio, Schuch, Cirac, Pérez-García, arXiv:2204.05940,
  `mpo.tex`, Definition 3.1 (coalgebra, lines 866--875), Definition 4.1 (pre-bialgebra,
  lines 1409--1414), and lines 1415--1421 and 1708.
* arXiv:2509.03600, section "MPO representations of bialgebras".
-/

open TensorProduct

universe u v

/-- A **pre-bialgebra** structure on an `R`-algebra `A`: a coalgebra structure on `A`
(a coassociative comultiplication `Δ` with a counit `ε` satisfying the two counit laws) whose
comultiplication is multiplicative, `Δ(xy) = Δ(x) Δ(y)`.

Neither `Δ 1 = 1 ⊗ 1` nor any compatibility of `ε` with the unit or the product is required.

Source: arXiv:2204.05940, `mpo.tex`, Definition 4.1 (lines 1409--1414), with the coalgebra of
Definition 3.1 (lines 866--875). -/
class PreBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
    extends Coalgebra R A where
  /-- The comultiplication is multiplicative.

  Source: arXiv:2204.05940, `mpo.tex`, Definition 4.1 (lines 1409--1414). -/
  comul_mul : ∀ a b : A, comul (a * b) = comul a * comul b

/-- Every bialgebra is a pre-bialgebra, by forgetting that the counit is an algebra
homomorphism and that the comultiplication is unital. -/
instance Bialgebra.toPreBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Bialgebra R A] : PreBialgebra R A where
  toCoalgebra := inferInstance
  comul_mul := Bialgebra.comul_mul
