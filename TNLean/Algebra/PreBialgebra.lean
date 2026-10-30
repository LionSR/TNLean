/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Pre-bialgebras

A pre-bialgebra over a commutative semiring `R` is an `R`-algebra `A` with a comultiplication
`Δ : A → A ⊗[R] A` that is coassociative and multiplicative,
`Δ(xy) = Δ(x) Δ(y)`, but need not be unital: `Δ(1)` need not be `1 ⊗ 1`, and
multiplicativity only makes it an idempotent.  This is the comultiplication part of the
pre-bialgebra axioms of Molnár et al., arXiv:2204.05940, `mpo.tex`, lines 1409--1419, where
`Δ(1) ≠ 1 ⊗ 1` is allowed (line 1708, equation `eq:delta_epsilon`).

Mathlib's `Coalgebra` and `Bialgebra` require a counit and `Δ(1) = 1 ⊗ 1`, which fail for the
fusion coproduct of a family of matrix product operators.  This class records only the
comultiplication: no counit is included.  Every bialgebra is a pre-bialgebra
(`Bialgebra.toPreBialgebra`).

## Main definitions

* `PreBialgebra R A`: a coassociative comultiplication `A →ₙₐ[R] A ⊗[R] A`.

## References

* Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, arXiv:2204.05940, `mpo.tex`,
  lines 866--875 (coassociativity), 1409--1419 (pre-bialgebra), 1708.
* arXiv:2509.03600, section "MPO representations of bialgebras".
-/

open TensorProduct

universe u v

/-- A **pre-bialgebra** structure on an `R`-algebra `A`: a comultiplication which is a
non-unital algebra homomorphism `A →ₙₐ[R] A ⊗[R] A` and is coassociative,
`(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` after reassociating the triple tensor product.

No counit is part of the structure, and `Δ 1 = 1` is not required.  Source:
arXiv:2204.05940, `mpo.tex`, lines 866--875 and 1409--1419. -/
class PreBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] where
  /-- The comultiplication, multiplicative but not necessarily unital. -/
  comul : A →ₙₐ[R] A ⊗[R] A
  /-- The comultiplication is coassociative. -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A).rTensor A ∘ₗ
      (comul : A →ₗ[R] A ⊗[R] A) =
    (comul : A →ₗ[R] A ⊗[R] A).lTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)

namespace PreBialgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
  [PreBialgebra R A]

theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A
        (((comul : A →ₙₐ[R] A ⊗[R] A) : A →ₗ[R] A ⊗[R] A).rTensor A (comul a)) =
      ((comul : A →ₙₐ[R] A ⊗[R] A) : A →ₗ[R] A ⊗[R] A).lTensor A (comul a) :=
  LinearMap.congr_fun coassoc a

theorem comul_mul (a b : A) :
    (comul (R := R) (a * b) : A ⊗[R] A) = comul a * comul b :=
  map_mul _ a b

end PreBialgebra

/-- Every bialgebra is a pre-bialgebra, by forgetting the counit and the unitality of the
comultiplication. -/
instance Bialgebra.toPreBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Bialgebra R A] : PreBialgebra R A where
  comul := (Bialgebra.comulAlgHom R A).toNonUnitalAlgHom
  coassoc := Coalgebra.coassoc

/-- The pre-bialgebra comultiplication of a bialgebra is its coalgebra comultiplication. -/
@[simp]
theorem Bialgebra.preBialgebra_comul_apply {R : Type u} {A : Type v} [CommSemiring R]
    [Semiring A] [Bialgebra R A] (a : A) :
    PreBialgebra.comul (R := R) a = Coalgebra.comul (R := R) a :=
  rfl
