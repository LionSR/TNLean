/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Pre-bialgebra comultiplications

A `PreBialgebra R A` structure on an `R`-algebra `A` is a comultiplication
`Δ : A → A ⊗[R] A` that is coassociative and multiplicative, `Δ(xy) = Δ(x) Δ(y)`, but need
not be unital: `Δ(1)` need not be `1 ⊗ 1`, and multiplicativity only makes it an idempotent.

**Scope restriction (no counit):** Molnár et al., arXiv:2204.05940, `mpo.tex`, Definition 4.1
(lines 1409--1414), define a pre-bialgebra as an algebra that is also a coalgebra with
multiplicative coproduct, and a coalgebra (Definition 3.1, lines 866--875) is a
finite-dimensional complex vector space with a coassociative coproduct `Δ` and a counit `ε`
satisfying `(ε ⊗ id) ∘ Δ = (id ⊗ ε) ∘ Δ = id`.  No compatibility of the counit with the unit
or the product is imposed (line 1407), and `Δ(1) ≠ 1 ⊗ 1` is allowed (lines 1421 and 1708,
equation `eq:delta_epsilon`).  This class records only the multiplicative coassociative
coproduct: the counit is not part of the structure.  It is therefore strictly weaker than the
source's definition; for instance, the zero comultiplication on a nonzero ring `R` satisfies
its axioms but admits no counit.  Documented in
`docs/paper-gaps/mrgscp22_pre_bialgebra_counit_scope.tex`.

Mathlib's `Bialgebra` requires a counit that is an algebra homomorphism and `Δ(1) = 1 ⊗ 1`;
the second condition fails for the fusion coproduct of a family of matrix product operators.
Every bialgebra carries a `PreBialgebra` structure (`Bialgebra.toPreBialgebra`).

## Main definitions

* `PreBialgebra R A`: a coassociative comultiplication `A →ₙₐ[R] A ⊗[R] A`.

## References

* Molnár, Ruiz-de-Alarcón, Garre-Rubio, Schuch, Cirac, Pérez-García, arXiv:2204.05940,
  `mpo.tex`, Definition 3.1 (coalgebra, lines 866--875), Definition 4.1 (pre-bialgebra,
  lines 1409--1414), and lines 1415--1421 and 1708.
* arXiv:2509.03600, section "MPO representations of bialgebras".
-/

open TensorProduct

universe u v

/-- A **pre-bialgebra** structure on an `R`-algebra `A`: a comultiplication which is a
non-unital algebra homomorphism `A →ₙₐ[R] A ⊗[R] A` and is coassociative,
`(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` after reassociating the triple tensor product.

No counit is part of the structure, and `Δ 1 = 1` is not required.  These are the
coproduct axioms of a pre-bialgebra in arXiv:2204.05940, `mpo.tex`, Definition 4.1
(lines 1409--1414) and Definition 3.1 (lines 866--875); the counit of Definition 3.1 is not
included, as recorded in the module docstring. -/
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
