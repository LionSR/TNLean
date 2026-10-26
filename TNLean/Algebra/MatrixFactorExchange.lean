/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OperatorBlock
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fintype.BigOperators

/-!
# Exchanging the middle factor of an operator decomposition

Let `a`, `b`, `c`, and `o` be configuration index types for the sites belonging
only to the old middle, only to the new middle, to both middles, and to neither
middle, respectively.
The coordinate exchange sends `((b, o), (a, c))` to `((a, o), (b, c))`.
Expanding the transferred coordinates in matrix units rewrites an old
exterior/middle Kronecker product as a sum of new exterior/middle products.

For a prescribed finite family of old middle matrices, the new middle family
is chosen before any exterior coefficient matrices. Its size is multiplied by
`card a ^ 2 * card b ^ 2`. The identities hold over any semiring and require
no finiteness or nonemptiness of the common middle and exterior index types.

This is the finite-dimensional coordinate algebra for changing the two cuts
in ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. Ordering of
physical sites and matrix product operator bond bounds are separate results.
-/

open scoped BigOperators Kronecker

namespace Matrix

/-- Regroup the old exterior and middle as the new exterior and middle.
Elementary coordinate identity used for the change of cuts in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
def middleFactorExchangeEquiv {a b c o : Type*} :
    ((b × o) × (a × c)) ≃ ((a × o) × (b × c)) where
  toFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  left_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

/-- A fixed old middle factor contributes its partial matrix entries on the
intersection, with a prescribed matrix unit on the newly retained sites.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
def exchangedMiddleFactor {R a b c : Type*} [Zero R] [One R] [Mul R]
    [DecidableEq b] (V : Matrix (a × c) (a × c) R)
    (a₀ a₁ : a) (b₀ b₁ : b) : Matrix (b × c) (b × c) R :=
  single b₀ b₁ (1 : R) ⊗ₖ operatorBlock V a₀ a₁

/-- Transfer the old-only and new-only coordinates by their standard matrix
units. The middle factors depend only on `V` and the four matrix-unit labels;
the old exterior operator `M` enters only the new exterior coefficients.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem reindex_kronecker_middleFactorExchange
    {R a b c o : Type*} [Semiring R] [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (M : Matrix (b × o) (b × o) R) (V : Matrix (a × c) (a × c) R) :
    (M ⊗ₖ V).reindex middleFactorExchangeEquiv middleFactorExchangeEquiv =
      ∑ a₀, ∑ a₁, ∑ b₀, ∑ b₁,
        (single a₀ a₁ (1 : R) ⊗ₖ operatorBlock M b₀ b₁) ⊗ₖ
          exchangedMiddleFactor V a₀ a₁ b₀ b₁ := by
  ext x y
  rcases x with ⟨⟨a₀, o₀⟩, ⟨b₀, c₀⟩⟩
  rcases y with ⟨⟨a₁, o₁⟩, ⟨b₁, c₁⟩⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, middleFactorExchangeEquiv,
    exchangedMiddleFactor, Matrix.kroneckerMap_apply, Matrix.operatorBlock,
    Matrix.sum_apply, Matrix.single_apply, ite_and, ite_mul, mul_ite, eq_comm]

/-- The prescribed new middle family is chosen from the old middle family
and standard matrix units, before any exterior coefficients are supplied.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
def exchangedMiddleFamily {R a b c ι : Type*}
    [Zero R] [One R] [Mul R] [DecidableEq b]
    (V : ι → Matrix (a × c) (a × c) R)
    (r : ι × (a × a) × (b × b)) : Matrix (b × c) (b × c) R :=
  exchangedMiddleFactor (V r.1) r.2.1.1 r.2.1.2 r.2.2.1 r.2.2.2

/-- One new family handles all exterior coefficient families. This exact
identity is the finite-dimensional change-of-cuts step of ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem reindex_sum_kronecker_middleFactorExchange
    {R a b c o ι : Type*} [Semiring R] [Fintype a] [Fintype b] [Fintype ι]
    [DecidableEq a] [DecidableEq b]
    (V : ι → Matrix (a × c) (a × c) R)
    (M : ι → Matrix (b × o) (b × o) R) :
    (∑ t, M t ⊗ₖ V t).reindex middleFactorExchangeEquiv middleFactorExchangeEquiv =
      ∑ r : ι × (a × a) × (b × b),
        (single r.2.1.1 r.2.1.2 (1 : R) ⊗ₖ
          operatorBlock (M r.1) r.2.2.1 r.2.2.2) ⊗ₖ exchangedMiddleFamily V r := by
  calc
    (∑ t, M t ⊗ₖ V t).reindex middleFactorExchangeEquiv middleFactorExchangeEquiv =
        ∑ t, (M t ⊗ₖ V t).reindex middleFactorExchangeEquiv middleFactorExchangeEquiv := by
      ext x y
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
    _ = _ := by
      simp_rw [reindex_kronecker_middleFactorExchange]
      simp only [Fintype.sum_prod_type, exchangedMiddleFamily]

/-- The change of middle coordinates multiplies the family size by the
squares of the two transferred configuration dimensions. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem card_exchangedMiddleFamily_index
    {a b ι : Type*} [Fintype a] [Fintype b] [Fintype ι] :
    Fintype.card (ι × (a × a) × (b × b)) =
      Fintype.card ι * Fintype.card a ^ 2 * Fintype.card b ^ 2 := by
  simp only [Fintype.card_prod, pow_two, Nat.mul_assoc]

end Matrix
