import TNLean.Algebra.SkolemNoether
import TNLean.PEPS.Defs

/-!
# Edge gauge extraction from insertion algebra isomorphisms

This file records the finite-dimensional algebra step in the injective PEPS
Fundamental Theorem. Once the edge-blocked three-site argument gives an algebra
isomorphism between the full matrix algebras of insertions on a chosen edge,
Skolem--Noether turns that isomorphism into conjugation by an invertible edge
matrix.
-/

open scoped Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The edge matrix-algebra isomorphism determines the bond dimension on that
edge and is realized as conjugation by an invertible edge matrix.

Source: arXiv:1804.04964, Section 3, lines 560--586. After the three-site
injective-chain argument constructs the algebra isomorphism $\varphi : X \mapsto Y$
between edge insertions, the source proves that it is an isomorphism between
full matrix algebras. It then concludes that the two matrix sizes agree and
writes $Y = Z_e X Z_e^{-1}$ for an invertible edge matrix $Z_e$. -/
theorem edgeGaugeFromInsertionAlgebraIsomorphism (A B : Tensor G d) (e : Edge G)
    (φ : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :
    ∃ hEdge : A.bondDim e = B.bondDim e,
      ∃ Z : GL (Fin (B.bondDim e)) ℂ,
        ∀ X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
          φ X = (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) X *
              ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :=
  MPSTensor.matrixAlgEquiv_inner_of_fin φ

end PEPS
end TNLean
