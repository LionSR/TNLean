import TNLean.PEPS.EdgeMiddlePhysical
import TNLean.PEPS.IdentityInsertion
import TNLean.PEPS.InsertionRealization
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Edge-blocked insertion algebra for PEPS

This file records the matrix-algebra correspondence obtained from applying the
three-site injective-chain argument to a PEPS blocked around one edge.

The statement follows the proof of Lemma inj_isomorph in
Molnar--Schuch--Verstraete--Cirac, arXiv:1804.04964, Section 3, lines
254--582 of Papers/1804.04964/paper_normal.tex: physical realization of
virtual insertions and the converse physical-to-virtual recovery produce an
algebra isomorphism between the matrix algebras on the chosen bond.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The algebra-isomorphism property obtained by comparing matrix insertions on an
edge-blocked PEPS pair.

The existentially quantified algebra equivalence is the map $X \mapsto Y$
between the full matrix algebras on the chosen virtual bond. The coefficient
identity says that inserting $X$ in the first blocked PEPS has the same
coefficient as inserting the corresponding matrix in the second blocked PEPS.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, especially lines
279--282 and 571--582 of Papers/1804.04964/paper_normal.tex. -/
def IsEdgeBlockedInsertionAlgebraIsomorphism (A B : Tensor G d) (e : Edge G) : Prop :=
  ∃ Φ :
    Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
    ∀ (σ : V → Fin d) (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ X =
        edgeInsertedCoeff (G := G) B e σ (Φ X)

/-! ### Post-absorption inserted-edge comparison -/

/-- Post-absorption equality of all inserted-edge coefficients.

Source: arXiv:1804.04964, Section 3, `eq:inj_equal_edge`
(`Papers/1804.04964/paper_normal.tex:1037-1065`). After absorbing the edge
gauges into the modified second tensor family $\widetilde B$, for every edge
and every inserted matrix, the first PEPS and $\widetilde B$ give the same
edge-inserted coefficient. -/
structure PostAbsorptionEdgeInsertionEquality (A Btilde : Tensor G d) : Prop where
  /-- The absorbed tensor family has the same bond dimensions as the first PEPS. -/
  bondDim_eq : A.bondDim = Btilde.bondDim
  /-- The same inserted virtual matrix gives equal edge-inserted coefficients. -/
  edgeInsertedCoeff_eq :
    ∀ (e : Edge G) (σ : V → Fin d)
      (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ M =
        edgeInsertedCoeff (G := G) Btilde e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun bondDim_eq e)) M)

/-- **Edge-blocked insertion algebra isomorphism.**

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
Papers/1804.04964/paper_normal.tex.

After blocking a PEPS around an edge $e=(u,v)$, suppose both resulting
three-site chains are injective and the original PEPS states agree. Then
matrix insertions on the chosen bond of the first blocked chain correspond, by
an algebra isomorphism, to matrix insertions on the chosen bond of the second
blocked chain, and the corresponding inserted coefficients agree.

**Proof status:** This declaration states the source theorem. The available
components and remaining implications are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem isEdgeBlockedInsertionAlgebraIsomorphism
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B) :
    IsEdgeBlockedInsertionAlgebraIsomorphism (G := G) A B e := by
  -- This is the algebra-isomorphism step in arXiv:1804.04964, Section 3,
  -- Lemma inj_isomorph, lines 254--582. The proof combines the
  -- virtual-to-physical realization with the physical-to-virtual recovery
  -- $O_1,O_2 \mapsto W$, then uses injectivity to prove uniqueness,
  -- bijectivity, and multiplicativity of the resulting map $X \mapsto Y$.
  sorry

end PEPS
end TNLean
