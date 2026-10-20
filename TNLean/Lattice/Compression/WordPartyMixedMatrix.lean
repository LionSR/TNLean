/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.WordPartyCoordinates
import TNLean.Lattice.Compression.PartyProductConjugation
/-!
# Mixed chronological products in party coordinates

The matrices of actual source-free words in the constructed party bases are
products of their literal restriction matrices. Thus a ket word, an input
operator word, and a bra word form the product of their local mixed matrices.
The input operator is the evaluation of a source-free word; its product
factorization follows from that word's actual singleton restrictions. The three
words may otherwise be arbitrary, and their local maps may vanish.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 409–434 and 565–588.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect.Word
variable {P : Type} [Fintype P] [DecidableEq P]
variable {I J : P → Type} [∀ p, Fintype (I p)] [∀ p, Fintype (J p)]

/-- The matrix of an actual source-free word is the product of its actual
restriction matrices. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 565–588. -/
theorem partyGroupedBasis_matrix_eval {a z : Layout P} (w : Word a z)
    (hs : w.sources = [])
    (b : ∀ p, OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (c : ∀ p, OrthonormalBasis (J p) ℂ (Mem (Layout.atParty p z)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    Matrix.of (fun x y ↦ (partyGroupedBasis z c ps hn hc).repr
      (w.eval (partyGroupedBasis a b ps hn hc y)) x) =
      dependentPhysicalProductFamilyMatrix (fun p ↦ Matrix.of (fun x y ↦
        (c p).repr ((w.restrict (partySelector p) hs).eval
          (b p y)) x)) := by
  classical
  ext x y
  exact partyGroupedBasis_repr_eval w hs b c ps hn hc x y

/-- A literal mixed chronological matrix product factors into its local
mixed products in the constructed party bases. No factorization is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434
and 565–588. -/
theorem partyGroupedBasis_mixed_matrix {a z : Layout P}
    (w v : Word a z) (u : Word a a)
    (hw : w.sources = []) (hv : v.sources = []) (hu : u.sources = [])
    (b : ∀ p, OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (c : ∀ p, OrthonormalBasis (J p) ℂ (Mem (Layout.atParty p z)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    Matrix.of (fun x y ↦ (partyGroupedBasis z c ps hn hc).repr
        (w.eval (partyGroupedBasis a b ps hn hc y)) x) *
      Matrix.of (fun x y ↦ (partyGroupedBasis a b ps hn hc).repr
        (u.eval (partyGroupedBasis a b ps hn hc y)) x) *
      (Matrix.of (fun x y ↦ (partyGroupedBasis z c ps hn hc).repr
        (v.eval (partyGroupedBasis a b ps hn hc y)) x))ᴴ =
      dependentPhysicalProductFamilyMatrix (fun p ↦
        Matrix.of (fun x y ↦ (c p).repr
            ((w.restrict (partySelector p) hw).eval (b p y)) x) *
          Matrix.of (fun x y ↦ (b p).repr
            ((u.restrict (partySelector p) hu).eval (b p y)) x) *
          (Matrix.of (fun x y ↦ (c p).repr
            ((v.restrict (partySelector p) hv).eval (b p y)) x))ᴴ) := by
  classical
  rw [partyGroupedBasis_matrix_eval w hw b c ps hn hc,
    partyGroupedBasis_matrix_eval u hu b b ps hn hc,
    partyGroupedBasis_matrix_eval v hv b c ps hn hc, partyProductMatrix_conjugate]

end TNLean.PEPS.PairEffect.Word
