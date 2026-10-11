/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareAreaLawHamiltonian
import TNLean.PEPS.Approximation.SheetSwapCorrection
import TNLean.PEPS.Approximation.SheetSwapConjugateSupport
import TNLean.Circuit.SitewiseTensorSupport
import QICLean.Analysis.DoubledSystemGap

/-!
# The local interactions of the partially swapped doubled Hamiltonian

Take the Hermitian part of each original site and edge interaction, double
it, pair the two coordinates at every site, and conjugate by the actual
partial swap. Each resulting term acts on its original designated support
and has norm at most twice the original bound. The sum is exactly the
partially swapped doubled Hamiltonian, since the original total is Hermitian.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `00-introduction.tex`, `eq:model`, and
`02-information.tex`, lines 416–424 and 498–524, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.Approximation

/-- The actual local interaction family of the swapped doubled Hamiltonian.
Its term at each original support is the conjugated doubled Hermitian part;
unused admissible supports carry zero. Only the original total is required
to be Hermitian. No ground-state or gap hypothesis is needed.

Source: polynomial-PEPS `eq:model` and `02-information.tex`, lines 416–424,
where pairing the two replicas at each site preserves range one. -/
theorem SquareHamiltonian.exists_swapped_doubled_localHamiltonian
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J) (hJ : 0 ≤ J)
    (R : Finset (SquareLatticeVertex L L)) :
    let p := QuantumCircuit.sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
    let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
    let F := Matrix.reindex p p (EncodedFrame.sheetSwapOp q R)
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.operator)
    ∃ g : AreaLaw.LocalHamiltonian (AreaLaw.rectangularDomain L L) (q * q) 1 (2 * J),
      g.term = Function.extend (squareAreaLawSupport L)
        (fun i : SquareInteraction L =>
          Matrix.reindex e e
            (F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianTerm i)) * Fᴴ)) 0 ∧
      g.operator = Matrix.reindex e e (F * K * Fᴴ) := by
  classical
  intro p e F K
  let B (i : SquareInteraction L) :=
    F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianTerm i)) * Fᴴ
  done

end TNLean.PEPS.Approximation
