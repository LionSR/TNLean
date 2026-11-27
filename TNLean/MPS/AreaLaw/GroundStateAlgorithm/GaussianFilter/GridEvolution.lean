/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.GridHamiltonian
import QICLean.ManyBody.Sites.Lattice.ChainBlocks
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.Product.ProductVector
import QICLean.ManyBody.Entropy.Filter.Optimizer
import QICLean.ManyBody.Sites.Twirl
import QICLean.Analysis.Exponential.HermitianUnitaryPath
import QICLean.ManyBody.Sites.Placement.Basic
import Mathlib.Data.List.OfFn

/-!
# Exact evolution inside the explicit grid blocks

The within-block Hamiltonians have pairwise disjoint supports. Their exponential is
therefore the ordered product of their individual exponentials, each supported on its
actual block. No block propagator is supplied as additional data.

Source: Osborne, arXiv:quant-ph/0508031v2, Figures 1--2 and equations (2)--(3);
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open ManyBody (interval)

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q w : ℕ}

/-- The explicitly constructed block Hamiltonians commute pairwise.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem commute_chainGridBlockHamiltonian (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) :
    Pairwise fun j k : Fin (L / w + 1) ↦
      Commute (chainGridBlockHamiltonian hw Φ j) (chainGridBlockHamiltonian hw Φ k) := by
  intro j k hjk
  have hdisj := ManyBody.pairwise_disjoint_chainGridBlock L w
    (show j.val ≠ k.val from fun heq ↦ hjk (Fin.ext heq))
  exact ManyBody.commute_of_mem_supportedOperators_of_disjoint
      (chainGridBlockHamiltonian_mem_supported hw Φ j)
      (chainGridBlockHamiltonian_mem_supported hw Φ k) hdisj

/-- The retained Hamiltonian has an exact product of its actual block evolutions.
The support layout and each factor are constructed from the original interaction terms.
Osborne, arXiv:quant-ph/0508031v2, Figures 1--2 and equation (3). -/
theorem hermitianUnitaryPath_chainGridRetained_eq_prod (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) (t : ℝ) :
    hermitianUnitaryPath (chainGridRetainedHamiltonian hw Φ) t =
      (List.ofFn fun j ↦ hermitianUnitaryPath (chainGridBlockHamiltonian hw Φ j) t).prod :=
  Matrix.hermitianUnitaryPath_fin_sum_of_commute _ (commute_chainGridBlockHamiltonian hw Φ) t

/-- Every factor of the exact block evolution is supported on its own grid block.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem chainGridBlockEvolution_mem_supported [NeZero q] (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) (j : Fin (L / w + 1)) (t : ℝ) :
    hermitianUnitaryPath (chainGridBlockHamiltonian hw Φ j) t ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q)
        (ManyBody.chainGridBlock L w j.val : Finset (Fin L)) :=
  ManyBody.hermitianUnitaryPath_mem_supportedOperators
    (chainGridBlockHamiltonian_mem_supported hw Φ j) t

end TNLean.MPS.AreaLaw
