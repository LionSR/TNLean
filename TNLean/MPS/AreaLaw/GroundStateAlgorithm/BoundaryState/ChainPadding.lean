/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Hamiltonian.ProductBasisPenalty
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates
import QICLean.Spectral.Gap.DoubledSystemGap
import QICLean.ManyBody.Sites.PlaceAlong

/-!
# Product-ancilla padding of a positive nearest-neighbour chain

The original terms are placed on the initial sites. Every new bond carries
one actual on-site penalty on its right site, vanishing at the specified
basis level: this is QICLean's padded interaction
`Φ.padded hi (fun _ ↦ ManyBody.siteBasisPenalty z)`, whose terms are positive contractions by
`ManyBody.BondInteraction.padded_term_nonneg` and `ManyBody.BondInteraction.padded_term_le_one`.
The interaction is chosen from the original terms and lengths,
without selecting a ground vector or energy. Here its Hamiltonian is written, for a chain of
positive length, as a sum over the appended sites, the sites outside the first `L`.

Source: product-ancilla accuracy reduction for the successive construction of
LVV13, arXiv:1307.5143v1, final induction, lines 652--678. This is an algebraic
physical reduction; it asserts no computational running time.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- For a chain of positive length, the padded Hamiltonian is the embedded original Hamiltonian
plus the actual sum of one on-site penalty for every appended site. LVV13, arXiv:1307.5143v1,
lines 652--678. -/
theorem hamiltonian_padded_siteBasisPenalty {L N q : ℕ} (hL : 1 ≤ L) (hi : L ≤ N) (z : Fin q)
    (Φ : ManyBody.BondInteraction L q) :
    (Φ.padded hi fun _ ↦ ManyBody.siteBasisPenalty z).hamiltonian =
      ManyBody.placeAlong (X := fun _ ↦ Fin q) (Fin.castLEEmb hi) Φ.hamiltonian +
      ∑ v : {v : Fin N // v ∉ leftBlock N L},
        ManyBody.placeAt (X := fun _ ↦ Fin q) v.1 (ManyBody.siteBasisPenalty z) := by
  classical
  rw [ManyBody.BondInteraction.hamiltonian_padded, max_eq_left hL]
  congr 1
  exact Finset.sum_subtype _ (fun v ↦ by simp [mem_leftBlock]) _

end TNLean.MPS.AreaLaw
