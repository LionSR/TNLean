/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Exponential.ExpConjugation
import QICLean.ManyBody.Dynamics.BoundedDegreeImaginaryTime
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.Lattice.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Positivity
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Imaginary-time conjugation for nearest-neighbour Hamiltonians

For a sum of positive unit contractions supported on nearest-neighbour bonds,
a two-site observable satisfies `‖exp(tH) * O * exp(-tH)‖ ≤ 2 * ‖O‖` for
`0 ≤ t ≤ 1 / 8`. The estimate is unchanged by a scalar shift of `H`.

This is the bond case of `ManyBody.Interaction.norm_exp_conjugation_shift_le_two`, the
short-time form of Arad, Kuwahara and Landau, arXiv:1406.3898, Lemma `lem:Hadamard-bound`,
`low70.tex`, lines 795–880: every bond has two sites, and every site lies in at most two bonds.
-/

open ManyBody (interval mem_interval)

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Every site of the chain lies in at most two of the nearest-neighbour bonds of a set.
Supporting AKL14, arXiv:1406.3898, `low70.tex`, lines 400–445. -/
theorem card_filter_mem_bond_le_two {L : ℕ} (s : Finset (Fin (L - 1))) (x : Fin L) :
    (s.filter fun i ↦ x ∈ interval L i.val (i.val + 2)).card ≤ 2 := by
  classical
  apply (Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val)
    (t := {x.val - 1, x.val}) ?_ Fin.val_injective.injOn).trans Finset.card_le_two
  intro i hi
  have hx := mem_interval.mp (Finset.mem_filter.mp hi).2
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  omega

/-- Imaginary-time conjugation by an original nearest-neighbour regional sum
has a uniform short-time bound, also after an arbitrary scalar shift.
This supplies the local estimate in AKL14, arXiv:1406.3898, low70.tex,
lines 795–880. The generator is the original regional sum; no locality
property of a clipped Hamiltonian is required. -/
theorem norm_exp_conjugation_nearest_neighbour_shift_le_two {L q c : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i ∈ I, 0 ≤ Φ.term i) (h1 : ∀ i ∈ I, Φ.term i ≤ 1)
    (O : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hO : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) O (interval L c (c + 2)))
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.partialHamiltonian I
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * ‖O‖ := by
  classical
  intro H
  have hH : H = ∑ i ∈ I, (Φ.restrict (· ∈ I)).term i :=
    (ManyBody.Interaction.partialHamiltonian_restrict_of_forall fun _ hi ↦ hi).symm
  rw [hH]
  exact (Φ.restrict (· ∈ I)).norm_exp_conjugation_shift_le_two I (k := 2) (g := 2)
    (fun i ↦ by by_cases hi : i ∈ I <;> simp [hi, h0])
    (fun i ↦ by by_cases hi : i ∈ I <;> simp [hi, h1])
    (fun i ↦ by simpa using ManyBody.card_interval_le (L := L) i.val (i.val + 2))
    (card_filter_mem_bond_le_two I) hO
    (by simpa using ManyBody.card_interval_le (L := L) c (c + 2)) z ht0 (by push_cast; linarith)

end TNLean.MPS.AreaLaw
