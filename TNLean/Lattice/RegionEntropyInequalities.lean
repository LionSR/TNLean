/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.RegionStrongSubadditivity
import QICLean.Entropy.MovementEtaRegional
import QICLean.Entropy.RegionEntropyInequalities

/-!
# Regional entropies for one-dimensional local spaces

Two facts about the regional entropies of a unit vector on a finite set `V` of sites, each of
local dimension `q`, that the inequalities of `QICLean.Entropy.RegionEntropyInequalities`
(subadditivity, the Araki–Lieb inequality, the dimension bound `S(A) ≤ |A| log q`, and the
statements on regions of zero entropy) do not contain. The statements use no geometry of `V`,
so the chain of `L` sites (`V = Fin L`) and the finite lattice domains (`V = Site Λ`) both
read them.

* The Hilbert-space dimension `q^{|D|}` of a region is at least one when `q ≥ 1`.
* For `q = 1` every region of a unit vector has zero entropy.

## Main results

* `one_le_supportDim_const`, `regionEntropy_eq_zero_of_localDimension_one`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), `part1_arealaw.tex`, Section 2
  (`sec:setting`), the reductions.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2 (`sec:prelim`), `01-preliminaries.tex`, line 116.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- The Hilbert-space dimension `q^{|D|}` of a region is at least one when `q ≥ 1`. -/
theorem one_le_supportDim_const (hq : 1 ≤ q) (D : Finset V) :
    1 ≤ Entropy.supportDim (fun _ : V ↦ q) D := by
  rw [Entropy.supportDim, Finset.prod_const]
  exact Nat.one_le_pow _ _ hq

/-- Every region of a unit vector on one-dimensional local spaces has zero entropy: the
regional state has trace one on a one-dimensional configuration space, so its rank is at
most one. Source: area-law preprint, `01-preliminaries.tex`, line 116. -/
theorem regionEntropy_eq_zero_of_localDimension_one
    {Ω : EuclideanSpace ℂ (V → Fin 1)} (hΩ : ‖Ω‖ = 1) (A : Finset V) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin 1) Ω A = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one (ManyBody.regionState_posSemidef A Ω)
    (ManyBody.trace_regionState_eq_one hΩ)
  exact (Matrix.rank_le_card_width _).trans_eq (by simp [ManyBody.RegionConfig])

end TNLean.Lattice
