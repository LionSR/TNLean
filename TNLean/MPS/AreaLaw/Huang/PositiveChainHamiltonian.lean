/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridLocalization

/-!
# The original positive nearest-neighbor chain as a finite-range Hamiltonian

The original interaction on each adjacent pair is assigned to that exact range-one
support; every other support receives zero. This is the range-one chain interaction
`ManyBody.BondInteraction.toChainInteraction` of the bond terms. Its operator is exactly the
original interaction sum (`ManyBody.Interaction.hamiltonian_extend`), and for positive
contractions its terms are positive contractions (`ManyBody.Interaction.extend_term_nonneg`,
`ManyBody.Interaction.extend_term_le_one`, `ManyBody.Interaction.norm_extend_term_le`). This
file adds that a bond has two sites, so that the single-site terms vanish.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, the nearest-neighbor
Hamiltonian and local positive-contraction assumptions preceding the viable-set algorithm;
Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. This identification changes neither
the physical operator nor the spectral hypotheses used by the two constructions.
-/

open ManyBody (ChainSupport bondSupport mem_interval)

namespace TNLean.MPS.AreaLaw

/-- Every bond contains exactly two sites. This is the adjacent-pair support convention of
LVV13, `algo53.tex`, used in Huang, Section 5.4. -/
theorem card_bondSupport {L : ℕ} (i : Fin (L - 1)) : (bondSupport i).val.card = 2 := by
  let x : Fin L := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩
  let y : Fin L := ⟨i.val + 1, by omega⟩
  have hset : (bondSupport i).val = {x, y} := by
    ext v
    simp only [bondSupport, mem_interval, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, x, y]
    omega
  rw [hset, Finset.card_pair]
  exact fun h ↦ by have := congrArg Fin.val h; dsimp only [x, y] at this; omega

/-- All singleton terms of a bond interaction, read as a range-one chain interaction, are
zero. This preserves the original adjacent-pair model of LVV13, `algo53.tex`. -/
theorem _root_.ManyBody.BondInteraction.toChainInteraction_term_eq_zero_of_card_one {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q) (X : ChainSupport L 1) (hX : X.val.card = 1) :
    Φ.toChainInteraction.term X = 0 := by
  refine ManyBody.Interaction.extend_term_eq_zero fun i hi ↦ ?_
  have := card_bondSupport i
  rw [hi] at this
  omega

end TNLean.MPS.AreaLaw
