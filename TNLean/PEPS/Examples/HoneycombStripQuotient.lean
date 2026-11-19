import TNLean.PEPS.Examples.HoneycombStripInjectivity
import TNLean.PEPS.RegionBlock.PartitionContraction
import Mathlib.Algebra.BigOperators.Fin

/-! # The partition quotient tensor for staggered honeycomb cells -/

open TNLean.PEPS
open TNLean.PEPS.PartitionBonds
namespace HoneycombStrip

variable {a b : ℕ} [NeZero (2 * b)] [NeZero (6 * a)]
  [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] (ha : 1 ≤ a) (hb : 2 ≤ b)

/-- Assign each fine site to its unique strip cell. -/
noncomputable def blockOf (v : ZMod (6 * a) × ZMod (2 * b)) : Cell a b :=
  Classical.choose ((injective_cover ha hb).1 v)

theorem block_sites (c : Cell a b) : PartitionBonds.sites (blockOf ha hb) c = region c := by
  ext v
  simp only [PartitionBonds.sites, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := Classical.choose_spec ((injective_cover ha hb).1 v)
  constructor
  · rintro rfl
    exact h.1
  · intro hv
    exact (h.2 c hv).symm

/-- Decode a physical coordinate into six binary spins in cyclic cell order. -/
noncomputable def coordinates (c : Cell a b) :
    Fin 64 ≃ RegionPhysicalConfig (d := 2) (PartitionBonds.sites (blockOf ha hb) c) := by
  rw [block_sites]
  exact finFunctionFinEquiv.symm.trans (rows c)

noncomputable local instance quotientAdj :
    DecidableRel ((Graph a b).map (blockOf ha hb)).Adj := Classical.decRel _

noncomputable abbrev quotientTensor :=
  coarseTensor (blockOf ha hb) (graphStatePEPS (Graph a b)) (coordinates ha hb)

/-- All coarse vertices are injective and every bundled bond admits an all-zero assignment. -/
theorem quotient_isInjective : (quotientTensor ha hb).IsInjective := by
  constructor
  · apply coarseTensor_vertexInjective
    intro c
    rw [block_sites]
    exact actual_injective ha hb c
  · intro q
    let bond := Bundle (blockOf ha hb) (graphStatePEPS (Graph a b)) q
    have : Nonempty bond := ⟨fun _ => (0 : Fin 2)⟩
    exact Nat.card_pos (α := bond)

/-- Contraction agrees coefficient by coefficient under the explicit six-bit coordinates. -/
theorem quotient_stateCoeff (s : Cell a b → Fin 64) :
    stateCoeff (quotientTensor ha hb) s =
      stateCoeff (graphStatePEPS (Graph a b)) (physical (blockOf ha hb) (coordinates ha hb) s) :=
  stateCoeff_coarseTensor _ _ _ _

end HoneycombStrip
