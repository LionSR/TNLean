/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.PEPS.KitaevCheckerboardBlocking
import TNLean.PEPS.KitaevPeriodicTiling

/-!
# Periodic checkerboard contraction after four-site blocking

Source: SCP10, arXiv:1001.3807, Section 7.1, lines 2755–2827.
The paired boundary legs of adjacent blocks are glued in opposite clockwise
orders. The redundant labels are eliminated in the global contraction, not
assumed to decouple independently at every site. All contractions have identity
bond matrices, with no inserted torus strings.

**Scope restriction (binary checkerboard):** This is the untwisted binary
example with positive coarse periods. The corresponding fine periods are even.
The general-group fixed-point assertion is separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "TV" => TorusVertex width height

/-- Read the doubled bonds at a periodic block in clockwise order. Horizontal
pairs are ordered from top to bottom, vertical pairs from left to right; the
opposite ends are therefore reversed. Source: SCP10, four-site blocking diagram,
lines 2755–2794. -/
def kitaevPeriodicBlockBoundary (hb vb : TV → KitaevBit × KitaevBit) (v : TV) :
    KitaevBlockBoundary :=
  ![vb v, hb v, (vb (v.1, v.2 - 1)).swap, (hb (v.1 - 1, v.2)).swap]

/-- Contract the eight external legs of every actual four-site checkerboard
block on a periodic coarse lattice. Source: SCP10, lines 2755–2827. -/
def kitaevPeriodicBlockedCoeff (σ : TV → KitaevBlockSpins) : ℂ :=
  ∑ hb : TV → KitaevBit × KitaevBit, ∑ vb : TV → KitaevBit × KitaevBit,
    ∏ v, kitaevCheckerboardBlock (kitaevPeriodicBlockBoundary hb vb v) (σ v)

/-- The four elementary-site leg configurations in a globally tiled lattice.
Each internal bond appears at its two neighboring corners; each external bond
is read again in the adjacent periodic block. Source: SCP10, lines 2755–2794. -/
def kitaevPeriodicSiteLegs (hb vb : TV → KitaevBit × KitaevBit)
    (x : TV → Fin 4 → KitaevBit) (v : TV) : Fin 4 → Fin 4 → KitaevBit :=
  let α := kitaevPeriodicBlockBoundary hb vb v
  ![![(α 0).2, (α 1).1, x v 1, x v 0],
    ![x v 1, (α 1).2, (α 2).1, x v 2],
    ![x v 3, x v 2, (α 2).2, (α 3).1],
    ![(α 0).1, x v 0, x v 3, (α 3).2]]

/-- The unblocked elementary checkerboard contraction, indexed by the disjoint
periodic tiling. The sum retains all four internal and four external bonds per
block, and the product has one elementary tensor at each fine-lattice site.
Source: SCP10, equations `eq:ex:kitaev-tens` and `eq:ex:kitaev-colordiff-rep`,
lines 2718–2827. -/
def kitaevPeriodicFineCoeff (σ : TV × Fin 4 → KitaevBit) : ℂ :=
  ∑ hb : TV → KitaevBit × KitaevBit, ∑ vb : TV → KitaevBit × KitaevBit,
    ∑ x : TV → Fin 4 → KitaevBit,
      ∏ p : TV × Fin 4, kitaevElementaryTensor (decide (p.2 = 0 ∨ p.2 = 2))
        (kitaevPeriodicSiteLegs hb vb x p.1 p.2) (σ p)

/-- Regroup the actual fine-site contraction into disjoint 2×2 blocks. All
internal sums are derived from the global bond sum using the distributive law.
Source: SCP10, Section 7.1, lines 2755–2794. -/
theorem kitaevPeriodicFineCoeff_eq_blocked (σ : TV × Fin 4 → KitaevBit) :
    kitaevPeriodicFineCoeff σ = kitaevPeriodicBlockedCoeff (fun v i => σ (v, i)) := by
  unfold kitaevPeriodicFineCoeff kitaevPeriodicBlockedCoeff
  apply Finset.sum_congr₂
  intro hb _ vb _
  conv_lhs =>
    arg 2
    intro x
    rw [Fintype.prod_prod_type]
  simp_rw [Fin.prod_univ_four]
  have hlocal (v : TV) :
      kitaevCheckerboardBlock (kitaevPeriodicBlockBoundary hb vb v) (fun i => σ (v, i)) =
        ∑ x : Fin 4 → KitaevBit,
          kitaevElementaryTensor true
            (kitaevPeriodicSiteLegs hb vb (fun _ => x) v 0) (σ (v, 0)) *
          kitaevElementaryTensor false
            (kitaevPeriodicSiteLegs hb vb (fun _ => x) v 1) (σ (v, 1)) *
          kitaevElementaryTensor true
            (kitaevPeriodicSiteLegs hb vb (fun _ => x) v 2) (σ (v, 2)) *
          kitaevElementaryTensor false
            (kitaevPeriodicSiteLegs hb vb (fun _ => x) v 3) (σ (v, 3)) := by
    unfold kitaevCheckerboardBlock
    apply Finset.sum_congr rfl
    intro x _
    change _ * _ * _ * _ = _
    dsimp [kitaevPeriodicSiteLegs]
    ring
  simp_rw [hlocal]
  rw [Fintype.prod_sum]
  rfl

private def duplicateBonds (p : (TV → KitaevBit) × (TV → KitaevBit)) :
    (TV → KitaevBit × KitaevBit) × (TV → KitaevBit × KitaevBit) :=
  (fun v => (p.1 v, p.1 v), fun v => (p.2 v, p.2 v))

omit [NeZero width] [NeZero height] in
private theorem duplicateBonds_injective :
    Function.Injective (duplicateBonds (width := width) (height := height)) := by
  intro p q h
  exact Prod.ext
    (funext fun v => congrArg (fun z => (z.1 v).1) h)
    (funext fun v => congrArg (fun z => (z.2 v).1) h)

private theorem periodicBlock_prod_eq_zero
    (p : (TV → KitaevBit × KitaevBit) × (TV → KitaevBit × KitaevBit))
    (hp : p ∉ Set.range duplicateBonds) (σ : TV → KitaevBlockSpins) :
    (∏ v, kitaevCheckerboardBlock (kitaevPeriodicBlockBoundary p.1 p.2 v) (σ v)) = 0 := by
  have hex : ∃ v, (p.1 v).2 ≠ (p.1 v).1 ∨ (p.2 v).2 ≠ (p.2 v).1 := by
    by_contra h
    push Not at h
    apply hp
    refine ⟨(fun v => (p.1 v).1, fun v => (p.2 v).1), ?_⟩
    apply Prod.ext <;> funext v
    · exact Prod.ext rfl (h v).1.symm
    · exact Prod.ext rfl (h v).2.symm
  obtain ⟨v, hv⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  rw [kitaevCheckerboardBlock_apply]
  split_ifs with h
  · exfalso
    rcases hv with hh | hv
    · exact hh (h.1 1)
    · exact hv (h.1 0)
  · rfl

/-- Global elimination of every redundant paired-bond register. The result is
the color-difference tensor on the coarse torus, with no scalar prefactor.
Source: SCP10, Section 7.1, lines 2755–2827. This concerns the binary checkerboard
example, whose redundant virtual registers are fixed at zero, rather than the
Bell pairs of the general regular-representation construction in Section 6.4. -/
theorem kitaevPeriodicBlockedCoeff_eq_colorNetwork (σ : TV → KitaevBlockSpins) :
    kitaevPeriodicBlockedCoeff σ =
      torusBondNetwork (fun v c => kitaevBlockColorMatrix (σ v)
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]) 1 1 := by
  rw [kitaevPeriodicBlockedCoeff, torusBondNetwork_one]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine (Fintype.sum_of_injective duplicateBonds duplicateBonds_injective _ _
    (fun p hp => periodicBlock_prod_eq_zero p hp σ) ?_).symm
  intro p
  apply Finset.prod_congr rfl
  intro v _
  have hb : kitaevPeriodicBlockBoundary (duplicateBonds p).1 (duplicateBonds p).2 v =
      fun i =>
        (![p.2 v, p.1 v, p.2 (v.1, v.2 - 1), p.1 (v.1 - 1, v.2)] i,
         ![p.2 v, p.1 v, p.2 (v.1, v.2 - 1), p.1 (v.1 - 1, v.2)] i) := by
    funext i
    fin_cases i <;> rfl
  rw [kitaevCheckerboardBlock_apply, hb]
  simp [kitaevBlockColorMatrix]

/-- The entire periodic elementary checkerboard state contracts to the coarse
color-difference PEPS. Unlike a local blocking lemma, this identity includes
all bonds crossing between distinct blocks. Source: SCP10, Section 7.1,
lines 2755–2827. -/
theorem kitaevPeriodicFineCoeff_eq_colorNetwork (σ : TV × Fin 4 → KitaevBit) :
    kitaevPeriodicFineCoeff σ =
      torusBondNetwork (fun v c => kitaevBlockColorMatrix (fun i => σ (v, i))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]) 1 1 := by
  rw [kitaevPeriodicFineCoeff_eq_blocked, kitaevPeriodicBlockedCoeff_eq_colorNetwork]

end TNLean.PEPS
