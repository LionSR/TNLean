/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BlockingTransfer
import TNLean.Channel.PeriodicityRemoval
import TNLean.Channel.PeripheralSpectrum
import TNLean.Channel.PeripheralClosure
import TNLean.MPS.Transfer


/-!
# Blocking periodicity removal

This file connects the channel-level periodicity-removal lemmas
(`TNLean.Channel.PeriodicityRemoval`) to the MPS blocking construction
(`TNLean.MPS.BlockingTransfer`).

It records the **legacy stronger bi-canonical route**: if a Kraus family is both
right-canonical / unital and left-canonical / trace-preserving, then its peripheral
eigenvalues are roots of unity, hence a common power kills them. Physically blocking
an MPS tensor corresponds to taking a power of its transfer map, so for some blocking
length the blocked transfer map is primitive.

For the Appendix-A pipeline used later in the project, the preferred theorem is the
left-canonical-only result in `BlockingPeriodicityCFII_viaAdjoint.lean`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

open Matrix

/-- **Blocking periodicity via bi-canonical gauge**: if `A` is both right-canonical / unital
and left-canonical / trace-preserving (i.e., bi-canonical), and the transfer map is
irreducible, then some blocking length `p > 0` makes the blocked transfer map primitive.

Equivalently, some power of the transfer map has peripheral eigenvalues `{1}`. -/
theorem exists_blockTensor_isPrimitive_of_irreducible_biCanonical
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (h_unital : KadisonSchwarz.IsUnitalKraus A)
    (h_tp : KadisonSchwarz.IsTPKraus A)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A)) :
    ∃ p : ℕ, 0 < p ∧
      IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p)) := by
  classical
  -- Abbreviate the original transfer map.
  let E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    transferMap (d := d) (D := D) A
  -- `ρ := 1` is a nonzero fixed point for `E` by unitality.
  have hfix : E (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    -- Expand `E 1` and use the unitality hypothesis.
    simpa [E, MPSTensor.transferMap_apply] using h_unital
  have hone_ne : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
    classical
    have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
    let i0 : Fin D := ⟨0, hDpos⟩
    intro h
    have hentry := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i0 i0) h
    -- Simplifying the diagonal entry turns this into a contradiction.
    simp [i0] at hentry
  -- The peripheral eigenvalues form a finite set.
  have hfin : (peripheralEigenvalues E).Finite := peripheralEigenvalues_finite (f := E)
  -- Each peripheral eigenvalue is a root of unity (irreducible + bi-canonical).
  have hroot : ∀ μ ∈ hfin.toFinset, ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
    intro μ hμ
    have hμ' : μ ∈ peripheralEigenvalues E := hfin.mem_toFinset.mp hμ
    -- Use the channel-level root-of-unity lemma.
    simpa [E] using
      (peripheral_isRootOfUnity_of_irreducible_biCanonical (K := A) h_unital h_tp hIrr μ
        (by simpa [E] using hμ'))
  -- Choose a common power killing all peripheral eigenvalues.
  obtain ⟨p, hp_pos, hp_all⟩ :=
    exists_common_power_eq_one_of_finite (s := hfin.toFinset) hroot
  have hper : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → μ ^ p = 1 := by
    intro μ hμ
    have hμ_fin : μ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hμ
    exact hp_all μ hμ_fin
  -- Hence the peripheral eigenvalues of `E ^ p` collapse to `{1}`.
  have hprim_pow : peripheralEigenvalues (E ^ p) = {1} :=
    peripheralEigenvalues_pow_eq_singleton (E := E) (p := p) hp_pos hper 1 hfix hone_ne
  refine ⟨p, hp_pos, ?_⟩
  -- Rewrite the blocked transfer map as a power and apply the previous lemma.
  unfold IsPrimitive
  -- `transferMap (blockTensor A p) = (transferMap A) ^ p`.
  rw [MPSTensor.transferMap_blockTensor (A := A) (L := p)]
  simpa [E] using hprim_pow

/-- Alias for `exists_blockTensor_isPrimitive_of_irreducible_biCanonical` with
more explicit parameter names matching the bi-canonical terminology. -/
theorem exists_blockTensor_isPrimitive_of_biCanonical_of_isIrreducibleMap
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hRight : KadisonSchwarz.IsUnitalKraus A)
    (hLeft : KadisonSchwarz.IsTPKraus A)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A)) :
    ∃ p : ℕ, 0 < p ∧
      IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p)) := by
  simpa using exists_blockTensor_isPrimitive_of_irreducible_biCanonical
    (A := A) hRight hLeft hIrr

end MPSTensor
