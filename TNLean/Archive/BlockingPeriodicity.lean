/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.BlockingTransfer
import TNLean.Channel.Peripheral.PeriodicityRemoval
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Archive.PeripheralClosure
import TNLean.MPS.Core.Transfer

/-!
# Legacy blocking periodicity wrapper

This file retains the older compatibility theorem that assumes both unitality
and trace preservation on a Kraus family.

The live Appendix-A route in the maintained library is
`TNLean.MPS.BlockingPeriodicityCFII_viaAdjoint`, which works from the
left-canonical / adjoint-fixed-point story. Accordingly, this module is
intentionally excluded from `TNLean.lean`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

open Matrix

/-- Legacy compatibility theorem for the historical unital + trace-preserving
route.

If `A` is unital, trace-preserving, and irreducible as a transfer map, then
some blocking length `p > 0` makes the blocked transfer map primitive. -/
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
  let E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    transferMap (d := d) (D := D) A
  have hfix : E (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simpa [E, MPSTensor.transferMap_apply] using h_unital
  have hone_ne : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
    classical
    have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
    let i0 : Fin D := ⟨0, hDpos⟩
    intro h
    have hentry := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i0 i0) h
    simp [i0] at hentry
  have hfin : (peripheralEigenvalues E).Finite := peripheralEigenvalues_finite (f := E)
  have hroot : ∀ μ ∈ hfin.toFinset, ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
    intro μ hμ
    have hμ' : μ ∈ peripheralEigenvalues E := hfin.mem_toFinset.mp hμ
    simpa [E] using
      (peripheral_isRootOfUnity_of_irreducible_biCanonical (K := A) h_unital h_tp hIrr μ
        (by simpa [E] using hμ'))
  obtain ⟨p, hp_pos, hp_all⟩ :=
    exists_common_power_eq_one_of_finite (s := hfin.toFinset) hroot
  have hper : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → μ ^ p = 1 := by
    intro μ hμ
    have hμ_fin : μ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hμ
    exact hp_all μ hμ_fin
  have hprim_pow : peripheralEigenvalues (E ^ p) = {1} :=
    peripheralEigenvalues_pow_eq_singleton (E := E) (p := p) hp_pos hper 1 hfix hone_ne
  refine ⟨p, hp_pos, ?_⟩
  rw [isPrimitive_iff]
  rw [MPSTensor.transferMap_blockTensor (A := A) (L := p)]
  simpa [E] using hprim_pow

/-- Legacy compatibility alias with the historical parameter names. -/
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
