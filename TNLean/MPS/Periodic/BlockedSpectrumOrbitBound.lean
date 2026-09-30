/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Core.BlockingTransfer
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Upper spectral bound for a blocked periodic tensor

The `p`-site transfer map is the `p`-th power of the one-site map. If the
one-site peripheral spectrum consists of the `m`-th roots of unity,
every peripheral eigenvalue after blocking has order dividing the length
of an orbit of translation by `p` in `ZMod m`. This is the upper spectral
bound used in arXiv:1708.00029, Section 4.1.
-/

open scoped Matrix

namespace MPSTensor

/-- The orbit length of translation by `p` annihilates the step in
`ZMod m`; equivalently, `m` divides `p` times the orbit length.
Source: arXiv:1708.00029, Section 4.1. -/
theorem period_dvd_blockSize_mul_orbitLength {m p n : ℕ} [NeZero m]
    (hn : addOrderOf (p : ZMod m) = n) : m ∣ p * n := by
  have hzero : n • (p : ZMod m) = 0 := by
    rw [← hn]
    exact addOrderOf_nsmul_eq_zero _
  have hcast : ((p * n : ℕ) : ZMod m) = 0 := by
    simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm] using hzero
  exact (ZMod.natCast_eq_zero_iff (p * n) m).mp hcast

/-- Every peripheral eigenvalue of a positively blocked periodic tensor
is a root of unity whose order divides the translation-orbit length.
Source: arXiv:1708.00029, Section 4.1. -/
theorem IsPeriodic.blockTensor_peripheral_pow_orbitLength
    {d D m p n : ℕ} [NeZero m]
    (A : MPSTensor d D) (hA : IsPeriodic m A)
    (hp : 0 < p) (hn : addOrderOf (p : ZMod m) = n) :
    peripheralEigenvalues (Kraus.mapLM (blockTensor A p)) ⊆
      {ν : ℂ | ν ^ n = 1} := by
  intro ν hν
  have hν_spec : ν ∈ spectrum ℂ ((Kraus.transferMap A) ^ p) := by
    rw [← transferMap_blockTensor]
    exact (Module.End.hasEigenvalue_iff_mem_spectrum).mp hν.1
  have hspec_map : spectrum ℂ ((Kraus.transferMap A) ^ p) =
      (fun μ : ℂ => μ ^ p) '' spectrum ℂ (Kraus.transferMap A) := by
    simpa using (spectrum.map_pow_of_pos (𝕜 := ℂ)
      (a := Kraus.transferMap A) (n := p) hp)
  rw [hspec_map] at hν_spec
  obtain ⟨μ, hμspec, rfl⟩ := hν_spec
  have hμnormpow : ‖μ‖ ^ p = 1 := by
    simpa only [norm_pow] using hν.2
  have hμnorm : ‖μ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg μ) (Nat.ne_of_gt hp)).mp hμnormpow
  have hμper : μ ∈ peripheralEigenvalues (Kraus.transferMap A) :=
    ⟨(Module.End.hasEigenvalue_iff_mem_spectrum).mpr hμspec, hμnorm⟩
  have hμm : μ ^ m = 1 := by
    rw [hA.peripheral_eq] at hμper
    exact hμper
  obtain ⟨k, hk⟩ := period_dvd_blockSize_mul_orbitLength hn
  change (μ ^ p) ^ n = 1
  rw [← pow_mul, hk, pow_mul, hμm, one_pow]

end MPSTensor
