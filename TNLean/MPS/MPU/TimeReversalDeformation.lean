/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntrinsicBlockingParity

/-!
# Intrinsic time-reversal signs along arbitrary MPU deformations

The exchange weight is an involution. On the stabilized rank-one transfer
range it therefore has eigenvalue one or minus one. The signed transfer
comparison quantizes the intrinsic trace without choosing standard-form
gates or deriving their local symmetry equation.

Canonical replacement preserves the two-site periodic operator. Thus both
quantization and constancy along continuous MPU paths hold for arbitrary
positive-dimensional ambient presentations. Canonical representatives are
chosen only pointwise inside the proof and need not vary continuously.

For supplied square standard forms, the existing finite-ring identity
identifies their gate trace with this intrinsic invariant. The unrestricted
local gate characterization remains a separate theorem.

Source: arXiv:1703.09188, canonical replacement, lines 319--356,
`eq:sigma-from-trace` and `prop:sigma-well-defined`, lines 1595--1631.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Every positive-dimensional MPU with adjoint symmetry at the even lengths
has intrinsic exchange trace equal to one or minus one. The reduced canonical
representative and the two transfer signs are derived internally. No supplied
standard form or local certificate is assumed.
Source: CPSV17, `eq:sigma-from-trace` and `prop:sigma-well-defined`,
lines 1595--1631; the intrinsic quantization is derived through the transfer. -/
theorem IsMPU.intrinsicTimeReversalSign_sq_eq_one
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ) :
    intrinsicTimeReversalSign U ^ 2 = 1 := by
  obtain ⟨E, _, V, hV, _, hMpo⟩ := hU.exists_reduced_cfii_representative
  have hTRV : ∀ N : ℕ, 1 < N → Even N → mpo V N = (mpo V N)ᴴ := by
    intro N hN heven
    simpa only [hMpo N (Nat.zero_lt_of_lt hN)] using hTR N hN heven
  have hfirst : intrinsicTimeReversalSign U = intrinsicTimeReversalSign V :=
    intrinsicTimeReversalSign_eq_of_mpo_two_eq (hMpo 2 (by omega)).symm
  obtain ⟨η, C, hη, hC, hvalue, _⟩ := hV.exists_intrinsic_blocking_phase_formula hTRV
  rw [hfirst, hvalue, mul_pow, sq_eq_one_iff.mpr hη, sq_eq_one_iff.mpr hC, one_mul]

/-- The intrinsic time-reversal sign is constant along every continuous path
of positive-dimensional MPUs with adjoint symmetry at the even lengths.
No canonical presentation, simplicity, gates, factors or local certificates
are supplied along the path. Source: CPSV17, `prop:sigma-well-defined`,
lines 1613--1631, using the intrinsic form of `eq:sigma-from-trace`. -/
theorem intrinsicTimeReversalSign_eq_on_timeReversal_path
    [NeZero d] [NeZero D]
    (W : ℝ → MPOTensor d D) (hW : ContinuousOn W (Set.Icc (0 : ℝ) 1))
    (hMPU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsMPU (W t))
    (hTR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ N : ℕ, 1 < N → Even N →
      mpo (W t) N = (mpo (W t) N)ᴴ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      intrinsicTimeReversalSign (W t) = intrinsicTimeReversalSign (W 0) := by
  have hcont := continuous_intrinsicTimeReversalSign.comp_continuousOn hW
  have hsq : Set.EqOn ((fun t ↦ intrinsicTimeReversalSign (W t)) ^ 2) 1
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hMPU t ht).intrinsicTimeReversalSign_sq_eq_one (hTR t ht)
  rcases isPreconnected_Icc.eq_one_or_eq_neg_one_of_sq_eq hcont hsq with h | h
  · intro t ht
    exact (h ht).trans (h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).symm
  · intro t ht
    exact (h ht).trans (h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).symm

/-- The normalized gate trace of any supplied square standard form is a sign
under actual even-family adjoint symmetry, regardless of the ambient virtual
presentation. This does not assert existence of a local gate certificate.
Source: CPSV17, `eq:sigma-from-trace`, lines 1595--1610. -/
theorem TwoSiteStandardFormData.timeReversalSign_sq_eq_one_of_even_mpo_eq_adjoint
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) :
    timeReversalSign u v ^ 2 = 1 := by
  let : NeZero (d * d) := NeZero.of_pos (Nat.mul_pos S.phys_pos S.phys_pos)
  let : NeZero D := NeZero.of_pos S.bond_pos
  rw [S.timeReversalSign_eq_intrinsic]
  exact S.isMPU.intrinsicTimeReversalSign_sq_eq_one hTR

/-- The gate traces at two points of an adjoint-symmetric continuous MPU
path agree. Standard forms are needed only at the two points being compared;
no standard forms or canonical presentations are chosen along the path.
Source: CPSV17, `prop:sigma-well-defined`, lines 1613--1631. -/
theorem timeReversalSign_eq_of_timeReversal_path
    (W : ℝ → MPOTensor (d * d) D)
    (hW : ContinuousOn W (Set.Icc (0 : ℝ) 1))
    (hMPU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsMPU (W t))
    (hTR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ N : ℕ, 1 < N → Even N →
      mpo (W t) N = (mpo (W t) N)ᴴ)
    {u₀ v₀ u₁ v₁ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S₀ : TwoSiteStandardFormData (W 0) u₀ v₀)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S₁ : TwoSiteStandardFormData (W t) u₁ v₁) :
    timeReversalSign u₁ v₁ = timeReversalSign u₀ v₀ := by
  let : NeZero (d * d) := NeZero.of_pos (Nat.mul_pos S₀.phys_pos S₀.phys_pos)
  let : NeZero D := NeZero.of_pos S₀.bond_pos
  rw [S₁.timeReversalSign_eq_intrinsic, S₀.timeReversalSign_eq_intrinsic]
  exact intrinsicTimeReversalSign_eq_on_timeReversal_path W hW hMPU hTR t ht

end MPOTensor
