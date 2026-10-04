/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.FundamentalTheorem.InjectivePhase
import TNLean.MPS.FundamentalTheorem.FiniteLength

/-!
# Symmetry phases from chain lengths two and three

Unimodular proportionality of matrix product vectors at every length at least
two determines a single one-site phase. Blocking reduces the assertion to
the positive-length fundamental theorem, and comparison at multiples of two
and three identifies the phase as the ratio of the two coefficients.

Source context: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Appendix B,
lines 2614–2632. No additional chain-length threshold is assumed.
-/

open scoped Matrix

namespace MPSTensor

/-- Blocking translates proportionality at lengths at least two into
proportionality at every positive blocked length. Source context:
arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem mpv_blockTensor_eq_smul_of_mpv_eq_smul_from_two
    {d D DA : ℕ} (A : MPSTensor d DA) (B : MPSTensor d D)
    (c : ℕ → ℂ)
    (hC : ∀ N, 2 ≤ N → ∀ σ : Fin N → Fin d, mpv A σ = c N * mpv B σ)
    {L : ℕ} (hL : 2 ≤ L) {N : ℕ} (hN : 0 < N)
    (σ : Fin N → Fin (blockPhysDim d L)) :
    mpv (blockTensor A L) σ = c (N * L) * mpv (blockTensor B L) σ := by
  have hNL : 2 ≤ N * L := by nlinarith
  simpa only [mpv, coeff, ofFn_blockedConfigEquiv, evalWord_blockTensor] using
    hC (N * L) hNL (blockedConfigEquiv d N L σ)

/-- Unimodular MPV proportionality at every length at least two is already
geometric. The one-site phase is determined by the ratio of the coefficients
at lengths three and two. No additional chain-length threshold is required.
Source context: arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem eq_pow_div_of_mpv_eq_smul_from_two
    {d D DA : ℕ} [NeZero D] (A : MPSTensor d DA) {B : MPSTensor d D}
    (hB : Kraus.IsInjective B) (c : ℕ → ℂ)
    (hC : ∀ N, 2 ≤ N → ∀ σ : Fin N → Fin d, mpv A σ = c N * mpv B σ)
    (hnorm : ∀ N, 2 ≤ N → ‖c N‖ = 1) :
    ∀ N, 2 ≤ N → c N = (c 3 / c 2) ^ N := by
  have hblocked : ∀ L, 2 ≤ L → ∀ N, 0 < N → c (N * L) = c L ^ N := by
    intro L hL
    have hBL : Kraus.IsInjective (blockTensor B L) :=
      (isNBlkInjective_iff_blockTensor_isInjective B L).mp
        (wordSpan_eq_top_of_isInjective hB (by omega))
    obtain ⟨lam, _, hlam⟩ := exists_eq_pow_of_mpv_eq_smul (blockTensor A L) hBL
      (fun N => c (N * L))
      (fun N hN σ => mpv_blockTensor_eq_smul_of_mpv_eq_smul_from_two A B c hC hL hN σ)
      (fun N hN => hnorm (N * L) (by nlinarith))
    have hlamL : lam = c L := by simpa using (hlam 1 one_pos).symm
    simpa only [hlamL] using hlam
  intro N hN
  have hsquare : c N ^ 2 = c 2 ^ N := by
    calc
      c N ^ 2 = c (2 * N) := (hblocked N hN 2 (by omega)).symm
      _ = c (N * 2) := by rw [Nat.mul_comm]
      _ = c 2 ^ N := hblocked 2 le_rfl N (by omega)
  have hcube : c N ^ 3 = c 3 ^ N := by
    calc
      c N ^ 3 = c (3 * N) := (hblocked N hN 3 (by omega)).symm
      _ = c (N * 3) := by rw [Nat.mul_comm]
      _ = c 3 ^ N := hblocked 3 (by omega) N (by omega)
  have hne : c N ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm N hN]; exact one_ne_zero)
  rw [div_pow, ← hsquare, ← hcube]
  apply (eq_div_iff (pow_ne_zero 2 hne)).mpr
  ring

/-- The symmetry characters of injective MPVs at lengths at least two are
powers of one unitary character. Its value is the ratio of the length-three
and length-two characters. Source context: arXiv:1010.3732, Appendix B,
lines 2614–2632. -/
theorem exists_character_pow_of_mpv_eq_smul_from_two
    {G : Type*} [Group G] {d D DA : ℕ} [NeZero D]
    (A : G → MPSTensor d DA) {B : MPSTensor d D} (hB : Kraus.IsInjective B)
    (c : ℕ → G →* ℂ)
    (hC : ∀ g N, 2 ≤ N → ∀ σ : Fin N → Fin d, mpv (A g) σ = c N g * mpv B σ)
    (hnorm : ∀ N, 2 ≤ N → ∀ g, ‖c N g‖ = 1) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      (∀ g, χ g = c 3 g / c 2 g) ∧
      ∀ g N, 2 ≤ N → c N g = χ g ^ N := by
  let χ : G →* ℂ :=
    { toFun := fun g => c 3 g / c 2 g
      map_one' := by simp
      map_mul' := by
        intro g h
        simp only [map_mul, div_mul_div_comm] }
  refine ⟨χ, ?_, fun _ => rfl, ?_⟩
  · intro g
    change ‖c 3 g / c 2 g‖ = 1
    rw [norm_div, hnorm 3 (by omega) g, hnorm 2 le_rfl g, div_self one_ne_zero]
  · intro g
    exact eq_pow_div_of_mpv_eq_smul_from_two (A g) hB (fun N => c N g)
      (hC g) (fun N hN => hnorm N hN g)

/-- For tensors of the same bond dimension, the character recovered from
lengths two and three gives equality of MPVs after one-site rephasing, even
at length one. This uses injectivity to extend equality from length two.
Source context: arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem exists_character_sameMPV_smul_of_mpv_eq_smul_from_two
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    (A : G → MPSTensor d D) {B : MPSTensor d D} (hB : Kraus.IsInjective B)
    (c : ℕ → G →* ℂ)
    (hC : ∀ g N, 2 ≤ N → ∀ σ : Fin N → Fin d, mpv (A g) σ = c N g * mpv B σ)
    (hnorm : ∀ N, 2 ≤ N → ∀ g, ‖c N g‖ = 1) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      (∀ g, χ g = c 3 g / c 2 g) ∧
      ∀ g, SameMPV (χ g • B) (A g) := by
  obtain ⟨χ, hχnorm, hχ, hpow⟩ :=
    exists_character_pow_of_mpv_eq_smul_from_two A hB c hC hnorm
  refine ⟨χ, hχnorm, hχ, ?_⟩
  intro g
  have hχne : χ g ≠ 0 := norm_ne_zero_iff.mp (by rw [hχnorm g]; exact one_ne_zero)
  apply sameMPV_of_sameMPVFrom_of_injective (hB.smul hχne) (N₀ := 2)
  intro N hN σ
  rw [mpv_smul, hC g N hN σ, hpow g N hN]

end MPSTensor
