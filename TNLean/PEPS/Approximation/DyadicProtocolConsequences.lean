/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationFromGap
import TNLean.PEPS.Approximation.DyadicProtocolFrozenFrames

/-!
# The dyadic distribution protocol from Proposition 4.1

This file assembles the Section 8 consequences of Proposition 7.1 of the polynomial-PEPS
manuscript at every large size. The angular information bound of Proposition 3.4 is the theorem
`angularInformationBound`; the adaptive patch constraint of Proposition 4.1 is taken as a
hypothesis in the form in which the manuscript states it (`06-geometry.tex`, lines 12–53 and
559–681). The constants are fixed in the order of
the source: `K₀ = 20`, a small `ε₀`, a small mesh ratio `ν`, the clearance `a = a₀ / 2`, the
information scale `D` of Proposition 3.4 at that clearance, and `B₀ = K₀ D`; then Proposition 4.1
supplies the patch constants.

**Scope restriction (consequences of Proposition 7.1):**
`largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint` proves the weaker
`LargeSizeDyadicProtocolConsequences` interface used in Section 8, not full Proposition 7.1.
The interface omits the following clauses of the proposition:

* a designated party holding the main copy of `Ω` and private initialization of each auxiliary
  copy at its designated party, rather than arbitrary normalized product initialization;
* factorization of every intermediate reference vector into main and auxiliary encoded frames,
  with every factor of norm at most one;
* the repainting-event scale and grid address for each additional party.

These omissions and the retained Section 8 consequences are recorded in
`docs/paper-gaps/polypeps_prop71_consequences_interface.tex`. To eliminate this restriction,
construct a certificate carrying all omitted clauses, prove full Proposition 7.1 for it, and
project to the present interface. The angular-scale and dyadic-padding lemmas in this module
are not part of this restriction.

* `IsAngularScale.mono` : a larger information scale and threshold are again admissible;
* `largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint` : the consequences of
  Proposition 7.1 used in §8.

## References

* Polynomial-PEPS manuscript (September 24, 2026): Proposition 3.4 (`02-information.tex`,
  lines 635–658), Proposition 4.1 (`03-patches.tex`, lines 26–49), and Proposition 7.1 with its
  proof (`06-geometry.tex`, lines 12–53 and 559–681; `07-assembly.tex`, line 11).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-- **A larger information scale is admissible.** Proposition 3.4 at the scale `D` and threshold
`L₀` gives it at every larger scale `D'` and threshold `max L₀ 1`: the hypotheses at `D'` are
stronger.

Polynomial-PEPS manuscript, `02-information.tex`, lines 635–658. -/
theorem IsAngularScale.mono {q : ℕ} {J Δ a A₀ : ℝ} {m₀ p : ℕ} {D L₀ D' : ℝ}
    (h : IsAngularScale q J Δ a A₀ m₀ p D L₀) (ha : 0 ≤ a) (hD : D ≤ D') :
    IsAngularScale q J Δ a A₀ m₀ p D' (max L₀ 1) := by
  intro L hL h' E₀ Ω hΩ pos c hpos V hV X E hXE n hn hnL hdiam hsep
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (le_of_max_le_right hL)
  have ht : D * Real.log L ≤ D' * Real.log L := mul_le_mul_of_nonneg_right hD hlog
  refine h L (le_of_max_le_left hL) h' E₀ Ω hΩ pos c hpos V hV X E hXE n (ht.trans hn) hnL hdiam
    fun x hx y hy => le_trans ?_ (hsep x hx y hy)
  exact mul_le_mul_of_nonneg_left (max_le_max ht le_rfl) ha

/-- The padded side: `L ≤ 2 ^ k < 2 L` for `k = ⌈log₂ L⌉`, `L ≥ 2`. -/
theorem le_two_pow_clog_lt {L : ℕ} (hL : 2 ≤ L) :
    1 ≤ Nat.clog 2 L ∧ L ≤ 2 ^ Nat.clog 2 L ∧ 2 ^ Nat.clog 2 L < 2 * L := by
  have h1 := Nat.clog_pos (b := 2) (by norm_num) (by omega : 1 < L)
  exact ⟨h1, le_paddedSide L, paddedSide_lt_two_mul (by omega)⟩

/-- **Proposition 7.1 in the form used in §8, from Proposition 4.1.** Assume the adaptive patch
constraint of Proposition 4.1; the angular information bound of Proposition 3.4 is
`angularInformationBound`. Then for every `q ≥ 2` and `J, Δ > 0` there are constants
`C`, `b`, `k`, `r`
and a threshold `L₀` such that every gapped ground vector of a square Hamiltonian of side
`L ≥ max 2 L₀` has a dyadic distribution protocol with the bounds of
`DyadicProtocol.IsDistributionProtocol`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol` and its proof, `06-geometry.tex`,
lines 12–53 and 559–681, with Proposition 3.4 (`02-information.tex`, lines 635–658) and
Proposition 4.1 (`03-patches.tex`, lines 26–49) at the power `60` (`07-assembly.tex`, line 11). -/
theorem largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint
    (hpatch : AdaptivePatchConstraint) : LargeSizeDyadicProtocolConsequences := by
  classical
  intro q hq J Δ hJ hΔ
  have : NeZero q := ⟨by omega⟩
  have ha₀ : angularConstant = 1 / 5000 := rfl
  -- the constants of the protocol, in the order of the source
  set ε₀ : ℝ := 1 / 30000 with hε₀_def
  have hε : 0 < ε₀ := by norm_num
  have hε16 : ε₀ ≤ 1 / 16 := by norm_num
  set K₀ : ℝ := 20 with hK₀_def
  obtain ⟨ν₁, hν₁, H₁⟩ := exists_isDistributionProtocol_of_largeRepaintings hε hε16
  obtain ⟨ν₂, hν₂, H₂⟩ := exists_pointTreatment_hasSourceBoundedChange hε hε16
  obtain ⟨ν₃, hν₃, H₃⟩ := exists_isDirectRepaintingRatio K₀ hε
  set ν := min (min ν₁ ν₂) (min ν₃ (1 / 6)) with hν_def
  have hν : 0 < ν := lt_min (lt_min hν₁ hν₂) (lt_min hν₃ (by norm_num))
  have hνν₁ : ν ≤ ν₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hνν₂ : ν ≤ ν₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hνν₃ : ν ≤ ν₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hν6 : ν ≤ 1 / 6 := (min_le_right _ _).trans (min_le_right _ _)
  set a : ℝ := angularConstant / 2 with ha_def
  have ha : 0 < a := by rw [ha_def, ha₀]; norm_num
  obtain ⟨D₁, L₁, hD₁⟩ :=
    (angularInformationBound (q := q) (J := J) (by omega) hJ.le hΔ).exists_isAngularScale
      ha le_rfl 4 (p := 60) (by norm_num)
  set D : ℝ := max D₁ 1 with hD_def
  have hD := hD₁.mono ha.le (le_max_left D₁ 1)
  set B₀ : ℝ := K₀ * D with hB₀_def
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc : IsProtocolConstants K₀ ε₀ ν a D B₀ :=
    { twenty_le_K₀ := le_rfl
      ε₀_pos := hε
      ε₀_small := by rw [hε₀_def, ha₀]; norm_num
      ν_pos := hν
      ν_small := by rw [hε₀_def]; linarith [hν6]
      a_pos := ha
      a_le := le_rfl
      D_pos := hDpos
      B₀_ge := le_rfl }
  -- the patch constants of Proposition 4.1
  obtain ⟨C, c, hC, hcpos, hsupply⟩ := hpatch.supply_cellCenterPos hq hJ hΔ (B₀ := B₀)
    (p := 60) (mul_pos (by norm_num) hDpos) (by norm_num)
  set b := protocolPatchBound ε₀ ν with hb_def
  have hb : 18 ≤ b := eighteen_le_protocolPatchBound ε₀ ν
  set C' := ⌈C⌉₊ with hC'_def
  set c' := ⌈c⌉₊ with hc'_def
  have hC' : 1 ≤ C' := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hC).ne'
  set kK := 3 * b * c' + 4 * b * (3 * b * c' + 30) with hkK_def
  set G : ℕ := (C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^ (2 * b) with hG_def
  set C₁ : ℝ := max 10080 (max (G : ℝ) (2 * b + 1)) with hC₁_def
  refine ⟨C₁, 64 * 189, kK, 2 * b, ⌈max L₁ 1⌉₊, fun L hL hL₁ h E₀ Ω hΩ => ?_⟩
  obtain ⟨hk1, hkL, hk2⟩ := le_two_pow_clog_lt hL
  set k := Nat.clog 2 L with hk_def
  have hΩ1 : ‖Ω‖ = 1 := hΩ.1
  have hLL : max L₁ 1 ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL₁)
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < D * Real.log L := mul_pos hDpos hℓ
  have hB : ε₀ * (D * Real.log L) ≤ B₀ * Real.log L := by
    rw [hB₀_def, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by norm_num) ht.le
  have hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L :=
    fun _ => ⟨mul_pos hε ht, hB⟩
  have P := hsupply L hL h E₀ Ω hΩ
  set rank : GuideLabel → ℕ := fun _ => 0
  set R₀ : RepaintedSquare k := ⟨⟨⟨0, by omega⟩, ⟨0, by positivity⟩, ⟨0, by positivity⟩⟩,
    by change 0 < k; omega⟩
  have hK1 : 1 ≤ rewriteGateBound C' c' b L := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hseg : ∀ i (hi : i < (eventSchedule k).length) (S : DyadicSquare k),
      (eventSchedule k)[i] = .inl S → largeSquare K₀ (D * Real.log L) S = true →
      ∃ seg : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)),
        seg 0 = protocolState P rank R₀ hε ht hB (largeSquare K₀ (D * Real.log L))
          (protocolFrozen P rank hr) protocolAuxOwner i ∧
        seg 189 = protocolState P rank R₀ hε ht hB (largeSquare K₀ (D * Real.log L))
          (protocolFrozen P rank hr) protocolAuxOwner (i + 1) ∧
        ∀ j < 189, HasSourceBoundedChange Ω (seg j) (seg (j + 1)) (ℓ := []) (1 : ℂ)
          {p | EventUses (.inl S) p} (2 * b) (rewriteGateBound C' c' b L) (2 * b)
          ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) := by
    intro i hi S he hl
    have hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (S.1 : ℕ) := by
      simpa [largeSquare] using hl
    exact exists_largeRepainting_segment hD hLL hΩ le_rfl le_rfl hc hL hkL hk2 P rank R₀ ht
      hB (protocolFrozen P rank hr) protocolAuxOwner hi he hl (by omega) hK1
      (fun hS => by
        intro g hg M M' Q₀ hQ hM L₀ hL₀
        exact H₂ ν hν hνν₂ hc hL hΩ1 P rank ⟨S, hS⟩ hlarge _ hg Q₀ hQ hM L₀ hL₀ (Nat.le_ceil C)
          hC' (Nat.le_ceil c))
      (fun hS e => protocolFrozen_auxInit P rank hr hi he hS e)
      (fun hS e => protocolAuxOwner_auxInit hi he hS e)
  have hholes : ((auxIndices k (largeSquare K₀ (D * Real.log L))).map fun x =>
      ((protocolFrozen (q := q) P rank hr x).holes.length : ℝ)).sum ≤ C₁ * (L : ℝ) ^ 3 := by
    have h2 : ∀ y ∈ (auxIndices k (largeSquare K₀ (D * Real.log L))).map fun x =>
        ((protocolFrozen (q := q) P rank hr x).holes.length : ℝ), y ≤ 2 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact_mod_cast length_holes_protocolFrozen_le P rank hc hL hr hx
    have hlen : ((auxIndices k (largeSquare K₀ (D * Real.log L))).length : ℝ) ≤
        5040 * (L : ℝ) ^ 3 :=
      (by exact_mod_cast List.length_filter_le _ _ :
        ((auxIndices k (largeSquare K₀ (D * Real.log L))).length : ℝ) ≤
          (protocolSchedule k (largeSquare K₀ (D * Real.log L))).length).trans
        (length_protocolSchedule_le_cube hk2 _)
    have hsum := List.sum_le_length_nsmul _ 2 h2
    rw [List.length_map, nsmul_eq_mul] at hsum
    have hC₁ : (10080 : ℝ) ≤ C₁ := le_max_left _ _
    have hL3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
    nlinarith
  obtain ⟨D', hD'⟩ := H₁ ν hν hνν₁ hc (H₃ ν hν hνν₃) P hL hkL hk2 hΩ1 rank R₀
    (protocolFrozen P rank hr) protocolAuxOwner (C' := C') (c' := c') (kK := kK) (C₁ := C₁)
    (Nat.le_ceil C) hC' (Nat.le_ceil c) hseg
    (fun x _ _ hh => norm_act_proj_sub_le_of_mem_holes_protocolFrozen P rank hr (by omega) x hh)
    hholes ((by norm_num : (5042 : ℝ) ≤ 10080).trans (le_max_left _ _))
    (by
      have hpow : (0 : ℝ) ≤ (L : ℝ) ^ kK := by positivity
      have hGC : (G : ℝ) ≤ C₁ := (le_max_left _ _).trans (le_max_right _ _)
      have hRG : (rewriteGateBound C' c' b L : ℝ) = (G : ℝ) * (L : ℝ) ^ kK := by
        rw [show rewriteGateBound C' c' b L = G * L ^ kK from rfl]
        push_cast
        ring
      rw [hRG]
      exact mul_le_mul_of_nonneg_right hGC hpow)
    ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨ProtocolParty k, inferInstance, D', hD'⟩

end TNLean.PEPS.Approximation
