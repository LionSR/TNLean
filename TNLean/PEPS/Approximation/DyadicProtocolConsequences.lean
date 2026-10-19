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

`largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint` proves
`LargeSizeDyadicProtocolConsequences`, which carries every clause of Proposition 7.1, from the
adaptive patch constraint of Proposition 4.1; with that constraint proved, it gives
`largeSizeDyadicProtocolConsequences` without hypotheses. The former scope restriction of this
interface is resolved in `docs/paper-gaps/polypeps_prop71_consequences_interface.tex`.

* `IsAngularScale.mono` : a larger information scale and threshold are again admissible;
* `DyadicProtocol.IsDistributionProtocol.mono` : larger count, expansion and error constants are
  again admissible;
* `protocolMeshRatio` : the mesh ratio `ν = 1 / 600000000` of the protocol, the smallest of the
  explicit ratios of the resizings, the point treatments and the direct repaintings;
* `protocolCountConstant`, `protocolExpansionConstant`, `protocolErrorConstant`,
  `protocolExpansionExponent`, `protocolLifetimeBound` : the named constants of the protocol, with
  the mesh ratio `ν` and the patch constants of Proposition 4.1 as parameters;
* `largeSizeDyadicProtocol_of_le_of_adaptivePatchConstraint` : Proposition 7.1 at every count,
  expansion and error constant at least the named ones;
* `largeSizeDyadicProtocolBounds_of_adaptivePatchConstraint` and
  `largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint` : the consequences of
  Proposition 7.1 used in §8, with separate constants and with one constant.

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

namespace DyadicProtocol.IsDistributionProtocol

variable {L q : ℕ} {P : Type} [Fintype P] {D : DyadicProtocol L q P} {Ω : StateSpace L q}
  {C_N C_K C_E : ℝ} {b k r : ℕ}

/-- **Larger constants are admissible.** The bounds of §8 with constants `C_N`, `C_K`, `C_E`
hold with any larger constants `C_N' ≥ C_N`, `C_K' ≥ C_K` and `C_E' ≥ C_E`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`,
`06-geometry.tex:17–52`. -/
theorem mono (h : D.IsDistributionProtocol Ω C_N C_K C_E b k r) {C_N' C_K' C_E' : ℝ}
    (hN : C_N ≤ C_N') (hK : C_K ≤ C_K') (hE : C_E ≤ C_E') :
    D.IsDistributionProtocol Ω C_N' C_K' C_E' b k r := by
  have hpow : C_K * (L : ℝ) ^ k ≤ C_K' * (L : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  obtain ⟨Ξ, hΞ, hlower, href⟩ := h.reference_changes
  exact { h with
    card_le := h.card_le.trans (by gcongr)
    changes_le := h.changes_le.trans (by gcongr)
    monomialBounded := fun t ht ↦ PairEffect.OriginalCircuit.isMonomialBounded_mono _
      (h.monomialBounded t ht) (Nat.floor_le_floor hpow)
    expansionBounded := fun t ht ↦ PairEffect.OriginalCircuit.isExpansionBounded_mono _
      (h.expansionBounded t ht) le_rfl hpow
    reference_step := fun t ht ↦ (h.reference_step t ht).trans (by gcongr)
    reference_changes := ⟨Ξ, hΞ, le_trans (by gcongr) hlower, href⟩ }

end DyadicProtocol.IsDistributionProtocol

/-- The separate-constant consequences of Proposition 7.1 give the single-constant ones, with
the largest of the three constants (`06-geometry.tex:12–53`). -/
theorem LargeSizeDyadicProtocolBounds.largeSizeDyadicProtocolConsequences
    (h : LargeSizeDyadicProtocolBounds) : LargeSizeDyadicProtocolConsequences := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C_N, C_K, C_E, b, k, r, L₀, hall⟩ := h q hq J Δ hJ hΔ
  refine ⟨max C_N (max C_K C_E), b, k, r, L₀, fun L hL hL₀ H E₀ Ω hΩ => ?_⟩
  obtain ⟨P, hP, D, hD⟩ := hall L hL hL₀ H E₀ Ω hΩ
  exact ⟨P, hP, D, hD.mono (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))⟩

/-! ### The named constants of the protocol -/

/-- The hole ratio `ε₀ = 1 / 30000` of the protocol: the holes at scale `n` have radius
`ε₀ min(n, t)`, `t = D log L`. It satisfies `2 ε₀ (a₀ + 1) ≤ a₀ / 2` for `a₀ = 1 / 5000`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–107, 349–351 and 408–415. -/
noncomputable def protocolHoleRatio : ℝ := 1 / 30000

/-- **The mesh ratio of the protocol**, at the hole ratio `ε₀ = protocolHoleRatio` and `K₀ = 20`:
the smaller of the point-treatment ratio `ν₂ = min(ε₀, 1) / 20000` and the direct-repainting
ratio `ν₃ = min(ε₀ / max(K₀, 1), 1) / 4`. It is also at most the resizing ratio
`ν₁ = min(ε₀, 1) / 8` and at most `1 / 6`, so it serves all three kinds of small-patch rewrites
of the protocol and the smallness condition of its constants. Its value is `1 / 600000000`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 447–541 and 559–570. -/
noncomputable def protocolMeshRatio : ℝ :=
  min (pointTreatmentRatio protocolHoleRatio) (directRepaintingRatio 20 protocolHoleRatio)

/-- The hole ratio of the protocol is positive (`06-geometry.tex:102–107`). -/
theorem protocolHoleRatio_pos : 0 < protocolHoleRatio := by norm_num [protocolHoleRatio]

/-- The mesh ratio of the protocol is positive (`06-geometry.tex:559–563`). -/
theorem protocolMeshRatio_pos : 0 < protocolMeshRatio :=
  lt_min (pointTreatmentRatio_pos protocolHoleRatio_pos)
    (directRepaintingRatio_pos 20 protocolHoleRatio_pos)

/-- The mesh ratio of the protocol is at most the point-treatment ratio
(`06-geometry.tex:481–505`). -/
theorem protocolMeshRatio_le_pointTreatmentRatio :
    protocolMeshRatio ≤ pointTreatmentRatio protocolHoleRatio :=
  min_le_left _ _

/-- The mesh ratio of the protocol is at most the direct-repainting ratio
(`06-geometry.tex:507–527`). -/
theorem protocolMeshRatio_le_directRepaintingRatio :
    protocolMeshRatio ≤ directRepaintingRatio 20 protocolHoleRatio :=
  min_le_right _ _

/-- The mesh ratio of the protocol is at most the resizing ratio (`06-geometry.tex:529–541`). -/
theorem protocolMeshRatio_le_resizeRatio : protocolMeshRatio ≤ resizeRatio protocolHoleRatio := by
  have h := protocolMeshRatio_le_pointTreatmentRatio
  have h0 := lt_min protocolHoleRatio_pos one_pos
  unfold pointTreatmentRatio at h
  unfold resizeRatio
  linarith

/-- The mesh ratio of the protocol is at most `1 / 6` (`06-geometry.tex:559–570`). -/
theorem protocolMeshRatio_le_one_sixth : protocolMeshRatio ≤ 1 / 6 := by
  have := protocolMeshRatio_le_pointTreatmentRatio.trans (pointTreatmentRatio_le _)
  linarith

/-- The mesh ratio of the protocol is `1 / 600000000`: the point-treatment ratio
`(1 / 30000) / 20000`, below the direct-repainting ratio `(1 / 30000) / 20 / 4`
(`06-geometry.tex:481–527`). -/
theorem protocolMeshRatio_eq : protocolMeshRatio = 1 / 600000000 := by
  have h1 : pointTreatmentRatio protocolHoleRatio = 1 / 600000000 := by
    rw [pointTreatmentRatio, protocolHoleRatio, min_eq_left (by norm_num : (1 / 30000 : ℝ) ≤ 1)]
    norm_num
  have h2 : directRepaintingRatio 20 protocolHoleRatio = 1 / 2400000 := by
    rw [directRepaintingRatio, protocolHoleRatio, max_eq_left (by norm_num : (1 : ℝ) ≤ 20),
      min_eq_left (by norm_num : (1 / 30000 : ℝ) / 20 ≤ 1)]
    norm_num
  rw [protocolMeshRatio, h1, h2, min_eq_left (by norm_num : (1 : ℝ) / 600000000 ≤ 1 / 2400000)]

/-- The prefactor `G = (C' + 1) ^ (3 b) (16 b² (C' + 1) ^ (6 b) + 1) ^ (2 b)` of the bound
`G L ^ k_K` on the number of monomials and on the coefficient sum of a small-patch rewrite with
`b` patches and tag counts at most `C' L ^ c'`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218 and
331–344. -/
def rewriteGatePrefactor (C' b : ℕ) : ℕ :=
  (C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^ (2 * b)

/-- The exponent `k_K = 3 b c' + 4 b (3 b c' + 30)` of the bound `G L ^ k_K` on the number of
monomials and on the coefficient sum of a small-patch rewrite with `b` patches and tag counts at
most `C' L ^ c'`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218 and
331–344. -/
def rewriteGateExponent (c' b : ℕ) : ℕ := 3 * b * c' + 4 * b * (3 * b * c' + 30)

/-- The bound of a small-patch rewrite is its prefactor times `L` to its exponent
(`05-frames.tex`, lines 331–344). -/
theorem rewriteGateBound_eq (C' c' b L : ℕ) :
    rewriteGateBound C' c' b L = rewriteGatePrefactor C' b * L ^ rewriteGateExponent c' b :=
  rfl

/-- The count constant `5042` of the protocol: at most `5042 L²` parties and at most
`5042 L³` changes, from the `5040 L³` changes of the schedule and the initial and final
changes.

Polynomial-PEPS manuscript, Proposition 7.1, items 1 and 2, `06-geometry.tex`, lines 18–25, and
the counts of the proof, lines 649–652. -/
noncomputable def protocolCountConstant : ℝ := 5042

/-- The bound `b_prot = 64 · 189` on the lifetime participation, the parties per gate, the gates
per change, the parties per square, and the address distances of the protocol: at most `64`
events use one party, and each event has at most `189` changes.

Polynomial-PEPS manuscript, Proposition 7.1, items 1–3, `06-geometry.tex`, lines 19–37, and the
lifetime argument, lines 572–631. -/
def protocolLifetimeBound : ℕ := 64 * 189

/-- The expansion constant of the protocol at mesh ratio `ν` and patch constant `C` of
Proposition 4.1: the prefactor `G` of the small-patch rewrites with `b = protocolPatchBound ε₀ ν`
patches and tag constant `⌈C⌉`. It bounds the number of monomials and the coefficient sum of
every gate by `G L ^ k_K`.

Polynomial-PEPS manuscript, Proposition 7.1, item 2, `06-geometry.tex`, lines 25–30 and
572–583; Lemma 6.3, `05-frames.tex`, lines 331–344. -/
noncomputable def protocolExpansionConstant (ν C : ℝ) : ℝ :=
  rewriteGatePrefactor ⌈C⌉₊ (protocolPatchBound protocolHoleRatio ν)

/-- The exponent `k_K` of the expansions of the protocol at mesh ratio `ν` and patch exponent
`c` of Proposition 4.1.

Polynomial-PEPS manuscript, Proposition 7.1, item 2, `06-geometry.tex`, lines 25–30 and
572–583; Lemma 6.3, `05-frames.tex`, lines 331–344. -/
noncomputable def protocolExpansionExponent (ν c : ℝ) : ℕ :=
  rewriteGateExponent ⌈c⌉₊ (protocolPatchBound protocolHoleRatio ν)

/-- The error constant `max 10080 (2 b + 1)` of the protocol at mesh ratio `ν`, with
`b = protocolPatchBound ε₀ ν`: each change has reference error at most `(2 b + 1) L⁻²⁰`, and the
frozen auxiliary frames carry at most `10080 L³` holes, at most two for each of the
`5040 L³` changes, so that `1 - 10080 L⁻⁵⁷ ≤ ‖Ξ‖`.

Polynomial-PEPS manuscript, Proposition 7.1, item 4, `06-geometry.tex`, lines 38–46, and its
proof, lines 581–583, 653–656 and 668–678. -/
noncomputable def protocolErrorConstant (ν : ℝ) : ℝ :=
  max 10080 (2 * protocolPatchBound protocolHoleRatio ν + 1)

/-- **Proposition 7.1 with explicit constants, from Proposition 4.1.** Assume the adaptive patch
constraint of Proposition 4.1. For every `q ≥ 2` and `J, Δ > 0` there are a mesh ratio
`0 < ν ≤ 1/6`, an information scale `D ≥ 1`, patch constants `C, c > 0` of Proposition 4.1 at
the radius constant `B₀ = 20 D` and power `60`, and a threshold `L₁`, such that for all
constants

* `C_N ≥ protocolCountConstant = 5042`,
* `C_K ≥ protocolExpansionConstant ν C`, the prefactor `G` of the small-patch rewrites,
* `C_E ≥ protocolErrorConstant ν = max 10080 (2 b + 1)`,

every gapped ground vector of a square Hamiltonian of side `L ≥ 2` with `L₁ ≤ L` has a dyadic
distribution protocol with the bounds of `DyadicProtocol.IsDistributionProtocol` at the count
constant `C_N`, the expansion constant `C_K`, the error constant `C_E`, the bound
`protocolLifetimeBound = 64 · 189`, the exponent `protocolExpansionExponent ν c` and `2 b` pair
effects, where `b = protocolPatchBound ε₀ ν`. The prefactor `G` enters only the expansion
constant; the threshold `L₁` is that of Proposition 3.4.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol` and its proof, `06-geometry.tex`,
lines 12–53 and 559–681, with Proposition 3.4 (`02-information.tex`, lines 635–658) and
Proposition 4.1 (`03-patches.tex`, lines 26–49) at the power `60` (`07-assembly.tex`, line 11). -/
theorem largeSizeDyadicProtocol_of_le_of_adaptivePatchConstraint
    (hpatch : AdaptivePatchConstraint) {q : ℕ} (hq : 2 ≤ q) {J Δ : ℝ} (hJ : 0 < J)
    (hΔ : 0 < Δ) :
    ∃ ν D C c L₁ : ℝ, 0 < ν ∧ ν ≤ 1 / 6 ∧ 1 ≤ D ∧ 0 < C ∧ 0 < c ∧
      (∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ →
          AdaptivePatchSupply (cellCenterPos L) Ω (20 * D) C c 60 L) ∧
      ∀ C_N C_K C_E : ℝ, protocolCountConstant ≤ C_N → protocolExpansionConstant ν C ≤ C_K →
        protocolErrorConstant ν ≤ C_E →
        ∀ L : ℕ, 2 ≤ L → L₁ ≤ L → ∀ h : SquareHamiltonian L q J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace L q, h.IsGappedGroundState E₀ Ω Δ →
            ∃ (P : Type) (_ : Fintype P) (D' : DyadicProtocol L q P),
              D'.IsDistributionProtocol Ω C_N C_K C_E protocolLifetimeBound
                (protocolExpansionExponent ν c) (2 * protocolPatchBound protocolHoleRatio ν) := by
  classical
  have : NeZero q := ⟨by omega⟩
  have ha₀ : angularConstant = 1 / 5000 := rfl
  -- the constants of the protocol, in the order of the source
  set ε₀ : ℝ := protocolHoleRatio with hε₀_def
  have hε : 0 < ε₀ := by norm_num [hε₀_def, protocolHoleRatio]
  have hε16 : ε₀ ≤ 1 / 16 := by norm_num [hε₀_def, protocolHoleRatio]
  set K₀ : ℝ := 20 with hK₀_def
  have H₁ := exists_isDistributionProtocol_of_largeRepaintings_of_le hε hε16
  have H₂ := pointTreatment_hasSourceBoundedChange_of_le hε hε16
  set ν := protocolMeshRatio with hν_def
  have hν : 0 < ν := protocolMeshRatio_pos
  have hνν₁ : ν ≤ resizeRatio ε₀ := protocolMeshRatio_le_resizeRatio
  have hνν₂ : ν ≤ pointTreatmentRatio ε₀ := protocolMeshRatio_le_pointTreatmentRatio
  have H₃ : IsDirectRepaintingRatio K₀ ε₀ ν :=
    isDirectRepaintingRatio_of_le K₀ hε protocolMeshRatio_le_directRepaintingRatio
  have hν6 : ν ≤ 1 / 6 := protocolMeshRatio_le_one_sixth
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
      ε₀_small := by rw [hε₀_def, ha₀]; norm_num [protocolHoleRatio]
      ν_pos := hν
      ν_small := by rw [hε₀_def, protocolHoleRatio]; linarith [hν6]
      a_pos := ha
      a_le := le_rfl
      D_pos := hDpos
      B₀_ge := le_rfl }
  -- the patch constants of Proposition 4.1
  obtain ⟨C, c, hC, hcpos, hsupply⟩ := hpatch.supply_cellCenterPos hq hJ hΔ (B₀ := B₀)
    (p := 60) (mul_pos (by norm_num) hDpos) (by norm_num)
  refine ⟨ν, D, C, c, max L₁ 1, hν, hν6, le_max_right _ _, hC, hcpos, hsupply,
    fun C_N C_K C_E hCN hCK hCE L hL hL₁ h E₀ Ω hΩ => ?_⟩
  set b := protocolPatchBound ε₀ ν with hb_def
  have hb : 18 ≤ b := eighteen_le_protocolPatchBound ε₀ ν
  set C' := ⌈C⌉₊ with hC'_def
  set c' := ⌈c⌉₊ with hc'_def
  have hC' : 1 ≤ C' := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hC).ne'
  set kK := rewriteGateExponent c' b with hkK_def
  set G : ℕ := rewriteGatePrefactor C' b with hG_def
  have hGC : (G : ℝ) ≤ C_K := hCK
  have hCE10080 : (10080 : ℝ) ≤ C_E := (le_max_left _ _).trans hCE
  have hCEb : (2 * b + 1 : ℝ) ≤ C_E := by
    have := (le_max_right _ _).trans hCE
    exact_mod_cast this
  obtain ⟨hk1, hkL, hk2⟩ := le_two_pow_clog_lt hL
  set k := Nat.clog 2 L with hk_def
  have hΩ1 : ‖Ω‖ = 1 := hΩ.1
  have hLL : max L₁ 1 ≤ (L : ℝ) := hL₁
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < D * Real.log L := mul_pos hDpos hℓ
  have hB : ε₀ * (D * Real.log L) ≤ B₀ * Real.log L := by
    rw [hB₀_def, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hε16.trans (by rw [hK₀_def]; norm_num)) ht.le
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
          ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧ seg (j + 1) ≠ [] := by
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
      ((protocolFrozen (q := q) P rank hr x).holes.length : ℝ)).sum ≤ C_E * (L : ℝ) ^ 3 := by
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
    have hL3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
    nlinarith
  obtain ⟨D', hD'⟩ := H₁ ν hν hνν₁ hc H₃ P hL hkL hk2 hΩ1 rank R₀
    (protocolFrozen P rank hr) protocolAuxOwner (C' := C') (c' := c') (kK := kK) (C_N := C_N)
    (C_K := C_K) (C_E := C_E)
    (Nat.le_ceil C) hC' (Nat.le_ceil c) hseg
    (fun x _ _ hh => norm_act_proj_sub_le_of_mem_holes_protocolFrozen P rank hr (by omega) x hh)
    hholes hCN
    (by
      rw [rewriteGateBound_eq]
      push_cast
      exact mul_le_mul_of_nonneg_right hGC (by positivity))
    hCEb
  exact ⟨ProtocolParty k, inferInstance, D', hD'⟩

/-- **Proposition 7.1 with separate constants, from Proposition 4.1.** The constants are those of
`largeSizeDyadicProtocol_of_le_of_adaptivePatchConstraint`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol` and its proof, `06-geometry.tex`,
lines 12–53 and 559–681. -/
theorem largeSizeDyadicProtocolBounds_of_adaptivePatchConstraint
    (hpatch : AdaptivePatchConstraint) : LargeSizeDyadicProtocolBounds := by
  intro q hq J Δ hJ hΔ
  obtain ⟨ν, -, C, c, L₁, -, -, -, -, -, -, H⟩ :=
    largeSizeDyadicProtocol_of_le_of_adaptivePatchConstraint hpatch hq hJ hΔ
  exact ⟨_, _, _, _, _, _, ⌈L₁⌉₊, fun L hL hL₀ => H _ _ _ le_rfl le_rfl le_rfl L hL
    ((Nat.le_ceil _).trans (by exact_mod_cast hL₀))⟩

/-- **Proposition 7.1 in the form used in §8, from Proposition 4.1.** Assume the adaptive patch
constraint of Proposition 4.1; the angular information bound of Proposition 3.4 is
`angularInformationBound`. Then for every `q ≥ 2` and `J, Δ > 0` there are constants
`C`, `b`, `k`, `r`
and a threshold `L₀` such that every gapped ground vector of a square Hamiltonian of side
`L ≥ max 2 L₀` has a dyadic distribution protocol with the bounds of
`DyadicProtocol.IsDistributionProtocol`. The constants are those of
`largeSizeDyadicProtocol_of_le_of_adaptivePatchConstraint`, with `C` the largest of the three.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol` and its proof, `06-geometry.tex`,
lines 12–53 and 559–681, with Proposition 3.4 (`02-information.tex`, lines 635–658) and
Proposition 4.1 (`03-patches.tex`, lines 26–49) at the power `60` (`07-assembly.tex`, line 11). -/
theorem largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint
    (hpatch : AdaptivePatchConstraint) : LargeSizeDyadicProtocolConsequences :=
  (largeSizeDyadicProtocolBounds_of_adaptivePatchConstraint
    hpatch).largeSizeDyadicProtocolConsequences

end TNLean.PEPS.Approximation
