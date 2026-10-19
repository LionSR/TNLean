/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximationFromSquareAreaLaw

/-!
# The constants of the polynomial PEPS approximation at given area-law and angular constants

Theorem 1.1 of the polynomial-PEPS manuscript asserts only that its constants exist. Its proof in
§8 fixes them in a definite order (`07-assembly.tex`, lines 179–214): the hole ratio, the mesh
ratio, the clearance and the information scale `D` of Proposition 3.4, then the patch constants
of Proposition 4.1 at `B₀ = 20 D`, the constants of the protocol of Proposition 7.1, the link
constants of Theorem 5.2 at accuracy `L⁻⁵`, and the congestion of Lemma 8.2.

This file writes these constants as functions of the area-law constant `C_A` of
Proposition 2.1 and of the slope `D` and threshold `L_ang` of Proposition 3.4. Every other input
is a named numerical constant: the hole ratio `ε₀ = 1 / 30000`, the mesh ratio
`ν = protocolMeshRatio = 1 / 600000000`, the clearance `a₀ / 2 = 1 / 10000` and the power `60`.

## Main definitions

* `pepsLinkExponentOf`, `pepsLinkPrefactorOf`: the link exponent and prefactor of the compressed
  network.
* `pepsCongestion`: the congestion `χ` of Lemma 8.2.
* `pepsNetworkErrorConstant`: the constant `C` of the network error `C L⁻⁵`.
* `pepsSizeThresholdOf`: the size threshold above which the network gives the approximation.
* `pepsBondExponentOf`, `pepsLargeSizePrefactorOf`: the bond exponent `k χ + 1` and the bond
  prefactor `max(C₁, 1) ^ χ` above the threshold.

## Main results

* `polynomialPEPSApproximation_of_ratios`: at a square area law with constant `C_A` and an
  information scale `D ≥ 1` with threshold `L_ang` of Proposition 3.4, every gapped ground vector
  of side `L ≥ 2` above `pepsSizeThresholdOf L_ang` has a PEPS approximation with these bond
  constants.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Theorem 1.1 `thm:main`,
  `00-introduction.tex:36–57`; Proposition 2.1, `01-preliminaries.tex:39–58`; Proposition 3.4,
  `02-information.tex:635–658`; Proposition 4.1, `03-patches.tex:26–49`; Proposition 7.1,
  `06-geometry.tex:12–53` and `559–681`; §8, `07-assembly.tex:9–214`. Revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-- The link exponent `k` of the compressed network: Theorem 5.2 at accuracy `L⁻⁵`, with `3` as
the gate-count exponent, physical-dimension exponent `0`, `2 b` pair effects for
`b = protocolPatchBound ε₀ ν`, arity `b_prot = protocolLifetimeBound`, and monomial and
coefficient-sum exponent `k_K = protocolExpansionExponent ν c`, where `c` is the patch exponent of
Proposition 4.1 at `B₀ = 20 D`, power `60` and area-law constant `C_A`.

Source: Polynomial-PEPS manuscript, `07-assembly.tex:45–63`, with Theorem 5.2,
`04-compression.tex:137–175`, and the expansions of Proposition 7.1, `06-geometry.tex:25–30`. -/
def pepsLinkExponentOf (q : ℕ) (J Δ C_A D : ℝ) : ℕ :=
  sampledNetworkExponent (2 * protocolPatchBound protocolHoleRatio protocolMeshRatio)
    protocolLifetimeBound 3 0
    (protocolExpansionExponent protocolMeshRatio (adaptivePatchExponent q J Δ (20 * D) 60 C_A))
    (protocolExpansionExponent protocolMeshRatio (adaptivePatchExponent q J Δ (20 * D) 60 C_A)) 5

/-- The link prefactor `C₁` of the compressed network: Theorem 5.2 with `2 b` pair effects, arity
`b_prot`, gate-count constant `5042 b_prot`, physical dimension `q`, and monomial-count and
coefficient-sum constant `G = protocolExpansionConstant ν C`, where `C` is the patch prefactor of
Proposition 4.1 at `B₀ = 20 D`.

Source: Polynomial-PEPS manuscript, `07-assembly.tex:45–63`, with Theorem 5.2,
`04-compression.tex:137–175`, and the expansions of Proposition 7.1, `06-geometry.tex:25–30`. -/
def pepsLinkPrefactorOf (q : ℕ) (D : ℝ) : ℝ :=
  sumCompressionPrefactor (2 * protocolPatchBound protocolHoleRatio protocolMeshRatio)
    protocolLifetimeBound (max protocolCountConstant 0 * protocolLifetimeBound) q
    (max (protocolExpansionConstant protocolMeshRatio (adaptivePatchPrefactor q (20 * D))) 0)
    (protocolExpansionConstant protocolMeshRatio (adaptivePatchPrefactor q (20 * D)))

/-- The congestion `χ = 8 (2 c + 1) B deg` of Lemma 8.2 at `c = B = b_prot` and
`deg = 2 b_prot (b_prot - 1)`.

Source: Polynomial-PEPS manuscript, Lemma 8.2 `lem:routing`, `07-assembly.tex:122–162`, and
`eq:final-bond`, lines 164–172. -/
def pepsCongestion : ℕ :=
  8 * (2 * protocolLifetimeBound + 1) * protocolLifetimeBound *
    (2 * protocolLifetimeBound * (protocolLifetimeBound - 1))

/-- The congestion of Lemma 8.2 is `χ = 685013510424821760` (`07-assembly.tex:122–162`). -/
theorem pepsCongestion_eq : pepsCongestion = 685013510424821760 := by
  norm_num [pepsCongestion, protocolLifetimeBound]

/-- The constant `C = 1 + 2 C_N C_E + 2 C_E` of the error `‖σ - |Ω⟩⟨Ω|‖₁ ≤ C L⁻⁵` of the
compressed network, at the count constant `C_N = 5042` and the error constant
`C_E = protocolErrorConstant ν` of the protocol.

Source: Polynomial-PEPS manuscript, `eq:compressed-density`, `07-assembly.tex:45–63`. -/
def pepsNetworkErrorConstant : ℝ :=
  1 + (2 * (protocolCountConstant * protocolErrorConstant protocolMeshRatio) +
    2 * protocolErrorConstant protocolMeshRatio)

/-- The size threshold `L₀ = max ⌈max L_ang 1⌉ ⌈2 C⌉`: the threshold of Proposition 3.4 and the
size above which the network error `C L⁻⁵` is at most half of `L⁻¹`.

Source: Polynomial-PEPS manuscript, `07-assembly.tex:203–206`. -/
def pepsSizeThresholdOf (L_ang : ℝ) : ℕ :=
  max ⌈max L_ang 1⌉₊ ⌈2 * pepsNetworkErrorConstant⌉₊

/-- The bond exponent `k χ + 1` above the size threshold, with the link exponent `k` and the
congestion `χ`.

Source: Polynomial-PEPS manuscript, `eq:final-bond`, `07-assembly.tex:164–172`, and the choice
of the final constants, lines 197–214. -/
def pepsBondExponentOf (q : ℕ) (J Δ C_A D : ℝ) : ℝ :=
  (pepsLinkExponentOf q J Δ C_A D : ℝ) * pepsCongestion + 1

/-- The bond prefactor `max(C₁, 1) ^ χ` above the size threshold, with the link prefactor `C₁`
and the congestion `χ`.

Source: Polynomial-PEPS manuscript, `eq:final-bond`, `07-assembly.tex:164–172`. -/
def pepsLargeSizePrefactorOf (q : ℕ) (D : ℝ) : ℝ :=
  max (pepsLinkPrefactorOf q D) 1 ^ pepsCongestion

/-- The bond prefactor above the size threshold is positive (`07-assembly.tex:164–172`). -/
theorem pepsLargeSizePrefactorOf_pos (q : ℕ) (D : ℝ) : 0 < pepsLargeSizePrefactorOf q D :=
  pow_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _

/-- The bond exponent is positive (`07-assembly.tex:164–172`). -/
theorem pepsBondExponentOf_pos (q : ℕ) (J Δ C_A D : ℝ) : 0 < pepsBondExponentOf q J Δ C_A D := by
  unfold pepsBondExponentOf
  positivity

/-- **The polynomial PEPS approximation at given area-law and angular constants.** Fix `q ≥ 2`
and `J, Δ > 0`. Assume the square entropy area law of Proposition 2.1 with constant `C_A`, and
let `D ≥ 1` be an information scale with threshold `L_ang` of Proposition 3.4 at the clearance
`a₀ / 2`, diameter ratio `1`, at most `4` marked points and power `60`. Then every gapped unit
ground vector of a square Hamiltonian of side `L ≥ 2` with `pepsSizeThresholdOf L_ang ≤ L` has a
nonzero PEPS approximation with bond dimensions at most
`pepsLargeSizePrefactorOf q D * L ^ pepsBondExponentOf q J Δ C_A D` and phase-normalized error
at most `L⁻¹`.

The prefactor and the threshold do not depend on the area-law constant; only the exponent does.
The sizes below the threshold are covered by exact spanning-tree PEPS and an enlarged prefactor
(`07-assembly.tex:205–212`); that step is not part of this statement. Both hypotheses are inputs
of the proof of Theorem 1.1, not hypotheses of the theorem itself, which asserts only that the
constants exist.

Source: Polynomial-PEPS manuscript, the proof of Theorem 1.1 in §8, `07-assembly.tex:9–206`,
with Proposition 2.1 (`01-preliminaries.tex:39–58`), Proposition 3.4
(`02-information.tex:635–658`), Proposition 4.1 (`03-patches.tex:26–49`) and Proposition 7.1
(`06-geometry.tex:12–53`). -/
theorem polynomialPEPSApproximation_of_ratios {q : ℕ} (hq : 2 ≤ q) {J Δ : ℝ}
    (hJ : 0 < J) (hΔ : 0 < Δ) {C_A D L_ang : ℝ} (hA : SquareEntropyAreaLawAt q J Δ C_A)
    (hD1 : 1 ≤ D) (hD : IsAngularScale q J Δ (angularConstant / 2) 1 4 60 D L_ang) :
    ∀ L : ℕ, 2 ≤ L → pepsSizeThresholdOf L_ang ≤ L → ∀ h : SquareHamiltonian L q J,
      ∀ E₀ : ℝ, ∀ Ω : StateSpace L q, h.IsGappedGroundState E₀ Ω Δ →
        HasPEPSApproximation (pepsLargeSizePrefactorOf q D) (pepsBondExponentOf q J Δ C_A D)
          L q Ω := by
  have hB₀ : (0 : ℝ) < 20 * D := mul_pos (by norm_num) (lt_of_lt_of_le one_pos hD1)
  have hsupply : ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ,
      ∀ Ω : StateSpace L q, h.IsGappedGroundState E₀ Ω Δ →
        AdaptivePatchSupply (cellCenterPos L) Ω (20 * D) (adaptivePatchPrefactor q (20 * D))
          (adaptivePatchExponent q J Δ (20 * D) 60 C_A) 60 L :=
    fun L hL h E₀ Ω hΩ ↦ AdaptivePatchSupply.cellCenterPos
      (hA.adaptivePatchSupply hq hJ hΔ (B₀ := 20 * D) (p := 60) hB₀ (by norm_num) L hL h E₀ Ω hΩ)
  have hnet := dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt hq
    (largeSizeDyadicProtocol_of_angularScale hq hD1 hD (adaptivePatchPrefactor_pos q hB₀.le)
      hsupply le_rfl le_rfl le_rfl)
  intro L hL hL₀ h E₀ Ω hΩ
  have H := hasPEPSApproximation_of_dyadicOperatorNetworkAt hnet L hL hL₀ h E₀ Ω hΩ
  have hk : max ((pepsLinkExponentOf q J Δ C_A D : ℕ) : ℝ) 0 = pepsLinkExponentOf q J Δ C_A D :=
    max_eq_left (Nat.cast_nonneg _)
  rw [pepsBondExponentOf, ← hk]
  exact H

end TNLean.PEPS.Approximation
