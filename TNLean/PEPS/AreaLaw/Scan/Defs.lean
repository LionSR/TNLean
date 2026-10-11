/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib

/-!
# Data of the collar scan (Proposition 9.2)

This module fixes the scales of the collar scan and packages, for one replica count, the
finite data on which the scanner estimate (Proposition 9.2, `prop:scanner`) operates.

The scan itself (offsets, fill and charge rounds, histories) and its probabilistic geometry are
the content of Lemma 9.1 (`scanner:histories`); the transported states and their entropy and
energy estimates are Proposition 7.4 (`prop:transport`); the norm comparisons are
Proposition 8.1 (`prop:comparators`). Following the source, Proposition 9.2 *uses* those
results. Here their conclusions are recorded as explicit fields of `ScanRound` and `ScanData`;
each field cites the relevant source passage. The mass-`1/2` hypotheses on transported measures
are restricted to interior parameters; the norm comparisons retain their endpoint values.
The charge defect needs only AE strong measurability in the interior: its existing bound
then gives interval integrability, which suffices for the telescope and exact averaging.

**Scope restriction (inputs as hypotheses):** `ScanData` takes the conclusions of Lemma 9.1,
Propositions 7.4 and 8.1, and Lemmas 2.1 and 2.3 for one scan as fields instead of deriving them
from the scan geometry and the transported states, so every result stated over `ScanData` is
Proposition 9.2 restricted to those conclusions. Documented in
`docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## Abstraction of the transported states

For a terminal leaf `j` the source integrates a function of `θ` against
`m_s(u) du dμ_{σ_{j,u}}(θ)` (`06-transport.tex`, lines 407–420). That measure on the unit
sphere `Θ` of the one-copy space is recorded as one finite measure (`ScanRound.μOld`,
`ScanRound.μNew`), indexed by the replica count `k` and the common interpolation parameter `p`.
Its mass is `2s = 1/2` for `0 < p < 1`, where the source's terminal weights are positive
(`06-transport.tex`, lines 393–400). No mass equality is imposed at inactive terminal leaves
at the endpoints. Endpoint norm continuity and the integrated entropy inequality are retained.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`: scales `scanner:scales` (lines 32–41), test geometry
  `scanner:test-geometry` (lines 43–48), rounds and fronts (lines 83–154), Lemma 9.1
  (lines 195–221), Proposition 9.2 (lines 349–397) and its proof (lines 399–533).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open MeasureTheory

/-- The fixed exponents of the scan: `0 < ℓ < 1`, `0 < κ < μ < 1 - ℓ`
(`scanner:scales`, `08-scanner.tex`, line 41), together with the exponent `e` of the entropy
input, `0 < e < 1`, `κ ≤ e` (line 352), and `ν > 0` with `ε = n^{-ν}` (line 358). -/
structure ScannerExponents where
  /-- The collar-depth exponent: `L = ⌊n^{1-ℓ}⌋`. -/
  ell : ℝ
  /-- The charge-lookahead exponent: `D = ⌈n^κ⌉`. -/
  kappa : ℝ
  /-- The window exponent: `m = ⌊n^μ⌋`. -/
  mu : ℝ
  /-- The interpolation exponent: `ε = n^{-ν}`. -/
  nu : ℝ
  /-- The exponent of the entropy input `scanner:entropy-input`. -/
  e : ℝ
  ell_pos : 0 < ell
  ell_lt_one : ell < 1
  kappa_pos : 0 < kappa
  kappa_lt_mu : kappa < mu
  mu_lt_one_sub_ell : mu < 1 - ell
  nu_pos : 0 < nu
  e_pos : 0 < e
  e_lt_one : e < 1
  kappa_le_e : kappa ≤ e

namespace ScannerExponents

variable (X : ScannerExponents)

/-- Total collar depth `L = ⌊n^{1-ℓ}⌋` (`scanner:scales`, line 34). -/
noncomputable def L (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 - X.ell)⌋₊

/-- Window scale `m = ⌊n^μ⌋` (`scanner:scales`, line 35). -/
noncomputable def m (n : ℕ) : ℕ := ⌊(n : ℝ) ^ X.mu⌋₊

/-- Number of bands `K = ⌊L / (8m)⌋` (`scanner:scales`, line 36). -/
noncomputable def K (n : ℕ) : ℕ := X.L n / (8 * X.m n)

/-- Charge lookahead `D = ⌈n^κ⌉` (`scanner:scales`, line 37). -/
noncomputable def D (n : ℕ) : ℕ := ⌈(n : ℝ) ^ X.kappa⌉₊

/-- Per-band metric weight `a = W / K` for the total weight `W` (`scanner:scales`, line 38). -/
noncomputable def a (W : ℝ) (n : ℕ) : ℝ := W / X.K n

/-- Interpolation scale `ε = n^{-ν}` (line 358). -/
noncomputable def eps (n : ℕ) : ℝ := (n : ℝ) ^ (-X.nu)

/-- Number of rounds: `nm` fill rounds and `nm` charge rounds (lines 106–107). -/
noncomputable def rounds (n : ℕ) : ℕ := 2 * n * X.m n

/-- The defect density `δ_n = C_δ ε^{-1} (n^{e-μ} + a^{1/4} (log n)^{C_l})`
(`scanner:density-output`, lines 380–384), with its constants made explicit. -/
noncomputable def delta (W Cδ Cl : ℝ) (n : ℕ) : ℝ :=
  Cδ * (X.eps n)⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + X.a W n ^ (1 / 4 : ℝ) * Real.log n ^ Cl)

end ScannerExponents

/-- Rounds are interleaved with a fill first (lines 106–107), so round `r` is a charge round
exactly when `r` is odd. -/
def IsChargeRound (r : ℕ) : Prop := r % 2 = 1

instance (r : ℕ) : Decidable (IsChargeRound r) := inferInstanceAs (Decidable (_ = _))

/-- The `nm` charge rounds among the `2nm` rounds. -/
noncomputable def ScannerExponents.chargeRounds (X : ScannerExponents) (n : ℕ) :
    Finset (Fin (X.rounds n)) :=
  Finset.univ.filter fun r ↦ IsChargeRound r

/-- Constants of the cited inputs, fixed before the scale `n`. They depend only on the fixed
exponents, the entropy-input constant `C_e` (line 396) and the Hamiltonian parameters
(local dimension `q`, gap `g`); never on the domain. A single `C ≥ 1` and a single logarithmic
power `C_l` dominate all universal constants of Lemma 9.1 and Propositions 7.4 and 8.1. -/
structure ScanConstants where
  /-- A common upper constant. -/
  C : ℝ
  /-- A common logarithmic power. -/
  Cl : ℝ
  /-- The sampling constant `c` of Lemma 9.1(4) (line 217). -/
  c : ℝ
  /-- The entropy-input constant `C_e` of `scanner:entropy-input` (lines 353–357). -/
  Ce : ℝ
  /-- The local Hilbert dimension `q`. -/
  q : ℕ
  /-- The spectral gap `g` of the original Hamiltonian. -/
  g : ℝ
  one_le_C : 1 ≤ C
  Cl_nonneg : 0 ≤ Cl
  c_pos : 0 < c
  Ce_pos : 0 < Ce
  two_le_q : 2 ≤ q
  g_pos : 0 < g

/-- One round of the scan at a fixed scale: the old weighted history tree, its conditional
choice trees, the split structure of the labelled terms, and the entropies of moves
(`08-scanner.tex`, lines 145–154 and 416–440; `06-transport.tex`, lines 259–287 and 321–366).
The finite measures `μOld k p h`, `μNew k p h c` stand for `m_s(u) du dμ_{σ_{j,u}}(θ)` at the
old leaf `(h, old)` and the new leaf `(h, c, new)` (`06-transport.tex`, lines 392–420). -/
structure ScanRound (ι Θ : Type) [MeasurableSpace Θ] where
  /-- Old joint histories `h`. -/
  H : Type
  [instFintypeH : Fintype H]
  /-- Conditional choices `c ∈ 𝒞_h`. -/
  Ch : H → Type
  [instFintypeCh : ∀ h, Fintype (Ch h)]
  /-- Old-history weights `w_h`. -/
  w : H → ℝ
  /-- Conditional choice weights `q_{c|h}`. -/
  q : (h : H) → Ch h → ℝ
  /-- Good old histories (Lemma 9.1(4), lines 212–213). -/
  good : H → Prop
  /-- Term `i` splits at the old leaf `(h, old)`. -/
  splitOld : ι → H → Prop
  /-- Term `i` splits at the new leaf `(h, c, new)`. -/
  splitNew : ι → (h : H) → Ch h → Prop
  /-- `η_{i,h}(θ)` at an old leaf (lines 433–437). -/
  etaOld : ι → H → Θ → ℝ
  /-- `η_{i,j}(θ)` at a new leaf (`06-transport.tex`, lines 355–360). -/
  etaNew : ι → (h : H) → Ch h → Θ → ℝ
  /-- The choice-averaged move entropy `∑_{c,g} q_{c|h} η_{h,c,g}(θ)` of
  `transport:entropy-gain` (`06-transport.tex`, lines 407–409). -/
  choiceGain : H → Θ → ℝ
  /-- The leaf measure at an old leaf, for replica count `k` and parameter `p`. -/
  μOld : ℕ → ℝ → H → Measure Θ
  /-- The leaf measure at a new leaf, for replica count `k` and parameter `p`. -/
  μNew : ℕ → ℝ → (h : H) → Ch h → Measure Θ
  /-- `log N(p)²` at replica count `k` (`transport:filtered-vector`). -/
  logNormSq : ℕ → ℝ → ℝ
  /-- The replica mean energy `⟨v(p), \bar{\widetilde H} v(p)⟩` at replica count `k`. -/
  meanEnergy : ℕ → ℝ → ℝ

attribute [instance] ScanRound.instFintypeH ScanRound.instFintypeCh

namespace ScanRound

variable {ι Θ : Type} [MeasurableSpace Θ] [Fintype ι] (S : ScanRound ι Θ)

open Classical in
/-- The entropy cost `𝒬(p)` of the old splits (`scanner:Q-definition`, lines 424–429). -/
noncomputable def chargeDefect (k : ℕ) (p : ℝ) : ℝ :=
  ∑ h, if S.good h then
    S.w h * ∑ i, if S.splitOld i h then ∫ θ, S.etaOld i h θ ∂(S.μOld k p h) else 0
  else 0

open Classical in
/-- The split weight `W_i(p) = ∑_{j ∈ 𝒥_i} π_j`, with terminal weights `(1-p) w_h` and
`p w_h q_{c|h}` (`transport:terminal-weights` and `transport:replica-energy`). -/
noncomputable def splitWeight (p : ℝ) (i : ι) : ℝ :=
  (∑ h, if S.splitOld i h then (1 - p) * S.w h else 0) +
    ∑ h, ∑ c, if S.splitNew i h c then p * S.w h * S.q h c else 0

open Classical in
/-- The leaf sum `∑_{j ∈ 𝒥_i} π_j ∫ η_{i,j}^{1/8}` of `transport:energy` for one term. -/
noncomputable def termEnergy (k : ℕ) (p : ℝ) (i : ι) : ℝ :=
  (∑ h, if S.splitOld i h then
      (1 - p) * S.w h * ∫ θ, S.etaOld i h θ ^ (1 / 8 : ℝ) ∂(S.μOld k p h) else 0) +
    ∑ h, ∑ c, if S.splitNew i h c then
      p * S.w h * S.q h c * ∫ θ, S.etaNew i h c θ ^ (1 / 8 : ℝ) ∂(S.μNew k p h c) else 0

/-- The energy sum `∑_i W_i(p) ∑_{j ∈ 𝒥_i} π_j ∫ η_{i,j}^{1/8}` of `transport:energy`
(`06-transport.tex`, lines 416–420). -/
noncomputable def energySum (k : ℕ) (p : ℝ) : ℝ :=
  ∑ i, S.splitWeight p i * S.termEnergy k p i

/-- The entropy-gain integrand `∑_h w_h ∫ ∑_c q_{c|h} η_{h,c,g}` of `transport:entropy-gain`. -/
noncomputable def choiceGainSum (k : ℕ) (p : ℝ) : ℝ :=
  ∑ h, S.w h * ∫ θ, S.choiceGain h θ ∂(S.μOld k p h)

open Classical in
/-- Total weight of the old histories that are not good. -/
noncomputable def badWeight : ℝ := ∑ h, if S.good h then 0 else S.w h

end ScanRound

/-- Elementary consequences of `scanner:scales` used throughout the proof of Proposition 9.2,
valid for all sufficiently large `n` with one constant `C₁` (lines 42, 52, 469, 480, 519–520). -/
structure ScaleFacts (X : ScannerExponents) (n : ℕ) (C₁ : ℝ) : Prop where
  two_le_n : 2 ≤ n
  one_le_K : 1 ≤ X.K n
  one_le_m : 1 ≤ X.m n
  one_le_D : 1 ≤ X.D n
  L_le_n : X.L n ≤ n
  eps_pos : 0 < X.eps n
  eps_lt_one : X.eps n < 1
  one_le_C₁ : 1 ≤ C₁
  /-- `n^e / m ≤ C₁ n^{e-μ}`, since `m ≍ n^μ` (line 480). -/
  pow_e_div_m_le : (n : ℝ) ^ X.e / X.m n ≤ C₁ * (n : ℝ) ^ (X.e - X.mu)
  /-- `D ≤ C₁ n^e`, since `κ ≤ e` (line 469). -/
  D_le : (X.D n : ℝ) ≤ C₁ * (n : ℝ) ^ X.e
  /-- `n D² / (m K) ≤ C₁ n^ℓ D²` (lines 519–520). -/
  coefficient_le :
    n * (X.D n : ℝ) ^ 2 / (X.m n * X.K n) ≤ C₁ * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2

open Classical in
/-- The finite data of the collar scan at scale `n`, for all replica counts `k`, together with
the conclusions of the results that Proposition 9.2 uses (`08-scanner.tex`, lines 399–533).

The complete finite system, the scan, and all auxiliary dimensions are fixed before `k → ∞`
(lines 393–395): every field except the `k`-indexed families is independent of `k`. -/
structure ScanData (X : ScannerExponents) (κ : ScanConstants) (n : ℕ) where
  /-- The labelled terms of the truncated Hamiltonian. -/
  ι : Type
  [instFintypeι : Fintype ι]
  /-- The unit sphere of the one-copy space. -/
  Θ : Type
  [instMeasΘ : MeasurableSpace Θ]
  /-- The rounds of the scan. -/
  round : Fin (X.rounds n) → ScanRound ι Θ
  /-- The total scalar metric weight `W = aK ≥ 1` of the scan (`scanner:scales`, lines 38–41).
  It is part of the scan at scale `n`, not a fixed exponent: the source later takes `W = n^ω`
  (`scanner:final-parameters`, line 843), so no constant may depend on it. -/
  W : ℝ
  /-- `W ≥ 1` (`scanner:scales`, line 41). -/
  one_le_W : 1 ≤ W
  /- Truncated Hamiltonian (Proposition 4.5 as used in lines 49–59). -/
  /-- Ground energy `\widetilde E_0`. -/
  E0 : ℝ
  /-- Spectral gap `\widetilde g`. -/
  gap : ℝ
  E0_nonneg : 0 ≤ E0
  E0_le : E0 ≤ (n : ℝ) ^ (-1000 : ℝ)
  half_g_le_gap : κ.g / 2 ≤ gap
  /- Entropy input (`scanner:entropy-input`, lines 353–357) and its transfer to the truncated
  ground state (lines 400–404, Lemma 2.1 `lem:continuity`). -/
  /-- `S_Ω(X)`. -/
  SX : ℝ
  /-- `S_{\widetilde Ω}(X)`. -/
  SXt : ℝ
  /-- `S_Ω(Q_j)`. -/
  SQ : ℕ → ℝ
  /-- `S_{\widetilde Ω}(Q_j)`. -/
  SQt : ℕ → ℝ
  entropy_input_X : SX ≤ κ.Ce * (n : ℝ) ^ (1 + X.e)
  entropy_input_Q : ∀ j ≤ X.L n, SQ j ≤ κ.Ce * (n * (X.L n : ℝ) ^ X.e + n)
  /-- Half the trace distance between `Ω` and `\widetilde Ω` (line 401). -/
  traceDist : ℝ
  traceDist_nonneg : 0 ≤ traceDist
  traceDist_le : traceDist ≤ (n : ℝ) ^ (-500 : ℝ)
  /-- Lemma 2.1 on the target, whose Hilbert space has `log`-dimension at most `C n² log q`. -/
  continuity_X : |SXt - SX| ≤ κ.C * √traceDist * (1 + κ.C * n ^ 2 * Real.log κ.q)
  /-- Lemma 2.1 on the shell sets `Q_j`. -/
  continuity_Q : ∀ j ≤ X.L n,
    |SQt j - SQ j| ≤ κ.C * √traceDist * (1 + κ.C * n ^ 2 * Real.log κ.q)
  /- Comparator data (Proposition 8.1, `07-comparators.tex`, lines 36–70). -/
  /-- `d_* = |E|`. -/
  dstar : ℝ
  /-- `z = ∑_{i ∈ E} p_i`. -/
  z : ℝ
  /-- Typical width `w`. -/
  width : ℝ
  width_eq : width = (n : ℝ) ^ (3 / 5 : ℝ)
  dstar_pos : 0 < dstar
  z_pos : 0 < z
  z_le_one : z ≤ 1
  /-- Width `n^{3/5}` has failure mass at most `n^{-100}` (Lemma 2.3, lines 411–414). -/
  one_sub_le_z : 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z
  /-- `comparator:typical-entropies`. -/
  log_dstar_le : |Real.log dstar - SXt| ≤ width + |Real.log z|
  /-- The shell entropy bound `B_sh` of `comparator:prefix-data`. -/
  Bsh : ℝ
  /-- The matched prefixes are shell sets `Q_j` up to a partial last depth row
  (Lemma 9.1(2), lines 403–404). -/
  Bsh_le : ∃ j ≤ X.L n, Bsh ≤ SQt j + n * Real.log κ.q
  /-- The mismatch bound `B_exc` of `comparator:prefix-data`. -/
  Bexc : ℝ
  /-- Matched prefixes differ by at most `C n D` sites (Lemma 9.1(2), line 206). -/
  Bexc_le : Bexc ≤ 1 + κ.C * n * X.D n * Real.log κ.q
  /-- Graph radius `r₀` of every splitting support, `r₀ = ⌈C log² n⌉` (line 49). -/
  r0 : ℕ
  r0_le : (r0 : ℝ) ≤ κ.C * Real.log n ^ 2 + 1
  /-- Number of crossing supports at a status cut. -/
  crossCount : ℕ
  /-- Status cuts have `O(nD)` edges, each crossing anchor lies within `r₀` of one
  (lines 405–408). -/
  crossCount_le : (crossCount : ℝ) ≤ κ.C * n * X.D n * (r0 + 1) ^ 2
  /-- The marginal-tail parameter `𝓑` of Lemma 2.3 (`lem:tail`). -/
  Bmarg : ℝ
  /-- `𝓑 = 1 + ∑ log²(e dᵢ)` with `dᵢ ≤ q^{C(1+r₀)²}` (lines 406–409). -/
  Bmarg_le : Bmarg ≤ 1 + crossCount * (1 + κ.C * (r0 + 1) ^ 2 * Real.log κ.q) ^ 2
  /- Replica remainders (Proposition 7.4, lines 421–433 of `06-transport.tex`). -/
  /-- The `o_k(1)` remainder, uniform in rounds, parameters, and replica states. -/
  rem : ℕ → ℝ
  rem_nonneg : ∀ k, 0 ≤ rem k
  tendsto_rem : Filter.Tendsto rem Filter.atTop (nhds 0)
  /-- `β_k = O_fixed(log(k+2))`. -/
  β : ℕ → ℝ
  Cβ : ℝ
  β_nonneg : ∀ k, 0 ≤ β k
  β_le : ∀ k, β k ≤ Cβ * Real.log (k + 2)
  /- Lemma 9.1 (`scanner:histories`, lines 195–221). -/
  w_nonneg : ∀ r h, 0 ≤ (round r).w h
  q_nonneg : ∀ r h c, 0 ≤ (round r).q h c
  sum_w : ∀ r, ∑ h, (round r).w h = 1
  sum_q : ∀ r h, ∑ c, (round r).q h c = 1
  /-- Lemma 9.1(3): split weight at most `CD/m`. -/
  splitWeight_le : ∀ r, ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ i,
    (round r).splitWeight p i ≤ κ.C * X.D n / X.m n
  /-- Lemma 9.1(2): at most `CKnD` split terms at every old leaf. -/
  card_splitOld_le : ∀ r h, ((Finset.univ.filter fun i ↦ (round r).splitOld i h).card : ℝ) ≤
    κ.C * X.K n * n * X.D n
  /-- Lemma 9.1(2): at most `CKnD` split terms at every new leaf. -/
  card_splitNew_le : ∀ r h c,
    ((Finset.univ.filter fun i ↦ (round r).splitNew i h c).card : ℝ) ≤ κ.C * X.K n * n * X.D n
  /-- Lemma 9.1(4) with the fixed tail power `M = 200`. -/
  badWeight_le : ∀ r, (round r).badWeight ≤ (n : ℝ) ^ (-200 : ℝ)
  /-- Lemma 9.1(4) and lines 442–444: on a good old history at a charge round each split term
  is sampled with probability at least `c/(nD)`, and its move has entropy `η_{i,h}`. -/
  sampling : ∀ r : Fin (X.rounds n), IsChargeRound r → ∀ h, (round r).good h → ∀ θ,
    κ.c / (n * X.D n) * ∑ i, (if (round r).splitOld i h then (round r).etaOld i h θ else 0) ≤
      (round r).choiceGain h θ
  /- Move entropies (lines 434–440). -/
  etaOld_nonneg : ∀ r i h θ, 0 ≤ (round r).etaOld i h θ
  etaOld_le : ∀ r i h θ, (round r).etaOld i h θ ≤ κ.C * Real.log n ^ κ.Cl
  etaNew_nonneg : ∀ r i h c θ, 0 ≤ (round r).etaNew i h c θ
  etaNew_le : ∀ r i h c θ, (round r).etaNew i h c θ ≤ κ.C * Real.log n ^ κ.Cl
  measurable_etaOld : ∀ r i h, Measurable ((round r).etaOld i h)
  measurable_etaNew : ∀ r i h c, Measurable ((round r).etaNew i h c)
  choiceGain_nonneg : ∀ r h θ, 0 ≤ (round r).choiceGain h θ
  measurable_choiceGain : ∀ r h, Measurable ((round r).choiceGain h)
  /-- The choice-averaged gain sums one move entropy per band, each bounded by
  `C (log n)^{C_l}` (lines 434–440), so it is at most `C K (log n)^{C_l}`. -/
  choiceGain_le : ∀ r h θ, (round r).choiceGain h θ ≤ κ.C * X.K n * Real.log n ^ κ.Cl
  /- Leaf measures: for `0 < p < 1`, `m_s(u) du dμ_σ` has mass `2s = 1/2`
  (`06-transport.tex`, lines 393–400; `08-scanner.tex`, line 440). -/
  isFiniteMeasure_μOld : ∀ r k p h, IsFiniteMeasure ((round r).μOld k p h)
  isFiniteMeasure_μNew : ∀ r k p h c, IsFiniteMeasure ((round r).μNew k p h c)
  /-- The old-leaf measure has mass `1/2` for `0 < p < 1`
  (`06-transport.tex`, lines 393–400; `08-scanner.tex`, line 440). -/
  μOld_real_univ : ∀ r k, ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ h,
    ((round r).μOld k p h).real Set.univ = 1 / 2
  /-- The new-leaf measure has mass `1/2` for `0 < p < 1`
  (`06-transport.tex`, lines 393–400; `08-scanner.tex`, line 440). -/
  μNew_real_univ : ∀ r k, ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ h c,
    ((round r).μNew k p h c).real Set.univ = 1 / 2
  /-- AE strong measurability of the charge defect in the interior parameter, sufficient for
  bounded integration and exact averaging (`08-scanner.tex`, lines 457–490). -/
  aestronglyMeasurable_chargeDefect : ∀ r k,
    AEStronglyMeasurable ((round r).chargeDefect k) (volume.restrict (Set.Ioo 0 1))
  /- Proposition 7.4 (`prop:transport`, `06-transport.tex`, lines 377–433). -/
  continuousOn_logNormSq : ∀ r k, ContinuousOn ((round r).logNormSq k) (Set.Icc 0 1)
  differentiableOn_logNormSq : ∀ r k, DifferentiableOn ℝ ((round r).logNormSq k) (Set.Ioo 0 1)
  /-- `transport:entropy-gain`, with the band count `K` and `ℓ = C (log n)^{C_l}`. -/
  entropy_gain : ∀ r k, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
    k * X.a W n * (round r).choiceGainSum k p
        - κ.C * k * X.a W n * X.K n * X.a W n ^ (1 / 4 : ℝ) * Real.log n ^ κ.Cl - β k ≤
      -deriv ((round r).logNormSq k) p
  /-- `transport:energy`, using that `pre` is a mean-energy eigenvector of eigenvalue
  `\widetilde E_0` (`comparator:prevector`). -/
  energy : ∀ r k, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
    (round r).meanEnergy k p ≤
      2 * E0 + κ.C * X.a W n ^ 2 * Real.log n ^ κ.Cl * (round r).energySum k p + rem k
  /- Schedule (lines 145–154, 457–461) and the rough upper comparison at the end
  (`comparator:rough-upper`, lines 462–467). -/
  /-- Adjacent endpoint metrics agree. -/
  logNormSq_succ : ∀ (r : Fin (X.rounds n)) (hr : r.val + 1 < X.rounds n) k,
    (round ⟨r.val + 1, hr⟩).logNormSq k 0 = (round r).logNormSq k 1
  /-- Initially `-log N² ≥ -β_k` (`replicas:leaf-floor`, `‖pre‖ ≤ 1`, lines 459–461). -/
  logNormSq_init : ∀ (r : Fin (X.rounds n)), r.val = 0 → ∀ k, (round r).logNormSq k 0 ≤ β k
  /-- `comparator:rough-upper` at the last endpoint, `s = 1/4`. -/
  logNormSq_final : ∀ (r : Fin (X.rounds n)), r.val + 1 = X.rounds n → ∀ k, 1 ≤ k →
    -(round r).logNormSq k 1 / k ≤
      2 * Real.log dstar - Real.log z + 2 * (1 / 4) * W * (2 * Bsh / z + 2 * Bexc) + rem k

attribute [instance] ScanData.instFintypeι ScanData.instMeasΘ

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants} {n : ℕ} (S : ScanData X κ n)

/-- The right side of `comparator:rough-upper` without its remainder. -/
noncomputable def terminalBound : ℝ :=
  2 * Real.log S.dstar - Real.log S.z + 2 * (1 / 4) * S.W * (2 * S.Bsh / S.z + 2 * S.Bexc)

/-- The defect energy `E_def = (⟨v, \bar{\widetilde H} v⟩ - \widetilde E_0) / \widetilde g`
(lines 366–369). -/
noncomputable def defectEnergy (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) : ℝ :=
  ((S.round r).meanEnergy k p - S.E0) / S.gap

/-- The integrated entropy inequality at replica count `k`: the entropy gains of
`scanner:charge-gain` integrated over every full round, with the charge integrals restricted to
`[ε/2, ε]`, the telescoped left side bounded by the initial floor and the terminal rough upper
comparison (lines 457–475), before normalization. -/
def IntegratedChargeBound (k : ℕ) : Prop :=
  k * X.a S.W n * (κ.c / (n * X.D n)) *
      ∑ r ∈ X.chargeRounds n, ∫ p in (X.eps n / 2)..(X.eps n), (S.round r).chargeDefect k p ≤
    S.β k + k * (S.terminalBound + S.rem k) +
      X.rounds n *
        (κ.C * k * X.a S.W n * X.K n * X.a S.W n ^ (1 / 4 : ℝ) * Real.log n ^ κ.Cl + S.β k)

end ScanData

end TNLean.PEPS.AreaLaw.Scan
