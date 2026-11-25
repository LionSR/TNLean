/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.GateExpansion.DensityError
import TNLean.Network.SampledApproximation.ApproximateSampledNetworkApproximation
import TNLean.Network.SampledApproximation.ActualNetworkResourceCoupling

/-!
# Uniform bounds for sampled approximations supplied at a fixed precision

Fix the polynomial bounds for the number of gates and the physical dimensions,
and fix polynomial bounds for the monomial and coefficient counts at every
integer precision. For a requested real exponent, one integer precision and
one pair of polynomial constants suffice for every size at least two. The
comparison density is formed from the original gate operators, with their
discarded outputs traced out and without normalization.

This is the uniform implication for an expansion supplied at the selected
precision. The assertion that such expansions exist for an original family
at every fixed precision is a separate hypothesis of the source theorem.
The exterior scalar is retained here; its absorption into one existing party
is a separate algebraic identity.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229, 565–588 and 590–600.
-/

noncomputable section
open QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal
namespace TNLean.Network

/-- The prefactor `C_branch ² + C_sample` of the link alphabets of the sampled
network, for arity and lifetime bound `b`, at most `r` pair effects per
monomial, gate-count constant `C_N`, physical-dimension constant `C_D`,
monomial-count constant `C_K` and coefficient-sum constant `C_B`. Here
`C_branch = C_K (64 C_N² (r C_B)² + 2) ^ r` bounds the label links and
`C_sample = 64 C_sources² (C_B ^ (4 b) C_D ⁴)² + 2`, with
`C_sources = max 1 (C_N · b(b-1)/2)`, bounds the sample links.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 61–67
(at most `K m ^ r` monomials), 343–344 (`Q = B ^ (4 b) d ⁴`), 552–557
(`k` with `Q / √k ≤ ε / (8 N)`) and 565–585 (label and sample links). -/
noncomputable def sampledNetworkPrefactor (r b : ℕ) (C_N C_D C_K C_B : ℝ) : ℝ :=
  (C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_B) ^ 2 + 2) ^ r) ^ 2 +
    (64 * max 1 (C_N * (b.choose 2 : ℝ)) ^ 2 * (C_B ^ (4 * b) * C_D ^ 4) ^ 2 + 2)

/-- The exponent of the link alphabets of the sampled network,
`max (2 (u + 2 r (n + s + t))) (2 (n + 4 b s + 4 d + t))` with `t = ⌈p⌉`.
The first entry bounds the label links of dimension `|Ξ|²`, `|Ξ| ≤ K m ^ r`;
the second bounds the sample links of dimension `k = ⌈(8 N Q / ε)²⌉`, with
`Q = B ^ (4 b) D ⁴` and `ε = L ^ (-t)`. Here `n`, `d`, `u` and `s` are the
exponents of the gate count, physical dimensions, monomial count and
coefficient sum.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 61–67,
202–204, 343–344, 366–367, 552–557 and 565–585. -/
noncomputable def sampledNetworkExponent (r b n d u s : ℕ) (p : ℝ) : ℕ :=
  max (2 * (u + 2 * r * (n + s + ⌈p⌉₊))) (2 * (n + 4 * b * s + 4 * d + ⌈p⌉₊))

/-- The prefactor of the sampled network is positive
(`04-compression.tex`, lines 565–585). -/
theorem sampledNetworkPrefactor_pos (r b : ℕ) (C_N C_D C_K C_B : ℝ) :
    0 < sampledNetworkPrefactor r b C_N C_D C_K C_B := by
  unfold sampledNetworkPrefactor
  positivity

/-- The exponent of the sampled network is positive for a positive accuracy
exponent (`04-compression.tex`, lines 565–585). -/
theorem sampledNetworkExponent_pos (r b n d u s : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < sampledNetworkExponent r b n d u s p := by
  have ht : 0 < ⌈p⌉₊ := Nat.succ_le_iff.mp (Nat.one_le_ceil_iff.mpr hp)
  unfold sampledNetworkExponent
  omega

end TNLean.Network

namespace QuantumCircuit.Party.EffectCircuit
open TNLean.Network ManyBody
attribute [local instance] Classical.propDecidable

/-- Uniform original resource bounds give a single polynomial bound for all
actual sampled alphabets, together with the full physical trace-norm error,
constant incidence, and the common-original-gate property. The alphabets are
at most `C_p * L ^ α` for every `C_p` at least `sampledNetworkPrefactor` and
every `α` at least `sampledNetworkExponent`. All constants and the local
precision are fixed before the size or a particular circuit is chosen. This
implication applies to expansions supplied at that precision; it does not
assert their availability for an original family.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
565–588 and 590–600. -/
theorem uniform_sampled_approximate_network_bounds_of_le
    (r b n d : ℕ) (C_N C_D : ℝ) (hCN : 1 ≤ C_N)
    (C_K C_B : ℝ) (u s : ℕ) (hCK : 0 ≤ C_K) (hCB : 0 ≤ C_B)
    (p : ℝ) {C_p : ℝ} {α : ℕ}
    (hC : sampledNetworkPrefactor r b C_N C_D C_K C_B ≤ C_p)
    (hα : sampledNetworkExponent r b n d u s p ≤ α) :
    let t := ⌈p⌉₊
    let q := n + t + ⌈16 * C_N⌉₊
    ∀ (L : ℝ) (hL : 2 ≤ L),
    ∀ (P : Type) [Fintype P] [DecidableEq P]
      (X : P → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
      (φ : ∀ j, EuclideanSpace ℂ (X j)) (hφ : ∀ j, ‖φ j‖ = 1)
      (physicalDim : P → ℕ) (V : P → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]
      (w : EffectCircuit X (physicalSystem physicalDim V)) (G : w.GateMaps)
      (K : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
      (hb : w.IsExpansionBounded r (B : ℝ))
      (hmonomial : ∀ g, w.monomialCount g ≤ K)
      (harity : ∀ g, (w.participants g).card ≤ b)
      (hlifetime : ∀ j, w.participationCount j ≤ b)
      (hphysical : ∀ j, (physicalDim j : ℝ≥0) ≤ D)
      (hK : (K : ℝ) ≤ C_K * L ^ u)
      (hN : (w.numGates : ℝ) ≤ C_N * L ^ n)
      (hBB : (B : ℝ) ≤ C_B * L ^ s)
      (hDD : (D : ℝ) ≤ C_D * L ^ d)
      (happrox : w.IsGateApproximation (L ^ q)⁻¹ G),
      let ε := (L ^ t)⁻¹
      let hε : 0 < ε := by positivity
      let hbudget : w.IsGateApproximation (sourceGateBudget (ε / 2) w.numGates) G := by
        have hprecision : w.IsGateApproximation
            (L ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * C_N⌉₊))⁻¹ G := by
          simpa only [Nat.ceil_natCast] using happrox
        simpa only [Real.rpow_neg (by linarith : 0 ≤ L), Real.rpow_natCast] using
          w.isGateApproximation_budget_of_power_bound G L C_N (t : ℝ)
            w.numGates n hL hCN hN hprecision
      let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) _).le G hbudget
      let hbW := w.isExpansionBounded_rescaledOriginal
        (sourceGateBudget_pos (half_pos hε) _).le G hbudget hb
      let R := W.replacement (sourceGateBudget_pos hε w.numGates) hbW
      let k := binomialSampleCount (max 1 (Fintype.card R.sourceLocations))
        ((B : ℝ) ^ (4 * b) * (D : ℝ) ^ 4) ε
      let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun j x ↦ φ j x)
      ∃ T : (j : P) → DistributedOperatorContraction.GateLabelsAt
          (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1)
          (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) j →
          (DistributedOperatorContraction.SampleAt
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) j → Fin k) →
          Matrix (Fin (physicalDim j)) (Fin (physicalDim j)) ℂ,
        Matrix.rectangularTraceNorm
          ((R.emptyGateScalar * conj R.emptyGateScalar) •
            DistributedOperatorContraction.contractedOperator
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
              (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
              (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k
              (DistributedOperatorContraction.densityPairCoefficient
                (Gate := R.nonemptyGateLocations)
                (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
                (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
                (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card)) T -
            w.physicalDensityWithGateMaps G (physicalReadout physicalDim V) ψ) ≤ L ^ (-p) ∧
        (∀ e : DistributedOperatorContraction.Link
          (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
          (Fintype.card (DistributedOperatorContraction.alphabet
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
            (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤ C_p * L ^ α) ∧
        (∀ j, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) j).card ≤
            2 * b * (b - 1)) ∧
        (∀ e : DistributedOperatorContraction.Link
          (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
          ∀ j l, j ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
            l ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
            ∃ g : w.gateLocations, j ∈ w.participants g ∧ l ∈ w.participants g) := by
  classical
  intro t q L hL P _ _ X _ _ φ hφ physicalDim V _ _ w G K B D hB hD
    hb hmonomial harity hlifetime hphysical hK hN hBB hDD happrox
    ε hε hbudget W hbW R k ψ
  have hLone : 1 ≤ L := le_trans (by norm_num) hL
  have hsmall : ε ≤ L ^ (-p) := by
    calc
      ε = L ^ (-(t : ℝ)) := by
        dsimp [ε]
        rw [Real.rpow_neg (by linarith : 0 ≤ L), Real.rpow_natCast]
      _ ≤ L ^ (-p) := Real.rpow_le_rpow_of_exponent_le hLone
        (neg_le_neg (Nat.le_ceil p))
  have hcountW : W.nonprivateCount ≤ w.numGates :=
    (w.nonprivateCount_rescaledOriginal _ G hbudget).le
  have harityW : ∀ g : W.nonprivateLocations, (W.participants g).card ≤ b := by
    intro g
    rw [w.participants_rescaledOriginal _ G hbudget g]
    exact harity _
  have hlifetimeW : ∀ j, W.participation j ≤ b := by
    intro j
    rw [w.participation_rescaledOriginal _ G hbudget j, PartyCircuit.natCard_participants_mem]
    exact hlifetime j
  have hK_W := w.isMonomialBounded_rescaledOriginal
    (sourceGateBudget_pos (half_pos hε) w.numGates).le G hbudget hmonomial
  have hdim := W.card_physicalFirstDensityAlphabet_le_power
    K r w.numGates b b (B : ℝ) (D : ℝ) L C_K C_N C_B C_D
    u n s d t hbW hK_W harityW hcountW hLone hCK hCN hCB
    B.coe_nonneg D.coe_nonneg hK hN hBB hDD (sourceGateBudget_pos hε w.numGates)
  have hinc := W.card_incidentPhysicalFirstDensityLinks_le
    (sourceGateBudget_pos hε w.numGates) hbW harityW hlifetimeW
  have hlocal := W.exists_original_gate_of_physicalFirst_density_link
    (sourceGateBudget_pos hε w.numGates) hbW
  have hεone : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hLone)
  obtain ⟨lam, E, F, _hframes, ω, hω⟩ :=
    w.exists_sampled_contractedOperator_approximate_error_le φ hφ physicalDim V G B D hB hD hb
      le_rfl hlifetime hphysical ε hε hεone hbudget
  dsimp only at hω hdim hinc hlocal
  refine ⟨_, hω.trans hsmall, ?_, hinc, ?_⟩
  · intro e
    have he : _ ≤ sampledNetworkPrefactor r b C_N C_D C_K C_B *
        L ^ sampledNetworkExponent r b n d u s p := hdim e
    exact he.trans (mul_le_mul hC (pow_le_pow_right₀ hLone hα) (by positivity)
      ((sampledNetworkPrefactor_pos r b C_N C_D C_K C_B).le.trans hC))
  · intro e j l hj hl
    obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
    refine ⟨w.rescaledLocationsEquiv _ G hbudget g, ?_⟩
    have hpart := w.participants_rescaledOriginal _ G hbudget g
    exact ⟨hpart ▸ hjg, hpart ▸ hlg⟩

/-- Uniform original resource bounds give a single polynomial bound for all
actual sampled alphabets, together with the full physical trace-norm error,
constant incidence, and the common-original-gate property. All constants and
the local precision are fixed before the size or a particular circuit is
chosen. The constants are `sampledNetworkPrefactor` and
`sampledNetworkExponent`, as in
`uniform_sampled_approximate_network_bounds_of_le`. This implication applies
to expansions supplied at that precision; it does not assert their
availability for an original family.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
565–588 and 590–600. -/
theorem exists_uniform_sampled_approximate_network_bounds
    (r b n d : ℕ) (C_N C_D : ℝ) (hCN : 1 ≤ C_N)
    (C_K C_B : ℕ → ℝ) (u s : ℕ → ℕ)
    (hCK : ∀ q, 0 ≤ C_K q) (hCB : ∀ q, 0 ≤ C_B q)
    (p : ℝ) (hp : 0 < p) :
    let t := ⌈p⌉₊
    let q := n + t + ⌈16 * C_N⌉₊
    ∃ (C : ℝ) (α : ℕ), 0 ≤ C ∧ 0 < α ∧
      ∀ (L : ℝ) (hL : 2 ≤ L),
      ∀ (P : Type) [Fintype P] [DecidableEq P]
        (X : P → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
        (φ : ∀ j, EuclideanSpace ℂ (X j)) (hφ : ∀ j, ‖φ j‖ = 1)
        (physicalDim : P → ℕ) (V : P → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]
        (w : EffectCircuit X (physicalSystem physicalDim V)) (G : w.GateMaps)
        (K : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
        (hb : w.IsExpansionBounded r (B : ℝ))
        (hmonomial : ∀ g, w.monomialCount g ≤ K)
        (harity : ∀ g, (w.participants g).card ≤ b)
        (hlifetime : ∀ j, w.participationCount j ≤ b)
        (hphysical : ∀ j, (physicalDim j : ℝ≥0) ≤ D)
        (hK : (K : ℝ) ≤ C_K q * L ^ (u q))
        (hN : (w.numGates : ℝ) ≤ C_N * L ^ n)
        (hBB : (B : ℝ) ≤ C_B q * L ^ (s q))
        (hDD : (D : ℝ) ≤ C_D * L ^ d)
        (happrox : w.IsGateApproximation (L ^ q)⁻¹ G),
        let ε := (L ^ t)⁻¹
        let hε : 0 < ε := by positivity
        let hbudget : w.IsGateApproximation (sourceGateBudget (ε / 2) w.numGates) G := by
          have hprecision : w.IsGateApproximation
              (L ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * C_N⌉₊))⁻¹ G := by
            simpa only [Nat.ceil_natCast] using happrox
          simpa only [Real.rpow_neg (by linarith : 0 ≤ L), Real.rpow_natCast] using
            w.isGateApproximation_budget_of_power_bound G L C_N (t : ℝ)
              w.numGates n hL hCN hN hprecision
        let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) _).le G hbudget
        let hbW := w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) _).le G hbudget hb
        let R := W.replacement (sourceGateBudget_pos hε w.numGates) hbW
        let k := binomialSampleCount (max 1 (Fintype.card R.sourceLocations))
          ((B : ℝ) ^ (4 * b) * (D : ℝ) ^ 4) ε
        let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun j x ↦ φ j x)
        ∃ T : (j : P) → DistributedOperatorContraction.GateLabelsAt
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1)
            (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) j →
            (DistributedOperatorContraction.SampleAt
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) j → Fin k) →
            Matrix (Fin (physicalDim j)) (Fin (physicalDim j)) ℂ,
          Matrix.rectangularTraceNorm
            ((R.emptyGateScalar * conj R.emptyGateScalar) •
              DistributedOperatorContraction.contractedOperator
                (Finset.univ : Finset R.nonemptyGateLocations)
                (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
                (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
                (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k
                (DistributedOperatorContraction.densityPairCoefficient
                  (Gate := R.nonemptyGateLocations)
                  (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
                  (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
                  (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card)) T -
              w.physicalDensityWithGateMaps G (physicalReadout physicalDim V) ψ) ≤ L ^ (-p) ∧
          (∀ e : DistributedOperatorContraction.Link
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
            (Fintype.card (DistributedOperatorContraction.alphabet
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
              (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤ C * L ^ α) ∧
          (∀ j, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) j).card ≤
              2 * b * (b - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
            ∀ j l, j ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
              l ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
              ∃ g : w.gateLocations, j ∈ w.participants g ∧ l ∈ w.participants g) := by
  intro t q
  exact ⟨sampledNetworkPrefactor r b C_N C_D (C_K q) (C_B q),
    sampledNetworkExponent r b n d (u q) (s q) p,
    (sampledNetworkPrefactor_pos r b C_N C_D (C_K q) (C_B q)).le,
    sampledNetworkExponent_pos r b n d (u q) (s q) hp,
    uniform_sampled_approximate_network_bounds_of_le r b n d C_N C_D hCN (C_K q) (C_B q)
      (u q) (s q) (hCK q) (hCB q) p le_rfl le_rfl⟩

end QuantumCircuit.Party.EffectCircuit
