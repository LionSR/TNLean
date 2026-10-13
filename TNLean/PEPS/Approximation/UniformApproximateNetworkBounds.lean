/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitBudget
import TNLean.PEPS.Approximation.ApproximateSampledNetworkApproximation
import TNLean.PEPS.Approximation.ActualNetworkResourceCoupling

/-!
# Uniform bounds for sampled approximations supplied at a fixed precision

Fix the polynomial bounds for the number of gates and the physical dimensions,
and fix polynomial bounds for the monomial and coefficient counts at every
integer precision. For a requested real exponent, one integer precision and
one pair of polynomial constants suffice for every size at least two. The
comparison density is formed from the original gate operators, with their
private outputs traced out and without normalization.

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
namespace TNLean.PEPS.PairEffect.EffectCircuit
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable

/-- Uniform original resource bounds give a single polynomial bound for all
actual sampled alphabets, together with the full physical trace-norm error,
constant incidence, and the common-original-gate property. All constants and
the local precision are fixed before the size or a particular circuit is
chosen. This implication applies to expansions supplied at that precision;
it does not assert their availability for an original family.
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
      ∀ (L : ℝ), 2 ≤ L →
      ∀ (P : Type) [Fintype P]
        (H : P → HSpace) (hH : ∀ j, FiniteDimensional ℂ (H j))
        (x : ∀ j, H j) (hx : ∀ j, ‖x j‖ = 1)
        (physicalDim : P → ℕ) (ps : List P) (hps : ps.Nodup)
        (hcover : ∀ j : P, j ∈ ps) (priv : Layout P)
        (w : EffectCircuit (ProductInput.wholePartyLayout H)
          (familyPhysicalLayout physicalDim ps ++ priv)) (G : w.GateMaps)
        (K : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
        (hb : w.IsExpansionBounded r (B : ℝ))
        (hmonomial : ∀ g, w.monomialCount g ≤ K)
        (harity : ∀ g, (w.participants g).card ≤ b)
        (hlifetime : ∀ j, Nat.card {g : w.gateLocations // j ∈ w.participants g} ≤ b)
        (hphysical : ∀ j, (physicalDim j : ℝ≥0) ≤ D)
        (hpriv : ∀ z ∈ priv, FiniteDimensional ℂ z.space.carrier)
        (hK : (K : ℝ) ≤ C_K q * L ^ (u q))
        (hN : (w.expandedGateCount : ℝ) ≤ C_N * L ^ n)
        (hBB : (B : ℝ) ≤ C_B q * L ^ (s q))
        (hDD : (D : ℝ) ≤ C_D * L ^ d)
        (happrox : w.IsGateApproximation (L ^ q)⁻¹ G),
        let ε := (L ^ t)⁻¹
        let hε : 0 < ε := by positivity
        let hεone : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
        let hbudget : w.IsGateApproximation
            (sourceGateBudget (ε / 2) w.expandedGateCount) G := by
          have hprecision : w.IsGateApproximation
              (L ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * C_N⌉₊))⁻¹ G := by
            simpa only [Nat.ceil_natCast] using happrox
          simpa only [Real.rpow_neg (by linarith : 0 ≤ L), Real.rpow_natCast] using
            w.isGateApproximation_budget_of_power_bound L C_N (t : ℝ)
              w.expandedGateCount n (by assumption) hCN hN hprecision
        let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) _).le G hbudget
        let hbW := w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) _).le G hbudget hb
        let δ := sourceGateBudget ε w.expandedGateCount
        let R := W.produce.physicalFirstReplacement (sourceGateBudget_pos hε _)
          (familyPhysicalLayout physicalDim ps) priv W.isAllowed_produce
          ((W.isExpansionBounded_produce_iff r (B : ℝ)).mpr hbW)
        let k := sourceSamplingCount (Fintype.card R.sourceLocations)
          ((B : ℝ) ^ (4 * b) * (D : ℝ) ^ 4) ε
        letI := ProductInput.finiteDimensional_wholePartyMem H hH
        letI := Layout.finiteDimensional_mem_of_registers priv hpriv
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
                  (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
                  (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
                  (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card)) T -
              w.physicalDensityWithGateMaps G
                (familyLabelledPhysicalReadout physicalDim ps hps hcover priv)
                (ProductInput.ofAllParties H x hx).vector) ≤ L ^ (-p) ∧
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
  classical
  intro t q
  let C_sources := max 1 (C_N * (b.choose 2 : ℝ))
  let C_branch := C_K q * (64 * C_N ^ 2 * ((r : ℝ) * C_B q) ^ 2 + 2) ^ r
  let C_sample := 64 * C_sources ^ 2 * ((C_B q) ^ (4 * b) * C_D ^ 4) ^ 2 + 2
  let C := C_branch ^ 2 + C_sample
  let a := max (2 * (u q + 2 * r * (n + s q + t)))
    (2 * (n + 4 * b * s q + 4 * d + t))
  have ht : 0 < t := Nat.succ_le_iff.mp (Nat.one_le_ceil_iff.mpr hp)
  refine ⟨C, a + t, by dsimp [C, C_sample]; positivity, by omega, ?_⟩
  intro L hL P inst H hH x hx physicalDim ps hps hcover priv w G K B D hB hD
    hb hmonomial harity hlifetime hphysical hpriv hK hN hBB hDD happrox
    ε hε hεone hbudget W hbW δ R k
  have hLone : 1 ≤ L := le_trans (by norm_num) hL
  have hsmall : ε ≤ L ^ (-p) := by
    calc
      ε = L ^ (-(t : ℝ)) := by
        dsimp [ε]
        rw [Real.rpow_neg (by linarith : 0 ≤ L), Real.rpow_natCast]
      _ ≤ L ^ (-p) := Real.rpow_le_rpow_of_exponent_le hLone
        (neg_le_neg (Nat.le_ceil p))
  have hcountW : W.nonprivateCount ≤ w.expandedGateCount :=
    (w.nonprivateCount_rescaledOriginal _ G hbudget).le
  have harityW : ∀ g : W.nonprivateLocations, (W.participants g).card ≤ b := by
    intro g
    rw [w.participants_rescaledOriginal _ G hbudget g]
    exact harity _
  have hlifetimeW : ∀ j, W.participationCount j ≤ b := by
    intro j
    rw [w.participationCount_rescaledOriginal _ G hbudget j]
    exact hlifetime j
  have hK_W := w.isMonomialBounded_rescaledOriginal _ G hbudget hmonomial
  have hdim := W.card_physicalFirstDensityAlphabet_le_power
    (familyPhysicalLayout physicalDim ps) priv K r w.expandedGateCount b b
    (B : ℝ) (D : ℝ) L (C_K q) C_N (C_B q) C_D
    (u q) n (s q) d t hbW hK_W harityW hcountW hLone (hCK q) hCN (hCB q)
    B.coe_nonneg D.coe_nonneg hK hN hBB hDD (sourceGateBudget_pos hε _)
  have hinc := W.card_incidentPhysicalFirstDensityLinks_le
    (familyPhysicalLayout physicalDim ps) priv (sourceGateBudget_pos hε _)
    hbW harityW hlifetimeW
  have hlocal := W.exists_original_gate_of_physicalFirst_density_link
    (familyPhysicalLayout physicalDim ps) priv (sourceGateBudget_pos hε _) hbW
  obtain ⟨lam, E, F, _hframes, ω, hω⟩ :=
    w.exists_sampled_contractedOperator_approximate_error_le H hH x hx
      physicalDim ps hps hcover priv G B D hB hD hb le_rfl hlifetime hphysical
      hpriv ε hε hεone hbudget
  dsimp only at hω hdim hinc hlocal
  let ψ := ProductInput.ofAllParties H x hx
  let m := stackLength r (B : ℝ) δ
  let garbage := W.produce.auxiliary m ++ priv
  let hfinite := W.produce.finiteDimensional_auxiliary_private_registers m priv hpriv
  let I := fun z : Option {j : P // (fun _ : P ↦ true) j = true} ↦
    Fin (Module.finrank ℂ (Mem (Layout.atParty z (R.allResidualSourceLayout ++ []))))
  let J := fun z : Option {j : P // (fun _ : P ↦ true) j = true} ↦
    Fin (Module.finrank ℂ (Mem (Layout.atParty z
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
  let T := fun (j : P)
    (ξζ : DistributedOperatorContraction.GateLabelsAt
      (Finset.univ : Finset R.nonemptyGateLocations) (fun g ↦ R.participants g.1)
      (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) j)
    (z : DistributedOperatorContraction.SampleAt
      (Finset.univ : Finset R.nonemptyGateLocations) (fun g ↦ R.participants g.1) j → Fin k) ↦
    SourceCircuit.incidentSampledPhysicalFactor (I := I) (E := J)
      physicalDim ps hps hcover garbage R ψ k lam E F j
      (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) ω
      (fun z ↦ R.allResidualSourceBasis z)
      (fun z ↦ SourceCircuit.allPartyDiscardBasis garbage hfinite z)
      (z ∘ SourceCircuit.partialSlotSampleEquiv R j)
  refine ⟨T, hω.trans hsmall, ?_, hinc, ?_⟩
  · intro e
    exact (hdim e).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hLone (Nat.le_add_right a t)) (by dsimp [C, C_sample]; positivity))
  · intro e j l hj hl
    obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
    refine ⟨w.rescaledLocationsEquiv _ G hbudget g, ?_⟩
    have hpart := w.participants_rescaledOriginal _ G hbudget g
    exact ⟨hpart ▸ hjg, hpart ▸ hlg⟩

end TNLean.PEPS.PairEffect.EffectCircuit
