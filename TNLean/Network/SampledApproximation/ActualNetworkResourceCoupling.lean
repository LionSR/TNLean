/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.CorrectedCost
import TNLean.Network.DistributedContraction.SourceAlphabetPolynomial
import TNLean.Network.DistributedContraction.SourceNetworkDimensions

/-!
# Original resource bounds for the actual sampled contraction

The source-only replacement of an original circuit keeps its nonprivate gate occurrences and
their participating parties. The star and sample links of the distributed network built on any
retained collection of these occurrences therefore join two participants of one original gate,
and their incidence is bounded by the original gate arity and lifetime participation.

Removing gate occurrences with empty participant sets preserves the full participation count of
every party. The gate type of the exact sampled contraction is the subtype of nonempty
occurrences, and its roots are derived from those occurrences; no root is selected on an empty
participant set. The proved branch and sample estimates therefore bound precisely its virtual
alphabets, and the incidence and common-gate statements hold for its links. Parallel star and
sample links are counted separately.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
140–142, 199–229, 342–381 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section

namespace QuantumCircuit.Party

open TNLean.Network GateIncidence

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable {X Y : P → Type}

open Classical in
/-- The retained nonempty occurrences preserve each party's complete
participation count. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 140–142 and 581–588. -/
theorem card_incidentNonemptyGates_eq_participationCount (w : SourceCircuit X Y) (p : P) :
    (incidentGates (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) p).card = w.participationCount p := by
  let e : {g : w.nonemptyGateLocations // p ∈ w.participants g.1} ≃
      {g : w.gateLocations // p ∈ w.participants g} :=
    { toFun := fun g ↦ ⟨g.1.1, g.2⟩
      invFun := fun g ↦ ⟨⟨g.1, ⟨p, g.2⟩⟩, g.2⟩
      left_inv := fun g ↦ by cases g; rfl
      right_inv := fun g ↦ by cases g; rfl }
  rw [← PartyCircuit.natCard_participants_mem, ← Nat.card_congr e, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rfl

open Classical in
/-- The actual density links have incidence at most `2*b*(b-1)` under
original arity and participation bounds. Root membership is derived from
its original participant set. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 581–588. -/
theorem card_incidentSourceDensityLinks_le (w : SourceCircuit X Y) (b : ℕ)
    (harity : ∀ g : w.nonemptyGateLocations, (w.participants g.1).card ≤ b)
    (hlifetime : ∀ p, w.participationCount p ≤ b) (p : P) :
    (incidentDistributedLinks (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w) p).card ≤ 2 * b * (b - 1) := by
  apply card_incidentDistributedLinks_le
    (Finset.univ : Finset w.nonemptyGateLocations)
    (fun g ↦ w.participants g.1) (sourceGateRoot w) b
    (fun g _ ↦ sourceGateRoot_mem w g) (fun g _ ↦ harity g) p
  rw [card_incidentNonemptyGates_eq_participationCount]
  exact hlifetime p

open Classical in
/-- Real power bounds on branch counts and sample size bound the alphabets
of the actual nonempty-occurrence density network.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem card_alphabet_source_density_le_of_power_bounds (w : SourceCircuit X Y)
    (k : ℕ) (L C_M C_k : ℝ) (u v : ℕ)
    (hL : 1 ≤ L) (hM0 : 0 ≤ C_M) (hk0 : 0 ≤ C_k)
    (hM : ∀ g : w.nonemptyGateLocations,
      (Fintype.card (w.branchLabels g.1) : ℝ) ≤ C_M * L ^ u)
    (hk : (k : ℝ) ≤ C_k * L ^ v)
    (e : DistributedOperatorContraction.Link
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)) :
    (Fintype.card (DistributedOperatorContraction.alphabet
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)
      (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k e) : ℝ) ≤
        (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) := by
  rw [card_alphabet_source_density]
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label with
  | inl p =>
      rw [Nat.cast_pow]
      change ((Fintype.card (w.branchLabels g.1) : ℝ) ^ 2) ≤ _
      calc
        _ = (Fintype.card (w.branchLabels g.1) : ℝ) *
            (Fintype.card (w.branchLabels g.1) : ℝ) := pow_two _
        _ ≤ (C_M * L ^ u) * (C_M * L ^ u) :=
          mul_le_mul (hM g) (hM g) (Nat.cast_nonneg _)
            (mul_nonneg hM0 (pow_nonneg (zero_le_one.trans hL) _))
        _ = C_M ^ 2 * L ^ (2 * u) := by rw [Nat.mul_comm 2 u, pow_mul]; ring
        _ ≤ C_M ^ 2 * L ^ (max (2 * u) v) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (Nat.le_max_left _ _)) (sq_nonneg C_M)
        _ ≤ (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hk0) (by positivity)
  | inr pair =>
      change (k : ℝ) ≤ _
      calc
        _ ≤ C_k * L ^ v := hk
        _ ≤ C_k * L ^ (max (2 * u) v) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (Nat.le_max_right _ _)) hk0
        _ ≤ (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg C_M)) (by positivity)

end SourceCircuit

namespace OriginalCircuit

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- The occurrence correspondence of the replacement, read backwards, keeps the participants.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 199–229 and 581–588. -/
private theorem participants_replacement_symm (w : OriginalCircuit X Y)
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (g : (w.replacement hδ hb).gateLocations) :
    (w.replacement hδ hb).participants g =
      w.participants ((w.replacementLocationsEquiv hδ hb).symm g) := by
  have h := w.participants_replacementLocationsEquiv hδ hb
    ((w.replacementLocationsEquiv hδ hb).symm g)
  rwa [Equiv.apply_symm_apply] at h

open Classical in
/-- Each link of the actual replacement network joins two parties that belong
to a single gate occurrence of the original circuit. The statement applies to any retained
collection of gate occurrences. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 199–229 and 565–588. -/
theorem exists_original_gate_of_physicalFirst_link (w : OriginalCircuit X Y)
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    let R := w.replacement hδ hb
    ∀ (gates : Finset R.gateLocations) (root : R.gateLocations → P),
      (∀ g ∈ gates, root g ∈ R.participants g) →
      ∀ e ∈ distributedLinks gates R.participants root, ∀ p q,
        p ∈ distributedLinkParties root e → q ∈ distributedLinkParties root e →
        ∃ g : w.nonprivateLocations, p ∈ w.participants g ∧ q ∈ w.participants g := by
  intro R gates root hroot e he p q hp hq
  obtain ⟨g, _, hp, hq⟩ :=
    exists_common_gate_of_mem_distributedLinkParties gates R.participants root hroot he hp hq
  have heq := w.participants_replacement_symm hδ hb g
  exact ⟨(w.replacementLocationsEquiv hδ hb).symm g, heq ▸ hp, heq ▸ hq⟩

open Classical in
/-- Original arity and whole-lifetime participation at most `b` imply the
constant incidence bound `2*b*(b-1)` for the actual replacement links, for any retained
collection of gate occurrences. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 140–142, 199–229 and 565–588. -/
theorem card_incidentPhysicalFirstLinks_le (w : OriginalCircuit X Y)
    {r b : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ b)
    (hlifetime : ∀ p, w.participation p ≤ b) :
    let R := w.replacement hδ hb
    ∀ (gates : Finset R.gateLocations) (root : R.gateLocations → P),
      (∀ g ∈ gates, root g ∈ R.participants g) → ∀ p,
      (incidentDistributedLinks gates R.participants root p).card ≤ 2 * b * (b - 1) := by
  intro R gates root hroot p
  apply card_incidentDistributedLinks_le gates R.participants root b hroot
  · intro g _
    rw [w.participants_replacement_symm hδ hb g]
    exact harity _
  · have hsub : incidentGates gates R.participants p ⊆
        incidentGates Finset.univ R.participants p :=
      Finset.filter_subset_filter _ (Finset.subset_univ gates)
    exact (Finset.card_le_card hsub).trans
      ((R.participationCount_eq_card_incidentGates p).symm.trans_le
        (w.participationCount_replacement_le hδ hb hlifetime p))

open Classical in
/-- The same polynomial constants from the original resource bounds control
exactly the alphabets of the sampled contraction on nonempty gate occurrences.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229 and 565–588. -/
theorem card_physicalFirstDensityAlphabet_le_power (w : OriginalCircuit X Y)
    (K r N arity lifetime : ℕ) (B D L C_K C_N C_B C_D : ℝ)
    (u n s d p : ℕ)
    (hb : w.IsExpansionBounded r B) (hmonomial : w.IsMonomialBounded K)
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (hcount : w.nonprivateCount ≤ N)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N) (hCB : 0 ≤ C_B)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hK : (K : ℝ) ≤ C_K * L ^ u) (hN : (N : ℝ) ≤ C_N * L ^ n)
    (hBbound : B ≤ C_B * L ^ s) (hDbound : D ≤ C_D * L ^ d)
    (hδ : 0 < sourceGateBudget (L ^ p)⁻¹ N) :
    let R := w.replacement hδ hb
    let k := binomialSampleCount (max 1 (Fintype.card R.sourceLocations))
      (B ^ (4 * lifetime) * D ^ 4) (L ^ p)⁻¹
    let C_sources := max 1 (C_N * (arity.choose 2 : ℝ))
    let C_branch := C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_B) ^ 2 + 2) ^ r
    let C_sample := 64 * C_sources ^ 2 * (C_B ^ (4 * lifetime) * C_D ^ 4) ^ 2 + 2
    ∀ e : DistributedOperatorContraction.Link
      (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
      (Fintype.card (DistributedOperatorContraction.alphabet
        (Finset.univ : Finset R.nonemptyGateLocations)
        (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
        (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤
        (C_branch ^ 2 + C_sample) *
          L ^ (max (2 * (u + 2 * r * (n + s + p)))
            (2 * (n + 4 * lifetime * s + 4 * d + p))) := by
  intro R k C_sources C_branch C_sample e
  apply R.card_alphabet_source_density_le_of_power_bounds k L C_branch C_sample
    (u + 2 * r * (n + s + p)) (2 * (n + 4 * lifetime * s + 4 * d + p)) hL
  · dsimp [C_branch]
    positivity
  · dsimp [C_sample]
    positivity
  · intro g
    exact w.card_branchLabels_replacement_le_power K r N B L C_K C_N C_B u n s p hb hmonomial
      hL hCK hCN hCB hB hK hN hBbound hδ g.1
  · exact (w.binomialSampleCount_replacement_lt_power (lifetime := lifetime) hδ hb hpart
      L C_N C_B C_D n s d p hL hCB hB hD ((Nat.cast_le.mpr hcount).trans hN) hBbound
      hDbound).le

open Classical in
/-- The actual nonempty-occurrence density links inherit the original
arity and whole-lifetime incidence bound, without a root premise.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–142 and 581–588. -/
theorem card_incidentPhysicalFirstDensityLinks_le (w : OriginalCircuit X Y)
    {r b : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ b)
    (hlifetime : ∀ p, w.participation p ≤ b) :
    let R := w.replacement hδ hb
    ∀ p, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) p).card ≤
        2 * b * (b - 1) := by
  intro R p
  apply R.card_incidentSourceDensityLinks_le b
  · intro g
    rw [w.participants_replacement_symm hδ hb g.1]
    exact harity _
  · exact w.participationCount_replacement_le hδ hb hlifetime

open Classical in
/-- Both endpoints of an actual sampled-density link participate together
in one original gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 581–588. -/
theorem exists_original_gate_of_physicalFirst_density_link (w : OriginalCircuit X Y)
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    let R := w.replacement hδ hb
    ∀ e : DistributedOperatorContraction.Link
      (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
      ∀ p q, p ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
        q ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
        ∃ g : w.nonprivateLocations, p ∈ w.participants g ∧ q ∈ w.participants g := by
  intro R e p q hp hq
  have hsub := R.distributedLinkParties_source_subset e
  have hpart := w.participants_replacement_symm hδ hb e.1.1.1
  exact ⟨(w.replacementLocationsEquiv hδ hb).symm e.1.1.1, hpart ▸ hsub hp, hpart ▸ hsub hq⟩

end OriginalCircuit

end QuantumCircuit.Party
