/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PhysicalFirstLinkPolynomial
import TNLean.PEPS.Approximation.PhysicalFirstNetworkResources
import TNLean.PEPS.Approximation.SourceNetworkDimensions
import TNLean.PEPS.Approximation.SourceNetworkIncidence

/-!
# Original resource bounds for the actual sampled contraction

The gate type is the original nonempty occurrence subtype used by the exact
sampled contraction. Its roots are derived from those occurrences. The proved
branch and sample estimates therefore bound precisely its virtual alphabets.
The original occurrence correspondence also preserves participant sets,
giving incidence and a common original gate for the two endpoints of a link.
No root is selected on an empty participant set.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229, 342–381 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
open TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}

namespace SourceCircuit

open Classical in
/-- Real power bounds on branch counts and sample size bound the alphabets
of the actual nonempty-occurrence density network.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem card_alphabet_source_density_le_of_power_bounds (w : SourceCircuit a b)
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

open Classical in
/-- The same polynomial constants from the original resource bounds control
exactly the alphabets of the sampled contraction on nonempty gate occurrences.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229 and 565–588. -/
theorem card_physicalFirstDensityAlphabet_le_power
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
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
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r B).mpr hb)
    let k := sourceSamplingCount (Fintype.card R.sourceLocations)
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
    exact w.card_branchLabels_physicalFirstReplacement_le_power physical priv
      K r N B L C_K C_N C_B u n s p hb hmonomial hL hCK hCN hCB hB
      hK hN hBbound hδ g.1
  · exact (w.sourceSamplingCount_physicalFirstReplacement_lt_power physical priv hδ hb
      hpart L C_N C_B C_D n s d p hL hCB hB hD
      ((Nat.cast_le.mpr hcount).trans hN) hBbound hDbound).le

open Classical in
/-- The inverse original-occurrence correspondence preserves participants.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 199–229 and 581–588. -/
private theorem participants_physicalFirstReplacement_symm
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    let E := w.physicalFirstReplacementLocationsEquiv physical priv hδ hb
    ∀ g : R.gateLocations, R.participants g = w.participants (E.symm g) := by
  intro R E g
  have h := w.participants_physicalFirstReplacementLocationsEquiv
    physical priv hδ hb (E.symm g)
  change R.participants (E (E.symm g)) = _ at h
  rw [E.apply_symm_apply] at h
  exact h

open Classical in
/-- The actual nonempty-occurrence density links inherit the original
arity and whole-lifetime incidence bound, without a root premise.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–142 and 581–588. -/
theorem card_incidentPhysicalFirstDensityLinks_le
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r b : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ b)
    (hlifetime : ∀ p, w.participationCount p ≤ b) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    ∀ p, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) p).card ≤
        2 * b * (b - 1) := by
  intro R p
  apply R.card_incidentSourceDensityLinks_le b
  · intro g
    exact (congrArg Finset.card
      (w.participants_physicalFirstReplacement_symm physical priv hδ hb g.1)).trans_le
        (harity _)
  · intro q
    exact (SourceCircuit.participationCount_physicalFirstOutput
      (w.produce.auxiliary (stackLength r S δ)) physical priv _ q).trans_le
        (w.participationCount_replacement_le hδ hb hlifetime q)

open Classical in
/-- Both endpoints of an actual sampled-density link participate together
in one original gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 581–588. -/
theorem exists_original_gate_of_physicalFirst_density_link
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    ∀ e : DistributedOperatorContraction.Link
      (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
      ∀ p q, p ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
        q ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
        ∃ g : w.nonprivateLocations, p ∈ w.participants g ∧ q ∈ w.participants g := by
  intro R e p q hp hq
  have hsub := R.distributedLinkParties_source_subset e
  have hpart := w.participants_physicalFirstReplacement_symm physical priv hδ hb e.1.1.1
  refine ⟨(w.physicalFirstReplacementLocationsEquiv physical priv hδ hb).symm e.1.1.1, ?_⟩
  exact ⟨hpart ▸ hsub hp, hpart ▸ hsub hq⟩

end OriginalCircuit

end TNLean.PEPS.PairEffect
