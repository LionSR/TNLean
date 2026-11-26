/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Source.Locations
import TNLean.Network.DistributedContraction.DistributedOperatorContraction
import QICLean.Circuit.Party.Compression.GateExpansion.ReplacementBounds

/-!
# Polynomial dimensions of the actual source-network alphabets

A star link carries the ordered pair of actual ket and bra branch labels of
its gate occurrence. A sample link carries one of the actual sample indices.
Polynomial bounds on these branch counts and on the sample count therefore
give a polynomial bound on every such virtual dimension, without a ceiling
or a bound on any private memory or source Schmidt rank.

This is a resource bound for the constructed alphabets. Identifying a sampled
physical density with a contraction of local tensors is a separate result.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.

It also contains the following results.

* `QuantumCircuit.Party.OriginalCircuit.card_physicalFirstNetworkAlphabet_le_power`: polynomial link
  dimensions from original gate resources.
-/

section SourceAlphabetPolynomial

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P] {X Y : P → Type}

open Classical in
/-- The actual star and sample alphabets have uniformly polynomial cardinality
when actual gate branch counts and the sample count do. The exact per-link
cardinality is used, so no integral upper bound on a global branch count is
introduced. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem card_sourceNetworkAlphabet_le_of_power_bounds (w : SourceCircuit X Y)
    (gates : Finset w.gateLocations) (root : w.gateLocations → P) (k : ℕ)
    (L C_M C_k : ℝ) (u v : ℕ) (hL : 1 ≤ L) (hM0 : 0 ≤ C_M) (hk0 : 0 ≤ C_k)
    (hM : ∀ g ∈ gates, (Fintype.card (w.branchLabels g) : ℝ) ≤ C_M * L ^ u)
    (hk : (k : ℝ) ≤ C_k * L ^ v)
    (e : DistributedOperatorContraction.Link gates w.participants root) :
    (Fintype.card (DistributedOperatorContraction.alphabet gates w.participants root
      (fun g ↦ w.branchLabels g × w.branchLabels g) k e) : ℝ) ≤
        (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) := by
  rw [DistributedOperatorContraction.card_alphabet]
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label with
  | inl p =>
      have hg := ((mem_distributedLinks gates w.participants root _).mp he).1
      change (Fintype.card (w.branchLabels g × w.branchLabels g) : ℝ) ≤ _
      rw [Fintype.card_prod, Nat.cast_mul]
      calc
        _ ≤ (C_M * L ^ u) * (C_M * L ^ u) :=
          mul_le_mul (hM g hg) (hM g hg) (Nat.cast_nonneg _)
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

end QuantumCircuit.Party.SourceCircuit

end

end SourceAlphabetPolynomial

section PhysicalFirstLinkPolynomial

/-!
## Polynomial link dimensions from original gate resources

The source-only replacement of an original circuit has one polynomial bound for
both its branch-pair links and its sample links. The coefficient and exponent
are explicit expressions in the original uniform bounds and the requested
accuracy exponent. They do not depend on the particular construction, its
private dimensions, or its source Schmidt ranks.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace QuantumCircuit.Party.OriginalCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

open Classical in
/-- The actual star and sample alphabets obey a single polynomial bound
whose constants depend only on the original resource bounds. This holds for
any retained collection of gate occurrences and any choice of its roots.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem card_physicalFirstNetworkAlphabet_le_power (w : OriginalCircuit X Y)
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
    ∀ (gates : Finset R.gateLocations) (root : R.gateLocations → P)
      (e : DistributedOperatorContraction.Link gates R.participants root),
      (Fintype.card (DistributedOperatorContraction.alphabet gates R.participants root
        (fun g ↦ R.branchLabels g × R.branchLabels g) k e) : ℝ) ≤
        (C_branch ^ 2 + C_sample) *
          L ^ (max (2 * (u + 2 * r * (n + s + p)))
            (2 * (n + 4 * lifetime * s + 4 * d + p))) := by
  intro R k C_sources C_branch C_sample gates root e
  apply R.card_sourceNetworkAlphabet_le_of_power_bounds gates root k L C_branch C_sample
    (u + 2 * r * (n + s + p)) (2 * (n + 4 * lifetime * s + 4 * d + p)) hL
  · dsimp [C_branch]
    positivity
  · dsimp [C_sample]
    positivity
  · intro g _
    exact w.card_branchLabels_replacement_le_power K r N B L C_K C_N C_B u n s p hb hmonomial
      hL hCK hCN hCB hB hK hN hBbound hδ g
  · exact (w.binomialSampleCount_replacement_lt_power (lifetime := lifetime) hδ hb hpart
      L C_N C_B C_D n s d p hL hCB hB hD ((Nat.cast_le.mpr hcount).trans hN) hBbound
      hDbound).le

end QuantumCircuit.Party.OriginalCircuit

end

end PhysicalFirstLinkPolynomial
