/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedOperatorContraction
import TNLean.PEPS.Approximation.DyadicRouting


/-!
# Degree of the distributed star and sample link family

The network degree counts the actual tagged links incident to a party. Identifying
this count with distributed-link incidence transfers the arity and lifetime bounds
used in the compression argument to the routing hypothesis. Parallel links retain
their gate and kind labels throughout.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
lines 581–588, and Section 8.1, `07-assembly.tex`, lines 61–62; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation.DistributedOperatorContraction

/-- The incidence count of the actual tagged link family is its routing degree.
Source: polynomial-PEPS manuscript, Theorem 5.2, 04-compression.tex,
lines 581–588, and 07-assembly.tex, lines 61–62. -/
theorem degreeBounded_of_card_incidentDistributedLinks_le
    {Party Gate : Type*} [DecidableEq Party] [DecidableEq Gate]
    (gates : Finset Gate) (participants : Gate → Finset Party)
    (root : Gate → Party) (d : ℕ)
    (h : ∀ p, (incidentDistributedLinks gates participants root p).card ≤ d) :
    DyadicPlacement.DegreeBounded
      (src gates participants root) (tgt gates participants root) d := by
  intro p
  have hmem (e : Link gates participants root) :
      (src gates participants root e = p ∨ tgt gates participants root e = p) ↔
      p ∈ distributedLinkParties root e.1 := by
    simp only [← endpoints_eq gates participants root e,
      Finset.mem_insert, Finset.mem_singleton, eq_comm]
  simp_rw [hmem]
  rw [Finset.univ_eq_attach,
    Finset.filter_attach (fun e ↦ p ∈ distributedLinkParties root e),
    Finset.card_map, Finset.card_attach]
  exact h p

/-- Bounded gate arity and lifetime participation bound the degree of the actual
star and sample link family, counting parallel links separately.
Source: polynomial-PEPS manuscript, Theorem 5.2, 04-compression.tex, lines 581–588. -/
theorem degreeBounded_of_arity_and_lifetime
    {Party Gate : Type*} [DecidableEq Party] [DecidableEq Gate]
    (gates : Finset Gate) (participants : Gate → Finset Party)
    (root : Gate → Party) (b : ℕ)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    (harity : ∀ g ∈ gates, (participants g).card ≤ b)
    (hlifetime : ∀ p, (incidentGates gates participants p).card ≤ b) :
    DyadicPlacement.DegreeBounded
      (src gates participants root) (tgt gates participants root) (2 * b * (b - 1)) := by
  exact degreeBounded_of_card_incidentDistributedLinks_le gates participants root _
    (fun p ↦ card_incidentDistributedLinks_le gates participants root b hroot harity p
      (hlifetime p))

end TNLean.PEPS.Approximation.DistributedOperatorContraction
