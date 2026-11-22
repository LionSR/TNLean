/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.PairEffectChain

/-!
# Elimination of normalized pair effects

A monomial of a gate expansion is a composition of contractions, preparations of normalized
pair vectors, and contractions by normalized pair bras (pair effects).  Grouping the steps
between consecutive effects, a monomial with `n` effects is a chain
`F_n ∘ E_n ∘ F_{n-1} ∘ ⋯ ∘ E_1 ∘ F_0`, where each `F_i` is a contraction and each
`E_i = ⟨η_i| ⊗ 1` contracts a pair register with a normalized pair vector `η_i` and leaves a
spectator space untouched.  Such chains, `EffectChain`, their replacement and the telescoping
bound for one monomial are defined and proved in `TNLean.Lattice.PartyCircuit.PairEffectChain`.

Each effect occurrence receives its own output stack of `m` pair registers.  In the replaced
monomial the effect `⟨η|` is replaced by the cyclic insertion `T_m`, and the stack stays idle
afterwards.  The ideal replacement appends the fixed vector `η^{⊗ m}`.  For a whole gate
expansion `G = ∑_ξ c_ξ M_ξ`, every monomial is given the stacks of all effect occurrences of
all monomials: those of other monomials are prepared as the fixed vectors `η^{⊗ m}`.  All
branches therefore have the same additional output space, and the ideal additional output is
the common normalized vector `Γ_m = ⨂_o η_o^{⊗ m}`.

Telescoping the at most `r` replacements in one monomial gives the error `r / √m`, and summing
with the original coefficients gives `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`.  Expanding the
averages over insertion positions writes `G'_m` as a weighted sum of at most `K m^r`
contractions, with unchanged absolute coefficient sum.

The model here has no parties: the effect-free pieces `F_i` of an `EffectChain` are arbitrary
contractions.  Two statements of Lemma 5.1 about parties (the expansion of `G'_m` uses only
local contractions and normalized pair sources, and its additional registers are owned by the
original participating parties) are proved in `TNLean.Lattice.PartyCircuit.PartyLayout`, where
monomials are placed on parties and their effect chains are the `EffectChain`s of this file.
The last clause, that all sources on one pair of parties combine into one, is proved for
arbitrary source occurrences in `TNLean.Lattice.PartyCircuit.PairEffectSourcePreparation` by
`partyPairEffectElimination_with_grouped_sources`.

## Main definitions

* `PartyCircuit.inventory`, `PartyCircuit.inventoryVector` : the common stack space and the
  common garbage vector `Γ_m` of a gate expansion.
* `PartyCircuit.replaceGate` : the replaced gate `G'_m`.
* `PartyCircuit.termList` : the expansion of `G'_m` into weighted contractions.
* `PartyCircuit.stackLength` : a choice of `m` from `r`, the coefficient sum and the target error.

## Main results

* `PartyCircuit.EffectChain.replace_eq_sum` : expansion of a replaced monomial.
* `PartyCircuit.norm_replaceGate_sub_le` : the gate error `(r / √m) ∑_ξ |c_ξ|`.
* `PartyCircuit.replaceGate_eq_sum_termList`, `PartyCircuit.length_termList_le`,
  `PartyCircuit.sum_norm_coeff_termList`, `PartyCircuit.norm_term_le_one` : the expansion of
  `G'_m`, its count `K m^r`, its absolute coefficient sum and contractivity of its terms.
* `PartyCircuit.pairEffectElimination` : the error, count and coefficient-sum clauses of
  Lemma 5.1 `lem:effects`.
* `PartyCircuit.replaceGate_rescaled`, `PartyCircuit.replaceGate_rescaled_stackLength` :
  near-contractivity and rescaling, also at the stack length chosen for a target error.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127; choice of `m` and rescaling, lines 199–212.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.Lattice.PartyCircuit

open EuclideanSpace CyclicInsertion ContinuousLinearMap

namespace EffectChain

/-- **Expansion of a replaced monomial.** Expanding the averages over insertion positions
writes the replaced monomial with `n` effects as the average of the `m^n` terms `replaceTerm`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 121–125. -/
theorem replace_eq_sum (m : ℕ) : {X Y : HSpace} → (M : EffectChain X Y) →
    M.replace m = ∑ κ, ((m : ℂ) ^ M.effectCount)⁻¹ • M.replaceTerm m κ
  | _, _, final F => by
      simp only [replace, Finset.univ_unique, pow_zero, inv_one, replaceTerm, one_smul,
        Finset.sum_const, Finset.card_singleton]
  | _, _, effect α β S F η rest => by
      simp only [replace, replaceTerm, replace_eq_sum m rest, cyclicInsertion,
        lTensor_finsetSum, rTensor_finsetSum, lTensor_smul, rTensor_smul, finsetSum_comp,
        comp_finsetSum, smul_comp, comp_smul, Finset.smul_sum]
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (rest.effectCount + 1) => Fin m),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun κ _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.tail_cons, Fin.cons_zero, smul_smul,
        effectCount, pow_succ, mul_inv, mul_comm]

end EffectChain

/-! ### Gate expansions with a common stack inventory -/

/-- A gate expansion `G = ∑_ξ c_ξ M_ξ`: a finite list of coefficients and monomials.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
lines 55–57. -/
abbrev GateExpansion (X Y : HSpace) : Type 1 := List (ℂ × EffectChain X Y)

variable {X Y : HSpace}

/-- The gate `∑_ξ c_ξ M_ξ` of an expansion. -/
def gate : GateExpansion X Y → (X →L[ℂ] Y)
  | [] => 0
  | p :: L => p.1 • p.2.eval + gate L

/-- The common stack inventory of a gate expansion: the stacks of every effect occurrence of
every monomial, indexed by the monomial and the position of the occurrence in it. -/
@[reducible] def inventory (m : ℕ) : GateExpansion X Y → HSpace
  | [] => HSpace.of ℂ
  | p :: L => HSpace.of (p.2.stackSpace m ⊗[ℂ] inventory m L)

/-- The common normalized garbage vector `Γ_m = ⨂_o η_o^{⊗ m}`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 105–112. -/
def inventoryVector (m : ℕ) : (L : GateExpansion X Y) → inventory m L
  | [] => (1 : ℂ)
  | p :: L => p.2.stackVector m ⊗ₜ[ℂ] inventoryVector m L

/-- The replaced gate `G'_m`: in the branch of each monomial its effect occurrences are
replaced by cyclic insertions, and the stacks of all other monomials are prepared as their
fixed vectors `η^{⊗ m}`.  Every branch has the same output space `Y ⊗ inventory m L`.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 5.1, `04-compression.tex`,
lines 100–115. -/
def replaceGate (m : ℕ) : (L : GateExpansion X Y) → (X →L[ℂ] Y ⊗[ℂ] inventory m L)
  | [] => 0
  | p :: L => p.1 • (assocL _ _ _ ∘L appendRight (inventoryVector m L) ∘L p.2.replace m) +
      leftCommL _ _ _ ∘L appendLeft (p.2.stackVector m) ∘L replaceGate m L

/-- The expansion of the replaced gate into terms with their coefficients: the
term of a monomial `c M` with `n` effects and insertion positions `κ` has coefficient
`c / m^n`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 121–125. -/
def termList (m : ℕ) :
    (L : GateExpansion X Y) → List (ℂ × (X →L[ℂ] Y ⊗[ℂ] inventory m L))
  | [] => []
  | p :: L =>
      (Finset.univ.toList.map fun κ => (p.1 * ((m : ℂ) ^ p.2.effectCount)⁻¹,
        assocL _ _ _ ∘L appendRight (inventoryVector m L) ∘L p.2.replaceTerm m κ)) ++
      (termList m L).map fun q => (q.1, leftCommL _ _ _ ∘L appendLeft (p.2.stackVector m) ∘L q.2)

theorem norm_inventoryVector (m : ℕ) : (L : GateExpansion X Y) → (∀ p ∈ L, p.2.IsAllowed) →
    ‖inventoryVector m L‖ = 1
  | [], _ => norm_one (α := ℂ)
  | p :: L, hL => by
      simp only [inventoryVector]
      rw [TensorProduct.norm_tmul, p.2.norm_stackVector m (hL p List.mem_cons_self),
        norm_inventoryVector m L fun q hq => hL q (List.mem_cons_of_mem _ hq), one_mul]

/-- **Gate error.** If every monomial of `G = ∑_ξ c_ξ M_ξ` is allowed and has at most `r`
pair effects, then `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, displayed
equation `eq:compression-effect-error`, `04-compression.tex`, lines 60–64 and 117–121. -/
theorem norm_replaceGate_sub_le {m : ℕ} (hm : m ≠ 0) {r : ℕ} :
    (L : GateExpansion X Y) → (∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r) →
    ‖replaceGate m L - appendRight (inventoryVector m L) ∘L gate L‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum
  | [], _ => by
      simp only [replaceGate, gate, comp_zero, sub_self, norm_zero, List.map_nil, List.sum_nil,
        mul_zero, le_refl]
  | p :: L, hL => by
      obtain ⟨hpA, hpr⟩ := hL p List.mem_cons_self
      have hL' : ∀ q ∈ L, q.2.IsAllowed ∧ q.2.effectCount ≤ r :=
        fun q hq => hL q (List.mem_cons_of_mem _ hq)
      have ih := norm_replaceGate_sub_le hm L hL'
      have hΓL : ‖inventoryVector m L‖ = 1 := norm_inventoryVector m L fun q hq => (hL' q hq).1
      set Γp := p.2.stackVector m
      set ΓL := inventoryVector m L
      have e1 : appendRight (Γp ⊗ₜ[ℂ] ΓL) ∘L (p.1 • p.2.eval) =
          p.1 • (assocL _ _ _ ∘L appendRight ΓL ∘L (appendRight Γp ∘L p.2.eval)) := by
        ext1 x
        simp [TensorProduct.smul_tmul']
      have e2 : appendRight (Γp ⊗ₜ[ℂ] ΓL) ∘L gate L =
          leftCommL _ _ _ ∘L appendLeft Γp ∘L (appendRight ΓL ∘L gate L) := by
        ext1 x
        simp
      have hsplit : replaceGate m (p :: L) -
          appendRight (inventoryVector m (p :: L)) ∘L gate (p :: L) =
          p.1 • (assocL _ _ _ ∘L appendRight ΓL ∘L (p.2.replace m - appendRight Γp ∘L p.2.eval)) +
          leftCommL _ _ _ ∘L appendLeft Γp ∘L (replaceGate m L - appendRight ΓL ∘L gate L) := by
        simp only [replaceGate, gate, inventoryVector, comp_add]
        rw [e1, e2]
        simp only [comp_sub, smul_sub]
        abel
      rw [hsplit, List.map_cons, List.sum_cons, mul_add]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, mul_comm (r / Real.sqrt m)]
        gcongr
        refine (norm_comp_le_of_norm_le_one _ norm_assocL_le).trans <|
          (norm_comp_le_of_norm_le_one _ ((norm_appendRight_le _).trans hΓL.le)).trans <|
          (p.2.norm_replace_sub_le hm hpA).trans ?_
        gcongr
      · exact (norm_comp_le_of_norm_le_one _ norm_leftCommL_le).trans <|
          (norm_comp_le_of_norm_le_one _ ((norm_appendLeft_le _).trans
            (p.2.norm_stackVector m hpA).le)).trans ih

/-- **Expansion of the replaced gate** into the weighted terms of `termList`. -/
theorem replaceGate_eq_sum_termList (m : ℕ) : (L : GateExpansion X Y) →
    replaceGate m L = ((termList m L).map fun q => q.1 • q.2).sum
  | [] => rfl
  | p :: L => by
      simp only [replaceGate, termList, List.map_append, List.sum_append, List.map_map]
      congr 1
      · rw [p.2.replace_eq_sum m]
        simp only [comp_finsetSum, comp_smul, Finset.smul_sum, smul_smul]
        rw [← Finset.sum_map_toList]
        rfl
      · rw [replaceGate_eq_sum_termList m L, ← comp_assoc, comp_listSum]
        rfl

/-- **Monomial count.** The expansion of `G'_m` has at most `K m^r` terms, where `K` is the
number of monomials of `G`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 65–66 and
120–124. -/
theorem length_termList_le {m r : ℕ} (hm : m ≠ 0) : (L : GateExpansion X Y) →
    (∀ p ∈ L, p.2.effectCount ≤ r) → (termList m L).length ≤ L.length * m ^ r
  | [], _ => by simp [termList]
  | p :: L, hL => by
      simp only [termList, List.length_append, List.length_map, Finset.length_toList,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, List.length_cons, add_mul,
        one_mul]
      rw [add_comm]
      exact add_le_add (length_termList_le hm L fun q hq => hL q (List.mem_cons_of_mem _ hq))
        (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm) (hL p List.mem_cons_self))

/-- **Absolute coefficient sum.** The expansion of `G'_m` has the same absolute coefficient
sum `∑_ξ |c_ξ|` as the original expansion.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 66–67 and
121–123. -/
theorem sum_norm_coeff_termList {m : ℕ} (hm : m ≠ 0) : (L : GateExpansion X Y) →
    ((termList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum
  | [] => rfl
  | p :: L => by
      simp only [termList, List.map_append, List.sum_append, List.map_map, List.map_cons,
        List.sum_cons]
      congr 1
      · rw [show ((fun q : ℂ × (X →L[ℂ] Y ⊗[ℂ] inventory m (p :: L)) => ‖q.1‖) ∘ _) =
            fun _ => ‖p.1 * ((m : ℂ) ^ p.2.effectCount)⁻¹‖ from rfl, List.map_const',
          List.sum_replicate, Finset.length_toList, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        have : ((m : ℝ) ^ p.2.effectCount) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm)
        push_cast
        field_simp
        simp only [Fintype.card_fin]
        ring
      · exact sum_norm_coeff_termList hm L

/-- Every term of the expansion of `G'_m` is a contraction. -/
theorem norm_term_le_one (m : ℕ) : (L : GateExpansion X Y) → (∀ p ∈ L, p.2.IsAllowed) →
    ∀ q ∈ termList m L, ‖q.2‖ ≤ 1
  | [], _ => by simp [termList]
  | p :: L, hL => by
      have hp := hL p List.mem_cons_self
      have hL' : ∀ q ∈ L, q.2.IsAllowed := fun q hq => hL q (List.mem_cons_of_mem _ hq)
      intro q hq
      simp only [termList, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨κ, _, rfl⟩ | ⟨q', hq', rfl⟩
      · exact norm_comp_le_one norm_assocL_le <| norm_comp_le_one
          ((norm_appendRight_le _).trans (norm_inventoryVector m L hL').le)
          (p.2.norm_replaceTerm_le_one m hp κ)
      · exact norm_comp_le_one norm_leftCommL_le <| norm_comp_le_one
          ((norm_appendLeft_le _).trans (p.2.norm_stackVector m hp).le)
          (norm_term_le_one m L hL' q' hq')

/-- **Elimination of normalized pair effects.** Let `G = ∑_ξ c_ξ M_ξ` be a gate expansion into
`K` allowed monomials, each with at most `r` normalized pair effects, and let `m ≥ 1`.  The
replaced gate `G'_m` and the common garbage vector `Γ_m` satisfy:

* `Γ_m` is normalized;
* `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`;
* `G'_m` is the weighted sum of the terms of `termList`;
* there are at most `K m^r` such terms;
* their absolute coefficient sum equals `∑_ξ |c_ξ|`;
* each term is a contraction.

These are the error, count and coefficient-sum clauses of the source lemma; the clauses about
parties are proved on a party layout in `partyPairEffectElimination`.

The hypothesis that `G` is a contraction is not needed here; it enters
`replaceGate_rescaled`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
`04-compression.tex`, lines 53–127. -/
theorem pairEffectElimination {m r : ℕ} (hm : m ≠ 0) (L : GateExpansion X Y)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r) :
    ‖inventoryVector m L‖ = 1 ∧
    ‖replaceGate m L - appendRight (inventoryVector m L) ∘L gate L‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ∧
    replaceGate m L = ((termList m L).map fun q => q.1 • q.2).sum ∧
    (termList m L).length ≤ L.length * m ^ r ∧
    ((termList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum ∧
    ∀ q ∈ termList m L, ‖q.2‖ ≤ 1 :=
  ⟨norm_inventoryVector m L fun p hp => (hL p hp).1, norm_replaceGate_sub_le hm L hL,
    replaceGate_eq_sum_termList m L, length_termList_le hm L fun p hp => (hL p hp).2,
    sum_norm_coeff_termList hm L, norm_term_le_one m L fun p hp => (hL p hp).1⟩

/-! ### Near-contractivity, rescaling and the choice of `m` -/

/-- A number `m ≥ 1` of stack registers achieving the target gate error `δ` for at most `r`
effects per monomial and absolute coefficient sum `S`: `m = ⌈(r S / δ)^2⌉ + 1`.  It is chosen
from the original coefficients, before the averages are expanded.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 201–208. -/
def stackLength (r : ℕ) (S δ : ℝ) : ℕ := ⌈(r * S / δ) ^ 2⌉₊ + 1

theorem stackLength_ne_zero (r : ℕ) (S δ : ℝ) : stackLength r S δ ≠ 0 := Nat.succ_ne_zero _

theorem stackLength_spec (r : ℕ) {S δ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) :
    r / Real.sqrt (stackLength r S δ) * S ≤ δ := by
  set N := stackLength r S δ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (stackLength_ne_zero r S δ)
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hrS : 0 ≤ r * S / δ := by positivity
  have hle : r * S / δ ≤ Real.sqrt N := by
    rw [Real.le_sqrt hrS hN.le]
    calc (r * S / δ) ^ 2 ≤ ⌈(r * S / δ) ^ 2⌉₊ := Nat.le_ceil _
      _ ≤ N := by simp only [N, stackLength]; push_cast; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hsq]
  calc (r : ℝ) * S = r * S / δ * δ := by field_simp
    _ ≤ Real.sqrt N * δ := by gcongr
    _ = δ * Real.sqrt N := mul_comm _ _

/-- **Near-contractivity and rescaling of the replaced gate.** If `G` is a contraction and
`δ ≥ (r / √m) ∑_ξ |c_ξ|`, then `G'_m` is within `δ` of `G ⊗ |Γ_m⟩`, `‖G'_m‖ ≤ 1 + δ`, and
`(1 + δ)⁻¹ G'_m` is a contraction within `2δ` of `G ⊗ |Γ_m⟩`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 210–212. -/
theorem replaceGate_rescaled {X Y : HSpace} {m r : ℕ} (hm : m ≠ 0) (L : GateExpansion X Y)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r) (hG : ‖gate L‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ≤ δ) :
    ‖replaceGate m L - appendRight (inventoryVector m L) ∘L gate L‖ ≤ δ ∧
    ‖replaceGate m L‖ ≤ 1 + δ ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m L‖ ≤ 1 ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m L - appendRight (inventoryVector m L) ∘L gate L‖ ≤
      2 * δ := by
  have hB : ‖appendRight (inventoryVector m L) ∘L gate L‖ ≤ 1 :=
    norm_comp_le_one ((norm_appendRight_le _).trans
      (norm_inventoryVector m L fun p hp => (hL p hp).1).le) hG
  have h := (norm_replaceGate_sub_le hm L hL).trans hδ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans h
  have hA := norm_le_one_add_of_norm_sub_le hB h
  exact ⟨h, hA, norm_inv_one_add_smul_le_one hδ0 hA, norm_inv_one_add_smul_sub_le hδ0 hB h⟩

/-- **Rescaling at the chosen stack length.** For a target error `δ > 0` and a bound
`S ≥ ∑_ξ |c_ξ|` on the original absolute coefficient sum, the stack length
`m = stackLength r S δ` makes `G'_m` lie within `δ` of `G ⊗ |Γ_m⟩` and `(1 + δ)⁻¹ G'_m` a
contraction within `2δ` of it.  The length `m` depends only on `r`, `S` and `δ`, not on the
expansion of `G'_m`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 201–212. -/
theorem replaceGate_rescaled_stackLength {X Y : HSpace} {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (L : GateExpansion X Y) (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r)
    (hG : ‖gate L‖ ≤ 1) (hS : (L.map fun p => ‖p.1‖).sum ≤ S) :
    ‖replaceGate (stackLength r S δ) L -
        appendRight (inventoryVector (stackLength r S δ) L) ∘L gate L‖ ≤ δ ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) L‖ ≤ 1 ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) L -
        appendRight (inventoryVector (stackLength r S δ) L) ∘L gate L‖ ≤ 2 * δ := by
  have hsum : 0 ≤ (L.map fun p => ‖p.1‖).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hle : r / Real.sqrt (stackLength r S δ) * (L.map fun p => ‖p.1‖).sum ≤ δ :=
    (mul_le_mul_of_nonneg_left hS (by positivity)).trans
      (stackLength_spec r (hsum.trans hS) hδ)
  obtain ⟨h1, -, h3, h4⟩ := replaceGate_rescaled (stackLength_ne_zero r S δ) L hL hG hle
  exact ⟨h1, h3, h4⟩

end TNLean.Lattice.PartyCircuit
