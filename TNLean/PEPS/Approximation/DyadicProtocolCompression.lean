/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedGateMapConstruction
import TNLean.PEPS.Approximation.DistributedPartyNetwork
import TNLean.PEPS.Approximation.DyadicProtocol
import TNLean.PEPS.Approximation.GroundStateApproximation
import TNLean.PEPS.Approximation.OriginalCircuitChain
import TNLean.PEPS.Approximation.OriginalCircuitSequence

/-!
# Compression of the dyadic distribution protocol

Section 8.1 of the polynomial-PEPS manuscript applies Theorem 5.2 (`thm:compression`) at
accuracy `L⁻⁵` to the protocol of Proposition 7.1 and obtains a party operator network `σ` with
polynomial link dimensions and `‖σ - |Ω⟩⟨Ω|‖₁ ≤ C L⁻⁵` (`eq:compressed-density`,
`07-assembly.tex:45–55`). This module carries out that step for the protocols of
`LargeSizeDyadicProtocolConsequences`.

The changes of a protocol are composed into one chronology, and the protocol is read as a
distributed construction of Theorem 5.2 with the recorded monomial expansions of its gates. Its
physical density is the physical density of the actual final vector.
All protocols, over all sizes, Hamiltonians, and ground vectors, form one family with uniform
polynomial bounds, so the constants of Theorem 5.2 are chosen before the family member, as in
the order of constants of `07-assembly.tex:179–203`. The resulting distributed operator
contraction is enumerated as a party network on the dyadic anchors of the protocol; the
separation hypothesis of Lemma 8.2 follows from item 3 of Proposition 7.1, since every link joins
two parties of a common gate.

The hypothesis `LargeSizeDyadicProtocolConsequences` is not proved, so the final statement is a
conditional form of Theorem 1.1.

**Scope restriction (consequences of Proposition 7.1):** the main theorems
`largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences` and
`polynomialPEPSApproximation_of_largeSizeDyadicProtocolConsequences` assume
`LargeSizeDyadicProtocolConsequences`, which is weaker than Proposition 7.1
(`06-geometry.tex:12–53`). It omits the registers of the copies of `Ω`, the frame factorization
of the reference vectors, the placement of additional parties, the pair-source and message counts
of each monomial, and the expansions of every fixed inverse-power accuracy; none of these is used here, since the single instantiated expansion of
each change is exact and serves at every accuracy of Theorem 5.2. Documented in
`docs/paper-gaps/polypeps_prop71_consequences_interface.tex`. Elimination: prove Proposition 7.1
for a construction certificate carrying the omitted clauses and forget it into this interface.

## Main results

* `TNLean.PEPS.Approximation.DyadicProtocol.exists_partyNetwork_of_contractedOperator`: a
  compressed density on the parties of a protocol gives an operator party network on dyadic
  anchors with the hypotheses of Lemma 8.2.
* `TNLean.PEPS.Approximation.largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences`:
  the compressed dyadic operator network from the consequences of Proposition 7.1.
* `TNLean.PEPS.Approximation.polynomialPEPSApproximation_of_largeSizeDyadicProtocolConsequences`:
  Theorem 1.1 conditional on those consequences.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `07-assembly.tex:9–63`; Theorem 5.2
  `thm:compression`, `04-compression.tex:137–175`; Theorem 1.1 `thm:main`,
  `00-introduction.tex:36–57`; immutable revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  These are original proofs; no OpenAI Lean code is copied or adapted.
-/

noncomputable section

open scoped Matrix

namespace TNLean.PEPS.PairEffect.OriginalCircuit

variable {P : Type} {a b : Layout P}

/-- An absolute coefficient sum at most `S` bounds every individual coefficient by any `S' ≥ S`,
and the pair-effect count of every monomial is unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 143–149. -/
theorem IsExpansionBounded.isTermwiseBounded {w : OriginalCircuit a b} {r : ℕ} {S S' : ℝ}
    (h : w.IsExpansionBounded r S) (hS : S ≤ S') : w.IsTermwiseBounded r S' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate owner hC L hL hG tail =>
      refine fun term hterm ↦ ⟨h.1 term hterm, (h.2.trans hS).trans' ?_⟩
      exact List.single_le_sum (fun x hx ↦ by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        exact norm_nonneg _) _ (List.mem_map_of_mem hterm)
  | swap => trivial
  | frame r w ih => exact ih h

end TNLean.PEPS.PairEffect.OriginalCircuit

namespace TNLean.PEPS.Approximation.DyadicProtocol

open Finset TNLean.PEPS.PairEffect

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- The first `n` changes of a protocol, composed into one chronology.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:25–32`. -/
def chain (n : ℕ) : OriginalCircuit (D.layout 0) (D.layout n) :=
  OriginalCircuit.sequence D.layout D.step n

/-- The composed changes take the initial vector to the actual vector at every stage.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:29–36`. -/
theorem eval_chain_trajectory (n : ℕ) : (D.chain n).eval (D.trajectory 0) = D.trajectory n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [chain, OriginalCircuit.eval_sequence_succ, ← chain, ih]
      rfl

/-- The composed changes have the nonprivate gates of all changes.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:25–32`. -/
theorem nonprivateCount_chain (n : ℕ) :
    (D.chain n).nonprivateCount = ∑ t ∈ range n, (D.step t).nonprivateCount :=
  OriginalCircuit.nonprivateCount_sequence D.layout D.step n

/-- The participation of a party in the composed changes is the sum over the changes.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:31–32`. -/
theorem participationCount_chain (n : ℕ) (p : P) :
    (D.chain n).participationCount p = ∑ t ∈ range n, (D.step t).participationCount p :=
  OriginalCircuit.participationCount_sequence D.layout D.step n p

/-- Every nonprivate gate of the composed changes is a nonprivate gate of one change.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:25–37`. -/
theorem exists_participants_chain (n : ℕ) (g : (D.chain n).nonprivateLocations) :
    ∃ t < n, ∃ g' : (D.step t).nonprivateLocations,
      (D.chain n).participants g = (D.step t).participants g' :=
  OriginalCircuit.forall_participants_sequence D.layout D.step
    (fun S ↦ ∃ t < n, ∃ g' : (D.step t).nonprivateLocations, S = (D.step t).participants g')
    n (fun t ht g' ↦ ⟨t, ht, g', rfl⟩) g

/-- The composed changes inherit the expansion bounds of every change.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:25–32`. -/
theorem isExpansionBounded_chain {r : ℕ} {S : ℝ} (n : ℕ)
    (h : ∀ t < n, (D.step t).IsExpansionBounded r S) : (D.chain n).IsExpansionBounded r S :=
  OriginalCircuit.isExpansionBounded_sequence D.layout D.step r S n h

/-- The composed changes inherit the monomial bounds of every change.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:25–32`. -/
theorem isMonomialBounded_chain {K : ℕ} (n : ℕ)
    (h : ∀ t < n, (D.step t).IsMonomialBounded K) : (D.chain n).IsMonomialBounded K :=
  OriginalCircuit.isMonomialBounded_sequence D.layout D.step K n h

/-- The protocol, read as one distributed construction of Theorem 5.2: its composed changes, with
their recorded monomial expansions, between the input and output layouts of the protocol.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:45–49`, and Theorem 5.2,
`04-compression.tex:137–151`. -/
def toDistributedConstruction (hL : 0 < L) : DistributedConstruction P where
  nonemptyParties := ⟨D.site (⟨0, hL⟩, ⟨0, hL⟩)⟩
  initialSpace := D.initialSpace
  finite_initialSpace := D.finite_initialSpace
  initialVector := D.initialVector
  norm_initialVector := D.norm_initialVector
  physicalDimension := D.physicalDimension
  physicalOrder := D.physicalOrder
  physicalOrder_nodup := D.physicalOrder_nodup
  mem_physicalOrder := D.mem_physicalOrder
  privateOutput := D.privateOutput
  finite_privateOutput := D.finite_privateOutput
  circuit := (D.chain D.changes).castLayouts D.layout_zero D.layout_changes

/-- Every property of the composed changes holds for the circuit of the protocol read as a
distributed construction, which only identifies its layouts.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:45–49`. -/
theorem toDistributedConstruction_circuit_induction (hL : 0 < L)
    (Q : ∀ a b : Layout P, OriginalCircuit a b → Prop) (h : Q _ _ (D.chain D.changes)) :
    Q _ _ (D.toDistributedConstruction hL).circuit :=
  OriginalCircuit.castLayouts_induction Q _ _ h

/-- The configuration of the square read from the physical outputs of the parties: the site `v`
carries the physical output of its unit-square party.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:48–51`. -/
theorem physicalConfigEquiv_apply (f : (p : P) → Fin (D.physicalDimension p))
    (v : SquareLatticeVertex L L) :
    D.physicalConfigEquiv f v = Fin.cast (D.physicalDimension_site v) (f (D.site v)) := by
  simp only [physicalConfigEquiv]; rfl

/-- The physical density of the protocol, read as a construction of Theorem 5.2, is the physical
density of its actual final vector, with the party configurations identified with the
configurations of the square.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:36–49`, and Theorem 5.2,
`04-compression.tex:150–153`. -/
theorem physicalDensity_toDistributedConstruction (hL : 0 < L) :
    (D.toDistributedConstruction hL).physicalDensity =
      D.physicalDensity.submatrix D.physicalConfigEquiv D.physicalConfigEquiv := by
  classical
  let := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
  set e := D.physicalConfigEquiv
  set J := familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder
    D.physicalOrder_nodup D.mem_physicalOrder D.privateOutput
  set w := J (Layout.memCongr D.layout_changes (D.trajectory D.changes))
  have hC : (D.toDistributedConstruction hL).physicalDensity =
      Matrix.partialTraceRight (Matrix.euclideanOuterProduct w w) := by
    have h : (D.toDistributedConstruction hL).circuit.eval
        (D.toDistributedConstruction hL).input.vector =
        Layout.memCongr D.layout_changes (D.trajectory D.changes) := by
      have hx : (D.toDistributedConstruction hL).input.vector =
          Layout.memCongr D.layout_zero (D.trajectory 0) := by
        change D.input.vector =
          Layout.memCongr D.layout_zero (Layout.memCongr D.layout_zero.symm D.input.vector)
        rw [Layout.memCongr_symm D.layout_zero, LinearIsometryEquiv.apply_symm_apply]
      rw [hx]
      exact (OriginalCircuit.eval_castLayouts_memCongr _ _ _ _).trans
        (congrArg _ (D.eval_chain_trajectory _))
    change Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (J ((D.toDistributedConstruction hL).circuit.eval
        (D.toDistributedConstruction hL).input.vector))
      (J ((D.toDistributedConstruction hL).circuit.eval
        (D.toDistributedConstruction hL).input.vector))) = _
    rw [h]
  have hD : D.physicalDensity = Matrix.partialTraceRight
      ((Matrix.euclideanOuterProduct w w).submatrix (e.prodCongr (Equiv.refl _)).symm
        (e.prodCongr (Equiv.refl _)).symm) := by
    unfold physicalDensity
    congr 1
  rw [hC, hD, Matrix.partialTraceRight_submatrix_prod_equiv, Matrix.submatrix_submatrix]
  ext x y
  simp

/-- Every party has a positive physical dimension when `q` is positive.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:48–51`. -/
theorem physicalDimension_pos (hq : 0 < q) (p : P) : 0 < D.physicalDimension p := by
  by_cases hp : p ∈ Set.range D.site
  · obtain ⟨v, rfl⟩ := hp
    rw [D.physicalDimension_site]
    exact hq
  · rw [D.physicalDimension_eq_one p hp]
    exact one_pos

/-- The physical coordinate of a party read from a local index in `Fin q`: the index itself at
the unit-square party of a site, and the only coordinate elsewhere.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:25–26` and `158–159`. -/
def physicalOut (p : P) (i : Fin q) : Fin (D.physicalDimension p) :=
  ⟨i % D.physicalDimension p, Nat.mod_lt _ (D.physicalDimension_pos i.pos p)⟩

/-- Reading every party at the fold of its anchor inverts the identification of the physical
configurations of the parties with the configurations of the square.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:25–26` and `158–159`. -/
theorem physicalOut_foldVertex (hL : 0 < L) (x : Configuration L q) :
    (fun p ↦ D.physicalOut p (x (foldVertex hL (D.placement.anchor p)))) =
      D.physicalConfigEquiv.symm x := by
  rw [Equiv.eq_symm_apply]
  funext v
  rw [physicalConfigEquiv_apply]
  obtain ⟨h0, hx, hy⟩ := D.placement_site v
  have hanchor : D.placement.anchor (D.site v) = (v.1.1, v.2.1) := by
    simp [DyadicPlacement.anchor, dyadicAnchor, h0, hx, hy]
  rw [hanchor, foldVertex_of_lt hL v.1.2 v.2.2]
  ext
  simp [physicalOut, D.physicalDimension_site, Nat.mod_eq_of_lt (x v).2]

open DistributedOperatorContraction in
/-- **From a compressed density to an operator party network on dyadic anchors.** Let a
distributed operator contraction on the parties of a protocol be within `ε` of the physical
density of the protocol, with link alphabets of size at most `C₁ L ^ α`, at most `deg` links at
each party, and links only between parties of a common nonprivate gate. Enumerating its
alphabets gives an operator party network on the dyadic anchors of the protocol with these
bounds, the separation constant `b` of the protocol, and
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ ε + (2 C² + 2 C) L⁻¹⁰`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the conclusion of Theorem 5.2,
`04-compression.tex:150–175`, applied in §8.1, `07-assembly.tex:53–63`, with the density
estimate `eq:protocol-density`, `07-assembly.tex:33–41`. -/
theorem exists_partyNetwork_of_contractedOperator (hL : 0 < L) {Ω : StateSpace L q} {C : ℝ}
    {b k r : ℕ} (h : D.IsDistributionProtocol Ω C b k r) (hC : 0 ≤ C) (hΩ : ‖Ω‖ = 1)
    {_ : DecidableEq P} {Gate : Type} {_ : DecidableEq Gate} (gates : Finset Gate)
    (participants : Gate → Finset P) (root : Gate → P)
    (hroot : ∀ g ∈ gates, root g ∈ participants g) (Label : Gate → Type)
    [∀ g, Fintype (Label g)] (m : ℕ) (c : (g : Gate) → Label g → ℂ)
    (T : (p : P) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin m) →
        Matrix (Fin (D.physicalDimension p)) (Fin (D.physicalDimension p)) ℂ)
    {ε C₁ : ℝ} {α deg : ℕ}
    {ρ : Matrix ((p : P) → Fin (D.physicalDimension p)) ((p : P) → Fin (D.physicalDimension p)) ℂ}
    (hρ : ρ = D.physicalDensity.submatrix D.physicalConfigEquiv D.physicalConfigEquiv)
    (herr : Matrix.rectangularTraceNorm
      (contractedOperator gates participants root hroot Label m c T - ρ) ≤ ε)
    (hdim : ∀ e : Link gates participants root,
      (Fintype.card (alphabet gates participants root Label m e) : ℝ) ≤ C₁ * (L : ℝ) ^ α)
    (hinc : ∀ j, (incidentDistributedLinks gates participants root j).card ≤ deg)
    (hloc : ∀ e : Link gates participants root, ∀ j l,
      j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
        ∃ t < D.changes, ∃ g, j ∈ (D.step t).participants g ∧ l ∈ (D.step t).participants g) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (N : PartyNetwork P Λ (q * q)),
      DyadicPlacement.DegreeBounded N.src N.tgt deg ∧
      D.placement.SeparationBounded N.src N.tgt b ∧
      (∀ ℓ, (N.dim ℓ : ℝ) ≤ C₁ * (L : ℝ) ^ α) ∧
      Matrix.rectangularTraceNorm
        (N.operatorCoeff (fun p ↦ foldVertex hL (D.placement.anchor p)) -
          Matrix.euclideanOuterProduct Ω Ω) ≤ ε + (2 * (C * C) + 2 * C) / (L : ℝ) ^ 10 := by
  classical
  subst hρ
  set e := D.physicalConfigEquiv
  let N := toPartyNetwork gates participants root hroot Label m c T D.physicalOut D.physicalOut
  have hmem : ∀ ℓ : Link gates participants root,
      src gates participants root ℓ ∈ distributedLinkParties root ℓ.1 ∧
        tgt gates participants root ℓ ∈ distributedLinkParties root ℓ.1 := fun ℓ ↦ by
    rw [← endpoints_eq]
    simp
  refine ⟨Link gates participants root, inferInstance, inferInstance, N, ?_, ?_, hdim, ?_⟩
  · intro p
    refine (Finset.card_le_card_of_injOn Subtype.val (fun ℓ hℓ ↦ ?_)
      Subtype.val_injective.injOn).trans (hinc p)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    simp only [incidentDistributedLinks, Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨ℓ.2, ?_⟩
    rw [← endpoints_eq]
    rcases hℓ with h' | h'
    · simp [N, toPartyNetwork] at h'
      simp [h']
    · simp [N, toPartyNetwork] at h'
      simp [h']
  · exact h.separationBounded _ _ fun ℓ ↦ hloc ℓ _ _ (hmem ℓ).1 (hmem ℓ).2
  · have hσ : N.operatorCoeff (fun p ↦ foldVertex hL (D.placement.anchor p)) =
        (contractedOperator gates participants root hroot Label m c T).submatrix e.symm e.symm := by
      ext x y
      rw [operatorCoeff_toPartyNetwork, D.physicalOut_foldVertex hL x,
        D.physicalOut_foldVertex hL y]
      rfl
    have hsplit : N.operatorCoeff (fun p ↦ foldVertex hL (D.placement.anchor p)) -
        Matrix.euclideanOuterProduct Ω Ω =
        Matrix.reindex e e (contractedOperator gates participants root hroot Label m c T -
          D.physicalDensity.submatrix e e) +
          (D.physicalDensity - Matrix.euclideanOuterProduct Ω Ω) := by
      rw [hσ]
      ext x y
      simp
    rw [hsplit]
    refine (Matrix.rectangularTraceNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.rectangularTraceNorm_reindex]
      exact herr
    · exact h.rectangularTraceNorm_physicalDensity_sub_le (Nat.one_le_iff_ne_zero.mpr hL.ne')
        hC hΩ

end TNLean.PEPS.Approximation.DyadicProtocol

namespace TNLean.PEPS.Approximation

open Finset TNLean.PEPS.PairEffect

/-- A protocol with the bounds of §8 for fixed constants, on a square of some side `L ≥ 2`,
together with its unit target vector. These instances form the family of constructions to which
Theorem 5.2 is applied.
Source: Polynomial-PEPS manuscript (Sept 24 2026), `04-compression.tex:137–139` and
`07-assembly.tex:45–49`. -/
private structure ProtocolInstance (q : ℕ) (C : ℝ) (b k r : ℕ) where
  size : ℕ
  two_le : 2 ≤ size
  Party : Type
  [fintype : Fintype Party]
  protocol : DyadicProtocol size q Party
  target : StateSpace size q
  norm_target : ‖target‖ = 1
  isDistributionProtocol : protocol.IsDistributionProtocol target C b k r

attribute [local instance] ProtocolInstance.fintype

/-- The floor of a real number is at most its positive part. -/
private theorem natCast_floor_le_max (x : ℝ) : (⌊x⌋₊ : ℝ) ≤ max x 0 := by
  rcases le_total 0 x with hx | hx
  · exact (Nat.floor_le hx).trans (le_max_left _ _)
  · rw [Nat.floor_eq_zero.mpr (hx.trans_lt one_pos)]
    simp

/-- **The compressed dyadic operator network from the consequences of Proposition 7.1.** If,
for every `q ≥ 2` and `J, Δ > 0`, every gapped ground vector of a square Hamiltonian of large
side `L` has a dyadic distribution protocol with the bounds of §8, with constants chosen before
`L`, the Hamiltonian, and the ground vector, then the compressed dyadic operator network of
§8.1 exists for all large squares.

The protocols for all sizes, Hamiltonians, and ground vectors form one family of distributed
constructions with uniformly polynomial gate counts, constant arity and lifetime participation,
physical dimensions at most `q`, and exact polynomial gate expansions. Theorem 5.2 at accuracy
`L⁻⁵` gives one operator network per protocol, with constants fixed before the family member;
the link dimensions are polynomial, every link joins two parties of a common gate, and the
density error adds to the protocol estimate `‖ρ - |Ω⟩⟨Ω|‖₁ ≤ C L⁻¹⁰`. The separation hypothesis
of Lemma 8.2 follows from item 3 of Proposition 7.1.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `07-assembly.tex:9–63`, with
Theorem 5.2 `thm:compression`, `04-compression.tex:137–175`, and the order of constants of
`07-assembly.tex:179–203`. -/
theorem largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences
    (hprot : LargeSizeDyadicProtocolConsequences) : LargeSizeDyadicOperatorNetwork := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, b, k, r, L₀, hall⟩ := hprot q hq J Δ hJ hΔ
  let size : ProtocolInstance q C b k r → ℝ := fun i ↦ i.size
  have hsize : ∀ i, 2 ≤ size i := fun i ↦ by
    change (2 : ℝ) ≤ (i.size : ℝ)
    exact_mod_cast i.two_le
  let C₀ : ∀ i : ProtocolInstance q C b k r, DistributedConstruction i.Party := fun i ↦
    i.protocol.toDistributedConstruction (by have := i.two_le; omega)
  have hN₀ : ∀ i, ((C₀ i).circuit.nonprivateCount : ℝ) ≤ (max C 0 * b) * size i ^ 3 := by
    intro i
    have hD := i.isDistributionProtocol
    have hcount : (C₀ i).circuit.nonprivateCount =
        (i.protocol.chain i.protocol.changes).nonprivateCount :=
      OriginalCircuit.nonprivateCount_castLayouts _ _ _
    rw [hcount, DyadicProtocol.nonprivateCount_chain]
    have hsum : ∑ t ∈ range i.protocol.changes, (i.protocol.step t).nonprivateCount ≤
        i.protocol.changes * b := by
      simpa using Finset.sum_le_card_nsmul _ _ b fun t ht ↦
        hD.nonprivateCount_le t (Finset.mem_range.mp ht)
    calc ((∑ t ∈ range i.protocol.changes, (i.protocol.step t).nonprivateCount : ℕ) : ℝ)
        ≤ (i.protocol.changes : ℝ) * b := by exact_mod_cast hsum
      _ ≤ (max C 0 * size i ^ 3) * b := by
          gcongr
          exact hD.changes_le.trans (by gcongr; exact le_max_left _ _)
      _ = (max C 0 * b) * size i ^ 3 := by ring
  have hphysical₀ : ∀ i j, ((C₀ i).physicalDimension j : ℝ) ≤ q * size i ^ 0 := by
    intro i j
    change (i.protocol.physicalDimension j : ℝ) ≤ _
    rw [pow_zero, mul_one]
    by_cases hj : j ∈ Set.range i.protocol.site
    · obtain ⟨v, rfl⟩ := hj
      rw [i.protocol.physicalDimension_site]
    · rw [i.protocol.physicalDimension_eq_one j hj]
      exact_mod_cast (show 1 ≤ q by omega)
  have harity₀ : ∀ i g, ((C₀ i).circuit.participants g).card ≤ b := fun i ↦
    i.protocol.toDistributedConstruction_circuit_induction _
      (fun _ _ w ↦ ∀ g, (w.participants g).card ≤ b) fun g ↦ by
        obtain ⟨t, ht, g', hg'⟩ := i.protocol.exists_participants_chain _ g
        rw [hg']
        exact i.isDistributionProtocol.card_participants_le t ht g'
  have hlifetime₀ : ∀ i j, (C₀ i).circuit.participationCount j ≤ b := fun i j ↦
    i.protocol.toDistributedConstruction_circuit_induction _
      (fun _ _ w ↦ w.participationCount j ≤ b) <| by
        rw [DyadicProtocol.participationCount_chain]
        exact i.isDistributionProtocol.participation_le j
  have hpow : ∀ i, C * size i ^ k ≤ max C 0 * size i ^ k := fun i ↦
    mul_pow_le_max_zero_mul_pow C (by linarith [hsize i]) k
  have hmonomial₀ : ∀ i, ∃ K : ℕ, (C₀ i).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ max C 0 * size i ^ k := fun i ↦
    ⟨⌊C * size i ^ k⌋₊, i.protocol.toDistributedConstruction_circuit_induction _
      (fun _ _ w ↦ w.IsMonomialBounded _)
      (i.protocol.isMonomialBounded_chain _ i.isDistributionProtocol.monomialBounded),
      (natCast_floor_le_max _).trans (max_le (hpow i)
        (mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith [hsize i]) _)))⟩
  have htermwise₀ : ∀ i, (C₀ i).circuit.IsTermwiseBounded r (max C 0 * size i ^ k) := fun i ↦
    i.protocol.toDistributedConstruction_circuit_induction _
      (fun _ _ w ↦ w.IsTermwiseBounded r _)
      ((i.protocol.isExpansionBounded_chain _
        i.isDistributionProtocol.expansionBounded).isTermwiseBounded (hpow i))
  obtain ⟨C_p, α, hCp, hα, hfam⟩ :=
    DistributedConstruction.exists_uniform_sampled_network size hsize (fun i ↦ i.Party) C₀
      b 3 0 r k k (max C 0 * b) q (max C 0) (max C 0)
      hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀ htermwise₀ 5 (by norm_num)
  refine ⟨1 + (2 * (C * C) + 2 * C), C_p, α, b, 2 * b * (b - 1), b, L₀, ?_⟩
  intro L hL hL₀ H E₀ Ω hΩ
  obtain ⟨P, hP, D, hD⟩ := hall L hL hL₀ H E₀ Ω hΩ
  let i : ProtocolInstance q C b k r := ⟨L, hL, P, D, Ω, hΩ.1, hD⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, T, herr, hdim, hinc, hloc⟩ := hfam i
  have hL0 : 0 < L := by omega
  have hC : 0 ≤ C := by
    have h1 : (1 : ℝ) ≤ Fintype.card P := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨D.site (⟨0, hL0⟩, ⟨0, hL0⟩)⟩
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (sq_nonneg (L : ℝ))
    linarith [hD.card_le]
  classical
  obtain ⟨Λ, _, _, N, hdeg, hsep, hdimN, hnorm⟩ :=
    D.exists_partyNetwork_of_contractedOperator hL0 hD hC hΩ.1 _ _ _ _ _ _ _ T
      (D.physicalDensity_toDistributedConstruction hL0) herr hdim hinc fun e j l hj hl ↦ by
        obtain ⟨g, hjg, hlg⟩ := hloc e j l hj hl
        refine D.toDistributedConstruction_circuit_induction hL0
          (fun _ _ w ↦ ∀ g, j ∈ w.participants g → l ∈ w.participants g →
            ∃ t < D.changes, ∃ g', j ∈ (D.step t).participants g' ∧
              l ∈ (D.step t).participants g') (fun g hjg hlg ↦ ?_) g hjg hlg
        obtain ⟨t, ht, g', hg'⟩ := D.exists_participants_chain _ g
        exact ⟨t, ht, g', hg' ▸ hjg, hg' ▸ hlg⟩
  refine ⟨P, Λ, hP, inferInstance, inferInstance, inferInstance, N, D.placement, hD.inGrid,
    hD.blockBounded, hdeg, hsep, fun ℓ ↦ (hdimN ℓ).trans_eq (by rw [Real.rpow_natCast]), ?_⟩
  have hx : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hx5 : (0 : ℝ) < (L : ℝ) ^ 5 := by positivity
  have hpow : (L : ℝ) ^ (-(5 : ℝ)) = 1 / (L : ℝ) ^ 5 := by
    rw [Real.rpow_neg (by positivity), show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  refine hnorm.trans ?_
  change (L : ℝ) ^ (-(5 : ℝ)) + _ ≤ _
  rw [hpow, add_div (1 : ℝ)]
  have h10 : (L : ℝ) ^ 5 ≤ (L : ℝ) ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hnn : 0 ≤ 2 * (C * C) + 2 * C := by positivity
  exact add_le_add le_rfl (div_le_div_of_nonneg_left hnn hx5 h10)

/-- **Theorem 1.1 from the consequences of Proposition 7.1.** The existence, for all large
squares, of dyadic distribution protocols with the bounds of §8 implies the uniform polynomial
PEPS approximation of gapped square-grid ground states.

This is a conditional form of Theorem 1.1: the hypothesis, a weakened form of Proposition 7.1,
is not proved.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Theorem 1.1 `thm:main`,
`00-introduction.tex:36–57`, and its proof in §8, `07-assembly.tex:9–214`. -/
theorem polynomialPEPSApproximation_of_largeSizeDyadicProtocolConsequences
    (h : LargeSizeDyadicProtocolConsequences) : PolynomialPEPSApproximation :=
  polynomialPEPSApproximation_of_largeSizeDyadicOperatorNetwork
    (largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences h)

end TNLean.PEPS.Approximation
