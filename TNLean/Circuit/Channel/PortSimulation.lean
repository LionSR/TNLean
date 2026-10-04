/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PortChannelRouting
import TNLean.Circuit.Channel.PortRegisters
import TNLean.Circuit.Channel.RegisterEncoding

/-!
# Simulating an entire matching through fixed physical ports

An arbitrary normalized Kraus channel on two neighboring `k`-qudit data registers is
placed on each bond of a matching. The placed channels commute because their spatial
supports are disjoint. One common routing moves every left data register into its right
scratch register, so all the channels act locally between the same forward and backward
routings. The whole matching has physical depth at most `2 * k`, independently of its
number of bonds, and acts identically on all other wires.

The ring has at least two spatial sites, so each two-register gate has distinct endpoints.
The one-site self-loop is a local operation and is not a two-register gate in this statement.
Source: Piroli, Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit.PortRegisters

variable {d N k : ℕ} [NeZero N]

private theorem left_ne_right (hN : 2 ≤ N) (i : Fin N) : i ≠ i + 1 := by
  intro h
  have h01 : (0 : Fin N) = 1 :=
    add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using h)
  have hN1 : N = 1 := Fin.one_eq_zero_iff.mp h01.symm
  omega

/-- A two-register Kraus channel placed on the data wires of one neighboring bond. -/
noncomputable def pairChannel (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (i : Fin N) :
    Module.End ℂ (Matrix (Fin (N * (1 + k + k)) → Fin d)
      (Fin (N * (1 + k + k)) → Fin d) ℂ) :=
  rectangularKrausMap fun a => embedOp (pairData i (i + 1) (left_ne_right hN i)) (A i a)

private theorem pairData_site_mem_bond {i : Fin N} (hne : i ≠ i + 1)
    (a : Fin (k + k)) : (layout N k).site (pairData i (i + 1) hne a) ∈ bond i := by
  refine Fin.addCases (fun t => ?_) (fun t => ?_) a
  · rw [pairData_left, site_data]
    exact Set.mem_insert i _
  · rw [pairData_right, site_data]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private theorem pair_kraus_mem_supportedOperators (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (i : Fin N) (a : Fin (r i)) :
    embedOp (pairData i (i + 1) (left_ne_right hN i)) (A i a) ∈
      supportedOperators d ((layout N k).site ⁻¹' bond i) := by
  apply supportedOperators_mono _
    (embedOp_mem_supportedOperators (pairData i (i + 1) (left_ne_right hN i)).injective _)
  rintro x ⟨j, rfl⟩
  exact pairData_site_mem_bond (left_ne_right hN i) j

/-- Channels placed on distinct bonds of a matching commute. -/
theorem pairChannel_commute (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint bond) :
    (K : Set (Fin N)).Pairwise (Function.onFun Commute (pairChannel hN A)) := by
  intro i hi j hj hij
  apply commute_rectangularKrausMap
  intro a b
  exact commute_of_mem_supportedOperators
    (Disjoint.preimage (layout N k).site (hK hi hj hij))
    (pair_kraus_mem_supportedOperators hN A i a) (pair_kraus_mem_supportedOperators hN A j b)

/-- The concrete product of the data-register channels on a matching. -/
noncomputable def matchingChannel (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint bond) :
    Module.End ℂ (Matrix (Fin (N * (1 + k + k)) → Fin d)
      (Fin (N * (1 + k + k)) → Fin d) ℂ) :=
  K.noncommProd (pairChannel hN A) (pairChannel_commute hN A K hK)

/-- An entire matching of normalized two-register channels shares one forward and backward
routing, and therefore has physical depth at most `2 * k`. -/
theorem matchingChannel_isPhysicalPortProtocol (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint bond)
    (hA : ∀ i ∈ K, ∑ a, (A i a)ᴴ * A i a = 1) :
    IsPhysicalPortProtocol (layout N k) (2 * k) (matchingChannel hN A K hK) := by
  unfold matchingChannel
  apply IsPhysicalPortProtocol.of_routed_family (layout N k) K (pairChannel hN A)
    (pairChannel_commute hN A K hK) (routingPermutation K hK)
    (routingPermutation_isPhysicalPortUnitary K hK)
  intro i hi
  unfold pairChannel
  rw [routingChannelConj_embeddedKraus]
  let e : Fin (k + k) ↪ Fin (N * (1 + k + k)) :=
    (pairData i (i + 1) (left_ne_right hN i)).trans (routingPermutation K hK).toEmbedding
  change IsPhysicalPortProtocol (layout N k) 0 (rectangularKrausMap fun a => embedOp e (A i a))
  apply IsPhysicalPortProtocol.onsite (P := layout N k) (i + 1)
  · intro a
    apply supportedOperators_mono _ (embedOp_mem_supportedOperators e.injective (A i a))
    rintro x ⟨j, rfl⟩
    exact routingPermutation_pairData_site K hK hi (left_ne_right hN i) j
  · exact sum_conjTranspose_embedOp_mul e (A i) (hA i hi)

end QuantumCircuit.PortRegisters

/-!
## Uniform physical-port cost for bounded-dimensional pair channels

Fix the physical dimension `d ≥ 2` and a local dimension bound `B`. A local system of
dimension at most `B` fits in `k = Nat.clog d B` memory qudits. Each matching of arbitrary
pair channels on the encoded systems is realized with physical depth at most `2 * k`,
independently of the chain length and the number of selected bonds. The local code and
the depth constant depend only on `d`, `B` and the local input dimension, not on `N`.

The input/output codes factor into onsite encodings. The extension outside the joint
code is CPTP, but need not factor onsite; it is executed only after the two registers
have been brought to one site. This theorem concerns the explicitly encoded matching
channel and the fixed-physical-port model. It does not remove an intermediate-dimension
bound from the unrestricted local-channel model, nor assert the source phase classification.

Source resource convention: Piroli, Styliaris and Cirac, arXiv:2103.13367,
Supplement pp. 7–8. The `2 * Nat.clog d B` bound is a derived register-routing estimate.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

noncomputable section

/-- The same bounded-dimensional local code is used at every system size. -/
def boundedPairRegisterCode {d B m : ℕ} (hd : 2 ≤ d) (hm : m ≤ B) :
    (Fin m × Fin m) ↪ (Fin (Nat.clog d B + Nat.clog d B) → Fin d) :=
  let e := registerBasisEmbedding (le_registerDimension hd hm)
  pairRegisterBasisEmbedding e e

/-- Every matching of bounded-dimensional pair channels has a concrete realization with
uniform physical depth. The chosen Kraus maps agree on their entire register space with
the specified CPTP code extension, and hence on all encoded inputs with the original maps.
The fallback density is used only outside the code, after the registers are colocated. -/
theorem exists_bounded_matching_simulation {d B m N : ℕ} [NeZero N]
    (hd : 2 ≤ d) (hm : m ≤ B) (hN : 2 ≤ N)
    (Φ : Fin N → Module.End ℂ (Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ))
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint bond)
    (hΦ : ∀ i ∈ K, IsKrausCPTP (Φ i))
    (ρ : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    ∃ (r : Fin N → ℕ)
      (A : ∀ i, Fin (r i) →
        Matrix (Fin (Nat.clog d B + Nat.clog d B) → Fin d)
          (Fin (Nat.clog d B + Nat.clog d B) → Fin d) ℂ),
      (∀ i ∈ K, rectangularKrausMap (A i) =
        registerEncodedMap (boundedPairRegisterCode hd hm) (boundedPairRegisterCode hd hm)
          ρ (Φ i)) ∧
      (∀ i ∈ K, ∀ X,
        rectangularKrausMap (A i) (singleKrausMap (registerEncoding
          (boundedPairRegisterCode hd hm)) X) =
        singleKrausMap (registerEncoding (boundedPairRegisterCode hd hm)) (Φ i X)) ∧
      IsPhysicalPortProtocol (PortRegisters.layout N (Nat.clog d B))
        (2 * Nat.clog d B) (PortRegisters.matchingChannel hN A K hK) := by
  classical
  let e := boundedPairRegisterCode hd hm
  let Ψ (i : Fin N) := if i ∈ K then Φ i else LinearMap.id
  have hΨ (i : Fin N) : IsKrausCPTP (Ψ i) := by
    dsimp [Ψ]
    split_ifs with hi
    · exact hΦ i hi
    · exact isKrausCPTP_id
  have hExt (i : Fin N) : IsKrausCPTP (registerEncodedMap e e ρ (Ψ i)) :=
    registerEncodedMap_isKrausCPTP e e hρ htr (hΨ i)
  choose r A hform hsum using hExt
  have hA (i : Fin N) : rectangularKrausMap (A i) = registerEncodedMap e e ρ (Ψ i) := by
    apply LinearMap.ext
    intro X
    exact (hform i X).symm
  refine ⟨r, A, ?_, ?_, ?_⟩
  · intro i hi
    simpa only [Ψ, ite_eq_left hi] using hA i
  · intro i hi X
    rw [hA]
    simpa only [Ψ, ite_eq_left hi] using registerEncodedMap_encoding e e ρ (Ψ i) X
  · exact PortRegisters.matchingChannel_isPhysicalPortProtocol hN A K hK (fun i _ => hsum i)

/-- Successive fixed-width matching layers have additive physical cost. The actual map is
the listed product, whose rightmost channel acts first. Free onsite channels may also be
inserted using `IsPhysicalPortProtocol.comp` without increasing this bound. -/
theorem IsPhysicalPortProtocol.list_prod_uniform {d N W : ℕ} [NeZero N]
    (P : PhysicalPortLayout N W) (c : ℕ)
    (L : List (Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)))
    (hL : ∀ Φ ∈ L, IsPhysicalPortProtocol P c Φ) :
    IsPhysicalPortProtocol P (c * L.length) L.prod := by
  induction L with
  | nil => simpa only [List.prod_nil, List.length_nil, Nat.mul_zero] using one (d := d) P
  | cons Φ L ih =>
    have htail := ih (fun Ψ hΨ => hL Ψ (List.mem_cons_of_mem Φ hΨ))
    have h := htail.comp (hL Φ List.mem_cons_self)
    simpa only [List.prod_cons, List.length_cons, Nat.mul_succ, Module.End.mul_eq_comp] using h

end

end QuantumCircuit
