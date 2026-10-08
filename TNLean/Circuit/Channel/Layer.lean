/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit
import QICLean.Channel.KrausCPTP

/-!
# Local channel circuits and their light cone

A local channel circuit of depth `T` on a bond geometry `bond : β → Set ι`
(`TNLean.Circuit.Geometry`) is a composition of `T` layers, each a composition of
trace-preserving completely positive maps (channels) acting on pairwise disjoint bonds. On the
ring of `N` sites the bonds are the pairs of neighbouring sites `{k, k + 1}`. These circuits act
on density matrices. They are the mixed-state counterpart of the unitary local circuits of
`TNLean.Circuit.LocalCircuit`, and they are the operations of a two-way equivalence of
periodic density families by local channel circuits: local channels, fixed product ancillas
and discarding, with no free classical communication.

A channel on a bond is given by Kraus operators acting on that bond, so a gate of a unitary
layer is the special case of a single unitary Kraus operator. The two facts about unitary
circuits used for the lower bound of arXiv:2307.01696 survive this generalization:

* the backward light cone: the Heisenberg dual of a local channel circuit of depth `T` maps an
  operator acting on `X` to an operator acting on the light cone of radius `T` of `X`
  (`channelCircuitDual_mem_supportedOperators_lightCone`), on the ring the sites within ring
  distance `T` of `X` (`channelCircuitDual_mem_supportedOperators`);
* a density matrix prepared from a product density by such a circuit has vanishing connected
  correlations for operators on sets with disjoint light cones
  (`IsBondChannelPreparedInDepth.trace_mul_mul_eq`), on the ring for operators at ring
  distance larger than `2T` (`trace_mul_mul_eq_of_isChannelPreparedInDepth`).

Unlike the unitary case, the Heisenberg dual of a channel is not multiplicative. The
factorization uses instead that the dual of one layer is multiplicative on pairs of operators
whose one-step neighbourhoods are disjoint, since no gate of the layer meets both
(`BondChannelLayer.dual_mul`).

## Conventions

Sites, bonds and supports are those of `TNLean.Circuit.LocalCircuit`. A gate is an operator on
all the sites given by a finite family of Kraus operators `K_j` acting on its bond with
`∑_j K_j† K_j = 1`; its map on states is `ρ ↦ ∑_j K_j ρ K_j†` and its Heisenberg dual is
`A ↦ ∑_j K_j† A K_j`. Layers are listed in the order in which they are applied.

## Main definitions

* `QuantumCircuit.BondChannelLayer` — one layer of channels on pairwise disjoint bonds, and
  `QuantumCircuit.ChannelLayer`, its ring specialization.
* `QuantumCircuit.BondChannelLayer.map`, `QuantumCircuit.BondChannelLayer.dual` — its map on
  states and its Heisenberg dual.
* `QuantumCircuit.channelCircuitMap`, `QuantumCircuit.channelCircuitDual` — a local channel
  circuit and its Heisenberg dual.
* `QuantumCircuit.IsBondChannelPreparedInDepth`, `QuantumCircuit.IsChannelPreparedInDepth` —
  a density matrix obtained from a product density by a local channel circuit of depth `T`.

## Main results

* `QuantumCircuit.channelCircuitMap_isKrausCPTP` — a local channel circuit is a
  trace-preserving completely positive map.
* `QuantumCircuit.trace_channelCircuitMap_mul` — Schrödinger–Heisenberg duality.
* `QuantumCircuit.channelCircuitDual_mem_supportedOperators_lightCone`,
  `QuantumCircuit.channelCircuitDual_mem_supportedOperators` — the backward light cone.
* `QuantumCircuit.channelCircuitMap_map_toChannelLayer` — a unitary local circuit is the
  local channel circuit with one Kraus operator per gate.
* `QuantumCircuit.IsBondChannelPreparedInDepth.trace_mul_mul_eq`,
  `QuantumCircuit.trace_mul_mul_eq_of_isChannelPreparedInDepth` — factorization of
  expectations of operators with disjoint light cones, on the ring of operators separated by
  more than `2T`.

## Follow-ups

Ancillas and blocking with a change of local dimension, approximate equivalence in trace
norm, and measurements with feedforward are not treated here.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), main text before Theorem 1 (local circuits)
  and Supplemental Material, proof of Theorem 1 (light cone).
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), main text, paragraph "Quantum circuits and
  LOCC": Definition 1 (depth-`ℓ` quantum circuits) and the circuits
  `V' = U_ℓ V_ℓ ⋯ U_1 V_1 U_0` with product ancillas and local unitaries between layers;
  discarding the ancillas of such a gate gives a channel on the same pair.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Traces against product densities -/

theorem _root_.Matrix.trace_rectKronecker (m : ι → Matrix (Fin d) (Fin d) ℂ) :
    trace (rectKronecker m) = ∏ i, trace (m i) := by
  simp only [trace, diag_apply, rectKronecker_apply]
  exact (Fintype.prod_sum fun i j ↦ m i j j).symm

private theorem trace_rectKronecker_eq_one {σ : ι → Matrix (Fin d) (Fin d) ℂ}
    (hσ : ∀ i, (σ i).PosSemidef ∧ trace (σ i) = 1) : trace (rectKronecker σ) = 1 := by
  rw [trace_rectKronecker]
  exact Finset.prod_eq_one fun i _ ↦ (hσ i).2

/-- Product densities factorize expectations of products of operators on disjoint sets of
sites: `tr(σ AB) tr σ = tr(σ A) tr(σ B)` for `σ = ⊗ᵢ σᵢ`. -/
theorem trace_rectKronecker_mul_mul {S S' : Set ι} (hSS' : Disjoint S S')
    (σ : ι → Matrix (Fin d) (Fin d) ℂ) {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d S) (hB : B ∈ supportedOperators d S') :
    trace (rectKronecker σ * (A * B)) * trace (rectKronecker σ) =
      trace (rectKronecker σ * A) * trace (rectKronecker σ * B) := by
  let φ := traceLinearMap (ι → Fin d) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (rectKronecker σ)
  rw [mul_comm]
  refine eq_of_mem_supportedOperators₂ (trace (rectKronecker σ) • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change trace (rectKronecker σ) * trace (rectKronecker σ * (rectKronecker m * rectKronecker m')) =
    trace (rectKronecker σ * rectKronecker m) * trace (rectKronecker σ * rectKronecker m')
  simp only [rectKronecker_mul, trace_rectKronecker, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Set.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

/-! ### Kraus maps on the sites -/

private theorem krausMap_apply {κ : Type*} [Fintype κ]
    (K : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (X : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    rectangularKrausMap K X = ∑ j, K j * X * (K j)ᴴ :=
  rfl

/-- Kraus maps whose Kraus operators commute with each other commute as maps. -/
theorem commute_rectangularKrausMap {κ κ' : Type*} [Fintype κ] [Fintype κ']
    {K : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ}
    {K' : κ' → Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (h : ∀ i j, Commute (K i) (K' j)) :
    Commute (rectangularKrausMap K : Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ))
      (rectangularKrausMap K') := by
  refine (commute_iff_eq _ _).mpr (LinearMap.ext fun X ↦ ?_)
  simp only [Module.End.mul_apply, krausMap_apply, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  calc K i * (K' j * X * (K' j)ᴴ) * (K i)ᴴ = K i * K' j * X * (K i * K' j)ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = K' j * K i * X * (K' j * K i)ᴴ := by rw [(h i j).eq]
    _ = K' j * (K i * X * (K i)ᴴ) * (K' j)ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- Kraus maps are dual for the trace pairing to the Kraus maps of the adjoint operators:
`tr(∑ⱼ Kⱼ ρ Kⱼ† A) = tr(ρ ∑ⱼ Kⱼ† A Kⱼ)`, for rectangular Kraus operators. -/
theorem trace_rectangularKrausMap_mul {κ α β : Type*} [Fintype κ] [Fintype α] [Fintype β]
    (K : κ → Matrix β α ℂ) (ρ : Matrix α α ℂ) (A : Matrix β β ℂ) :
    trace (rectangularKrausMap K ρ * A) = trace (ρ * rectangularKrausMap (fun j ↦ (K j)ᴴ) A) := by
  change trace ((∑ j, K j * ρ * (K j)ᴴ) * A) = trace (ρ * ∑ j, (K j)ᴴ * A * (K j)ᴴᴴ)
  simp only [conjTranspose_conjTranspose, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show K j * ρ * (K j)ᴴ * A = K j * (ρ * ((K j)ᴴ * A)) by simp only [Matrix.mul_assoc],
    trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- A Heisenberg-picture map *acts on the sites `S`*: it fixes the operators acting off `S`,
preserves the operators acting on any set containing `S`, and commutes with multiplication by
operators acting off `S` on either side. The Heisenberg dual of a gate on the bond `bond b`
acts on `bond b`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the light cone of a local
circuit), here for the dual of a channel. -/
structure IsHeisenbergLocal (S : Set ι)
    (φ : Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)) : Prop where
  map_eq_self : ∀ A ∈ supportedOperators d Sᶜ, φ A = A
  map_mem : ∀ Z, S ⊆ Z → ∀ A ∈ supportedOperators d Z, φ A ∈ supportedOperators d Z
  map_mul_right : ∀ A, ∀ B ∈ supportedOperators d Sᶜ, φ (A * B) = φ A * B
  map_mul_left : ∀ A, ∀ B ∈ supportedOperators d Sᶜ, φ (B * A) = B * φ A

namespace IsHeisenbergLocal

variable {S S' : Set ι} {φ ψ : Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)}

theorem mono (h : IsHeisenbergLocal S φ) (hSS' : S ⊆ S') : IsHeisenbergLocal S' φ where
  map_eq_self A hA :=
    h.map_eq_self A (supportedOperators_mono (Set.compl_subset_compl.mpr hSS') hA)
  map_mem Z hZ := h.map_mem Z (hSS'.trans hZ)
  map_mul_right A B hB :=
    h.map_mul_right A B (supportedOperators_mono (Set.compl_subset_compl.mpr hSS') hB)
  map_mul_left A B hB :=
    h.map_mul_left A B (supportedOperators_mono (Set.compl_subset_compl.mpr hSS') hB)

theorem one (S : Set ι) :
    IsHeisenbergLocal S (1 : Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)) where
  map_eq_self _ _ := rfl
  map_mem _ _ _ hA := hA
  map_mul_right _ _ _ := rfl
  map_mul_left _ _ _ := rfl

theorem mul (hφ : IsHeisenbergLocal S φ) (hψ : IsHeisenbergLocal S ψ) :
    IsHeisenbergLocal S (φ * ψ) where
  map_eq_self A hA := by rw [Module.End.mul_apply, hψ.map_eq_self A hA, hφ.map_eq_self A hA]
  map_mem Z hZ A hA := hφ.map_mem Z hZ _ (hψ.map_mem Z hZ A hA)
  map_mul_right A B hB := by
    rw [Module.End.mul_apply, hψ.map_mul_right A B hB, hφ.map_mul_right _ B hB,
      Module.End.mul_apply]
  map_mul_left A B hB := by
    rw [Module.End.mul_apply, hψ.map_mul_left A B hB, hφ.map_mul_left _ B hB,
      Module.End.mul_apply]

end IsHeisenbergLocal

/-- The Heisenberg dual `A ↦ ∑ⱼ Kⱼ† A Kⱼ` of a channel whose Kraus operators act on `S` acts
on `S`. -/
theorem isHeisenbergLocal_rectangularKrausMap {S : Set ι} {κ : Type*} [Fintype κ]
    {K : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ} (hK : ∀ j, K j ∈ supportedOperators d S)
    (hsum : ∑ j, (K j)ᴴ * K j = 1) :
    IsHeisenbergLocal S (rectangularKrausMap fun j ↦ (K j)ᴴ) := by
  have happ (A : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
      rectangularKrausMap (fun j ↦ (K j)ᴴ) A = ∑ j, (K j)ᴴ * A * K j := by
    simp only [krausMap_apply, conjTranspose_conjTranspose]
  have hcomm {B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hB : B ∈ supportedOperators d Sᶜ)
    (j : κ) :
      Commute B (K j) :=
    commute_of_mem_supportedOperators disjoint_compl_left hB (hK j)
  have hcomm' {B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hB : B ∈ supportedOperators d Sᶜ)
    (j : κ) :
      Commute (K j)ᴴ B :=
    commute_of_mem_supportedOperators disjoint_compl_right (star_mem_supportedOperators (hK j)) hB
  refine ⟨fun A hA ↦ ?_, fun Z hZ A hA ↦ ?_, fun A B hB ↦ ?_, fun A B hB ↦ ?_⟩
  · rw [happ]
    calc ∑ j, (K j)ᴴ * A * K j = ∑ j, (K j)ᴴ * K j * A :=
          Finset.sum_congr rfl fun j _ ↦ by
            rw [Matrix.mul_assoc, (hcomm hA j).eq, ← Matrix.mul_assoc]
      _ = A := by rw [← Finset.sum_mul, hsum, Matrix.one_mul]
  · rw [happ]
    have hKZ (j : κ) := supportedOperators_mono hZ (hK j)
    exact Submodule.sum_mem _ fun j _ ↦ mul_mem_supportedOperators
      (mul_mem_supportedOperators (star_mem_supportedOperators (hKZ j)) hA) (hKZ j)
  · rw [happ, happ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Matrix.mul_assoc, (hcomm hB j).eq]
  · rw [happ, happ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [← Matrix.mul_assoc, (hcomm' hB j).eq]

/-! ### Trace pairing of commuting products -/

/-- If each `f i` is dual to `g i` for the trace pairing, then the product of the commuting
maps `f i` is dual to the product of the commuting maps `g i`. -/
theorem trace_noncommProd_mul {κ : Type*} (s : Finset κ)
    (f g : κ → Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ))
    (hf : (s : Set κ).Pairwise (Function.onFun Commute f))
    (hg : (s : Set κ).Pairwise (Function.onFun Commute g))
    (h : ∀ i ∈ s, ∀ ρ A, trace (f i ρ * A) = trace (ρ * g i A))
    (ρ A : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    trace (s.noncommProd f hf ρ * A) = trace (ρ * s.noncommProd g hg A) := by
  induction s using Finset.cons_induction generalizing ρ A with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.noncommProd_cons, Finset.noncommProd_cons', Module.End.mul_apply,
      Module.End.mul_apply, h a (Finset.mem_cons_self a s),
      ih _ _ (fun i hi ↦ h i (Finset.mem_cons_of_mem hi))]

/-! ### Channel layers and circuits on a bond geometry -/

section Bonds

variable {β : Type*} {bond : β → Set ι}

/-- One layer of a local channel circuit on the bond geometry `bond`: for `b` in a finite set
`bonds` of pairwise disjoint bonds, a channel on the bond `bond b`, given by Kraus operators
`kraus b j` acting on that bond with `∑ⱼ (kraus b j)† (kraus b j) = 1`.

Source: arXiv:2307.01696, main text before Theorem 1 (layers of a local circuit), with each
unitary gate replaced by a channel on the same bond, as for the local operations of
arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (gates acting with
product ancillas on nearest-neighbour pairs of a lattice). -/
structure BondChannelLayer (d : ℕ) (bond : β → Set ι) where
  /-- The bonds carrying a channel. -/
  bonds : Finset β
  /-- The number of Kraus operators of the channel on the bond `b`. -/
  r : β → ℕ
  /-- The Kraus operators of the channel on the bond `b`, as operators on all the sites. -/
  kraus : (b : β) → Fin (r b) → Matrix (ι → Fin d) (ι → Fin d) ℂ
  kraus_mem_supportedOperators : ∀ b ∈ bonds, ∀ j, kraus b j ∈ supportedOperators d (bond b)
  sum_kraus : ∀ b ∈ bonds, ∑ j, (kraus b j)ᴴ * kraus b j = 1
  pairwiseDisjoint : (bonds : Set β).PairwiseDisjoint bond

namespace BondChannelLayer

/-- The channel `ρ ↦ ∑ⱼ Kⱼ ρ Kⱼ†` on the bond `b`.

It is defined for every `b`, as `BondLayer.gate` is, but it is a channel on that bond only for
`b ∈ L.bonds`, where the fields `kraus_mem_supportedOperators` and `sum_kraus` hold. -/
noncomputable def gateMap (L : BondChannelLayer d bond) (b : β) :
    Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
  rectangularKrausMap (L.kraus b)

/-- The Heisenberg dual `A ↦ ∑ⱼ Kⱼ† A Kⱼ` of the channel on the bond `b`, meaningful for
`b ∈ L.bonds` as for `gateMap`. -/
noncomputable def gateDual (L : BondChannelLayer d bond) (b : β) :
    Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
  rectangularKrausMap fun j ↦ (L.kraus b j)ᴴ

theorem gateMap_commute (L : BondChannelLayer d bond) :
    (L.bonds : Set β).Pairwise (Function.onFun Commute L.gateMap) :=
  fun k hk l hl hkl ↦ commute_rectangularKrausMap fun i j ↦
    commute_of_mem_supportedOperators (L.pairwiseDisjoint hk hl hkl)
      (L.kraus_mem_supportedOperators k hk i) (L.kraus_mem_supportedOperators l hl j)

theorem gateDual_commute (L : BondChannelLayer d bond) (s : Finset β) (hs : s ⊆ L.bonds) :
    (s : Set β).Pairwise (Function.onFun Commute L.gateDual) :=
  fun k hk l hl hkl ↦ commute_rectangularKrausMap fun i j ↦
    commute_of_mem_supportedOperators (L.pairwiseDisjoint (hs hk) (hs hl) hkl)
      (star_mem_supportedOperators (L.kraus_mem_supportedOperators k (hs hk) i))
      (star_mem_supportedOperators (L.kraus_mem_supportedOperators l (hs hl) j))

/-- The channel of a layer on states: the composition of its commuting channels.

Source: arXiv:2307.01696, main text before Theorem 1 (a layer of a local circuit). -/
noncomputable def map (L : BondChannelLayer d bond) :
    Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
  L.bonds.noncommProd L.gateMap L.gateMap_commute

/-- The composition of the Heisenberg duals of the channels of `L` on a subset `s` of its
bonds. -/
noncomputable def partialDual (L : BondChannelLayer d bond) (s : Finset β) (hs : s ⊆ L.bonds) :
    Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
  s.noncommProd L.gateDual (L.gateDual_commute s hs)

/-- The Heisenberg dual of a layer. -/
noncomputable def dual (L : BondChannelLayer d bond) :
    Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
  L.partialDual L.bonds subset_rfl

theorem gateMap_isKrausCPTP (L : BondChannelLayer d bond) {b : β} (hb : b ∈ L.bonds) :
    IsKrausCPTP (L.gateMap b) :=
  rectangularKrausMap_isKrausCPTP _ (L.sum_kraus b hb)

/-- The channel of a layer is trace-preserving and completely positive. -/
theorem map_isKrausCPTP (L : BondChannelLayer d bond) : IsKrausCPTP L.map :=
  Finset.noncommProd_induction _ _ _ IsKrausCPTP
    (fun _ _ ha hb ↦ by rw [Module.End.mul_eq_comp]; exact isKrausCPTP_comp hb ha)
    (by rw [Module.End.one_eq_id]; exact isKrausCPTP_id) fun _ hk ↦ L.gateMap_isKrausCPTP hk

/-- Schrödinger–Heisenberg duality for a layer: `tr(Φ(ρ) A) = tr(ρ Φ†(A))`. -/
theorem trace_map_mul (L : BondChannelLayer d bond) (ρ A : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    trace (L.map ρ * A) = trace (ρ * L.dual A) :=
  trace_noncommProd_mul L.bonds L.gateMap L.gateDual L.gateMap_commute
    (L.gateDual_commute _ subset_rfl) (fun k _ ↦ trace_rectangularKrausMap_mul (L.kraus k)) ρ A

theorem partialDual_isHeisenbergLocal (L : BondChannelLayer d bond) (s : Finset β)
    (hs : s ⊆ L.bonds) {S : Set ι} (hS : ∀ k ∈ s, bond k ⊆ S) :
    IsHeisenbergLocal S (L.partialDual s hs) :=
  Finset.noncommProd_induction _ _ _ (IsHeisenbergLocal S) (fun _ _ ha hb ↦ ha.mul hb)
    (IsHeisenbergLocal.one S) fun k hk ↦
      (isHeisenbergLocal_rectangularKrausMap (L.kraus_mem_supportedOperators k (hs hk))
        (L.sum_kraus k (hs hk))).mono (hS k hk)

/-- Splitting the bonds of `s` by a predicate splits the partial dual into a product. -/
theorem partialDual_eq_filter_mul (L : BondChannelLayer d bond) (s : Finset β)
    (hs : s ⊆ L.bonds) (p : β → Prop) [DecidablePred p] :
    L.partialDual s hs =
      L.partialDual (s.filter p) ((Finset.filter_subset _ _).trans hs) *
        L.partialDual (s.filter fun k ↦ ¬ p k) ((Finset.filter_subset _ _).trans hs) := by
  classical
  rw [partialDual, partialDual, partialDual,
    Finset.noncommProd_congr (Finset.filter_union_filter_not_eq p s).symm (fun _ _ ↦ rfl)]
  exact Finset.noncommProd_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _) _ _

/-- The part of a partial dual on the bonds missing `X` acts off `X`. -/
private theorem partialDual_filter_not_isHeisenbergLocal (L : BondChannelLayer d bond)
    (s : Finset β) (hs : s ⊆ L.bonds) (X : Set ι)
    [DecidablePred fun k : β ↦ (bond k ∩ X).Nonempty] :
    IsHeisenbergLocal Xᶜ
      (L.partialDual (s.filter fun k ↦ ¬ (bond k ∩ X).Nonempty)
        ((Finset.filter_subset _ _).trans hs)) :=
  L.partialDual_isHeisenbergLocal _ _ fun _ hk j hj hjX ↦
    (Finset.mem_filter.mp hk).2 ⟨j, hj, hjX⟩

/-- The part of a partial dual on the bonds meeting `X` acts on the one-step neighbourhood
of `X`. -/
private theorem partialDual_filter_isHeisenbergLocal (L : BondChannelLayer d bond)
    (s : Finset β) (hs : s ⊆ L.bonds) (X : Set ι)
    [DecidablePred fun k : β ↦ (bond k ∩ X).Nonempty] :
    IsHeisenbergLocal (bondNeighbourhood bond X)
      (L.partialDual (s.filter fun k ↦ (bond k ∩ X).Nonempty)
        ((Finset.filter_subset _ _).trans hs)) :=
  L.partialDual_isHeisenbergLocal _ _ fun _ hk ↦
    bond_subset_bondNeighbourhood (Finset.mem_filter.mp hk).2

/-- Any part of the dual of one layer enlarges the support of an operator to at most its
one-step neighbourhood. -/
theorem partialDual_mem_supportedOperators (L : BondChannelLayer d bond) (s : Finset β)
    (hs : s ⊆ L.bonds) {X : Set ι} {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d X) :
    L.partialDual s hs A ∈ supportedOperators d (bondNeighbourhood bond X) := by
  classical
  rw [L.partialDual_eq_filter_mul s hs fun k ↦ (bond k ∩ X).Nonempty, Module.End.mul_apply,
    (L.partialDual_filter_not_isHeisenbergLocal s hs X).map_eq_self A (by rwa [compl_compl])]
  exact (L.partialDual_filter_isHeisenbergLocal s hs X).map_mem _ subset_rfl A
    (supportedOperators_mono (subset_bondNeighbourhood X) hA)

/-- **Light cone of one layer.** The Heisenberg dual of a layer enlarges the support of an
operator to at most its one-step neighbourhood. -/
theorem dual_mem_supportedOperators (L : BondChannelLayer d bond) {X : Set ι}
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d X) :
    L.dual A ∈ supportedOperators d (bondNeighbourhood bond X) :=
  L.partialDual_mem_supportedOperators _ _ hA

/-- The Heisenberg dual of a layer is multiplicative on operators acting on sets whose
one-step neighbourhoods are disjoint: no channel of the layer acts on both. -/
theorem dual_mul (L : BondChannelLayer d bond) {X Y : Set ι}
    (hXY : Disjoint (bondNeighbourhood bond X) (bondNeighbourhood bond Y))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y) :
    L.dual (A * B) = L.dual A * L.dual B := by
  classical
  have hP := L.partialDual_filter_isHeisenbergLocal L.bonds subset_rfl X
  have hQ := L.partialDual_filter_not_isHeisenbergLocal L.bonds subset_rfl X
  have hA' : A ∈ supportedOperators d Xᶜᶜ := by rwa [compl_compl]
  have hQB := L.partialDual_mem_supportedOperators
    (L.bonds.filter fun k ↦ ¬ (bond k ∩ X).Nonempty) (Finset.filter_subset _ _) hB
  have hQB' := supportedOperators_mono (fun _ hy hx ↦ Set.disjoint_left.mp hXY hx hy) hQB
  rw [dual, L.partialDual_eq_filter_mul L.bonds subset_rfl fun k ↦ (bond k ∩ X).Nonempty]
  simp only [Module.End.mul_apply]
  rw [hQ.map_mul_left B A hA', hP.map_mul_right A _ hQB', hQ.map_eq_self A hA',
    hP.map_eq_self _ hQB']

end BondChannelLayer

/-- The channel of a local channel circuit given by its list of layers, the head of the list
being applied first: `channelCircuitMap [L₁, …, L_T] = Φ_{L_T} ∘ ⋯ ∘ Φ_{L₁}`.

Source: arXiv:2307.01696, main text before Theorem 1 (depth-`T` local circuits), with channels
in place of unitary gates. -/
noncomputable def channelCircuitMap :
    List (BondChannelLayer d bond) → Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)
  | [] => 1
  | L :: Ls => channelCircuitMap Ls * L.map

/-- The Heisenberg dual of a local channel circuit:
`channelCircuitDual [L₁, …, L_T] = Φ_{L₁}† ∘ ⋯ ∘ Φ_{L_T}†`. -/
noncomputable def channelCircuitDual :
    List (BondChannelLayer d bond) → Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)
  | [] => 1
  | L :: Ls => L.dual * channelCircuitDual Ls

/-- A local channel circuit is trace-preserving and completely positive. -/
theorem channelCircuitMap_isKrausCPTP (Ls : List (BondChannelLayer d bond)) :
    IsKrausCPTP (channelCircuitMap Ls) := by
  induction Ls with
  | nil => exact isKrausCPTP_id
  | cons L Ls ih => exact isKrausCPTP_comp L.map_isKrausCPTP ih

theorem trace_channelCircuitMap (Ls : List (BondChannelLayer d bond))
    (ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ) : trace (channelCircuitMap Ls ρ) = trace ρ :=
  (channelCircuitMap_isKrausCPTP Ls).trace_map ρ

theorem posSemidef_channelCircuitMap (Ls : List (BondChannelLayer d bond))
    {ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hρ : ρ.PosSemidef) :
    (channelCircuitMap Ls ρ).PosSemidef :=
  (channelCircuitMap_isKrausCPTP Ls).map_posSemidef hρ

/-- Schrödinger–Heisenberg duality for a local channel circuit: `tr(Φ(ρ) A) = tr(ρ Φ†(A))`. -/
theorem trace_channelCircuitMap_mul (Ls : List (BondChannelLayer d bond))
    (ρ A : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    trace (channelCircuitMap Ls ρ * A) = trace (ρ * channelCircuitDual Ls A) := by
  induction Ls generalizing ρ A with
  | nil => rfl
  | cons L Ls ih =>
    simp only [channelCircuitMap, channelCircuitDual, Module.End.mul_apply]
    rw [ih, L.trace_map_mul]

/-- **Backward light cone.** The Heisenberg dual of a local channel circuit of depth `T` maps an
operator acting on the sites `X` to an operator acting on the light cone of radius `T` of `X`.

Source: arXiv:2307.01696, main text after Theorem 1 ("strictly finite light cone") and
Supplemental Material, proof of Theorem 1, here for channels in place of unitary gates. -/
theorem channelCircuitDual_mem_supportedOperators_lightCone (Ls : List (BondChannelLayer d bond))
    {X : Set ι} {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d X) :
    channelCircuitDual Ls A ∈ supportedOperators d (lightCone bond X Ls.length) := by
  induction Ls with
  | nil => exact hA
  | cons L Ls ih => exact L.dual_mem_supportedOperators ih

/-- The Heisenberg dual of a local channel circuit of depth `T` is multiplicative on operators
acting on sets whose light cones of radius `T` are disjoint. -/
theorem channelCircuitDual_mul_of_disjoint_lightCone (Ls : List (BondChannelLayer d bond))
    {X Y : Set ι} (hXY : Disjoint (lightCone bond X Ls.length) (lightCone bond Y Ls.length))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d X)
    (hB : B ∈ supportedOperators d Y) :
    channelCircuitDual Ls (A * B) = channelCircuitDual Ls A * channelCircuitDual Ls B := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    simp only [channelCircuitDual, Module.End.mul_apply]
    rw [ih (hXY.mono (lightCone_subset_succ X _) (lightCone_subset_succ Y _))]
    exact L.dual_mul hXY (channelCircuitDual_mem_supportedOperators_lightCone Ls hA)
      (channelCircuitDual_mem_supportedOperators_lightCone Ls hB)

/-! ### Unitary circuits as channel circuits -/

/-- Conjugation `X ↦ U X U†`, as a monoid homomorphism from matrices to maps. -/
noncomputable def conjMonoidHom :
    Matrix (ι → Fin d) (ι → Fin d) ℂ →* Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) where
  toFun := singleKrausMap
  map_one' := LinearMap.ext fun X ↦ by simp
  map_mul' U V := LinearMap.ext fun X ↦ by
    simp [conjTranspose_mul, Matrix.mul_assoc]

/-- A unitary layer as a channel layer with one Kraus operator, the unitary gate, per bond. -/
noncomputable def BondLayer.toChannelLayer (L : BondLayer d bond) : BondChannelLayer d bond where
  bonds := L.bonds
  r _ := 1
  kraus k _ := L.gate k
  kraus_mem_supportedOperators k hk _ := L.gate_mem_supportedOperators k hk
  sum_kraus k hk := by
    simpa [star_eq_conjTranspose] using Unitary.star_mul_self_of_mem (L.gate_mem_unitary k hk)
  pairwiseDisjoint := L.pairwiseDisjoint

/-- The channel of a unitary layer is conjugation by its unitary: `ρ ↦ U ρ U†`. -/
theorem BondLayer.toChannelLayer_map (L : BondLayer d bond) :
    L.toChannelLayer.map = singleKrausMap L.op := by
  have hgate (k : β) : L.toChannelLayer.gateMap k = conjMonoidHom (L.gate k) :=
    LinearMap.ext fun X ↦ Fin.sum_univ_one fun _ ↦ L.gate k * X * (L.gate k)ᴴ
  change _ = conjMonoidHom (L.bonds.noncommProd L.gate (L.gate_commute _ subset_rfl))
  rw [Finset.map_noncommProd]
  exact Finset.noncommProd_congr rfl (fun k _ ↦ hgate k) _

/-- The channel of a unitary local circuit is conjugation by its unitary. -/
theorem channelCircuitMap_map_toChannelLayer (Ls : List (BondLayer d bond)) :
    channelCircuitMap (Ls.map BondLayer.toChannelLayer) = singleKrausMap (circuitOp Ls) := by
  induction Ls with
  | nil => exact (conjMonoidHom.map_one).symm
  | cons L Ls ih =>
    change channelCircuitMap _ * L.toChannelLayer.map = conjMonoidHom (circuitOp Ls * L.op)
    rw [ih, L.toChannelLayer_map, map_mul]
    rfl

/-! ### Preparation from product densities -/

variable (bond) in
/-- A density matrix is *prepared in depth `T` by local channels* on the bond geometry `bond`
when it is a local channel circuit of depth `T` applied to a product density `⊗ᵢ σᵢ`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits
applied to product states"), with channels in place of unitary gates and product densities in
place of product vectors; arXiv:2103.13367, main text, paragraph "Quantum circuits and
LOCC", for circuits of local operations. -/
def IsBondChannelPreparedInDepth (T : ℕ) (ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ) : Prop :=
  ∃ Ls : List (BondChannelLayer d bond), Ls.length = T ∧
    ∃ σ : ι → Matrix (Fin d) (Fin d) ℂ, (∀ i, (σ i).PosSemidef ∧ trace (σ i) = 1) ∧
      ρ = channelCircuitMap Ls (rectKronecker σ)

/-- **Vanishing connected correlations beyond the light cone.** For a density matrix `ρ`
prepared in depth `T` by local channels and operators `A`, `B` acting on sets whose light
cones of radius `T` are disjoint, `tr(ρ AB) = tr(ρ A) tr(ρ B)`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 ("every connected
correlation for operators at a distance larger than `2T` vanishes"), here for channels in
place of unitary gates and product densities in place of product vectors. -/
theorem IsBondChannelPreparedInDepth.trace_mul_mul_eq {T : ℕ}
    {ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hρ : IsBondChannelPreparedInDepth bond T ρ)
    {X Y : Set ι} (hXY : Disjoint (lightCone bond X T) (lightCone bond Y T))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y) :
    trace (ρ * (A * B)) = trace (ρ * A) * trace (ρ * B) := by
  obtain ⟨Ls, rfl, σ, hσ, rfl⟩ := hρ
  have h := trace_rectKronecker_mul_mul hXY σ
    (channelCircuitDual_mem_supportedOperators_lightCone Ls hA)
    (channelCircuitDual_mem_supportedOperators_lightCone Ls hB)
  rw [trace_rectKronecker_eq_one hσ, mul_one] at h
  rw [trace_channelCircuitMap_mul, trace_channelCircuitMap_mul, trace_channelCircuitMap_mul,
    channelCircuitDual_mul_of_disjoint_lightCone Ls hXY hA hB, h]

end Bonds

/-! ### Channel circuits on the ring -/

section Ring

variable {N : ℕ} [NeZero N]

/-- One layer of a local channel circuit on the ring of `N` sites: for `k` in a finite set
`bonds` of pairwise disjoint pairs `{k, k + 1}`, a channel on that pair.

Source: arXiv:2307.01696, main text before Theorem 1 (layers of a local circuit), with each
unitary gate replaced by a channel on the same pair. -/
abbrev ChannelLayer (d N : ℕ) [NeZero N] := BondChannelLayer d (ringBond (N := N))

/-- **Light cone of one layer on the ring.** The Heisenberg dual of a layer enlarges the
support of an operator by at most one site on each side. -/
theorem ChannelLayer.dual_mem_supportedOperators (L : ChannelLayer d N) {X : Set (Fin N)}
    {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (hA : A ∈ supportedOperators d X) :
    L.dual A ∈ supportedOperators d (neighbourhood X 1) :=
  bondNeighbourhood_ringBond X ▸ BondChannelLayer.dual_mem_supportedOperators L hA

/-- On the ring, the Heisenberg dual of a layer is multiplicative on operators acting on sets
whose neighbourhoods of radius `1` are disjoint. -/
theorem ChannelLayer.dual_mul (L : ChannelLayer d N) {X Y : Set (Fin N)}
    (hXY : Disjoint (neighbourhood X 1) (neighbourhood Y 1))
    {A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y) :
    L.dual (A * B) = L.dual A * L.dual B :=
  BondChannelLayer.dual_mul L (by rwa [bondNeighbourhood_ringBond, bondNeighbourhood_ringBond])
    hA hB

/-- **Backward light cone on the ring.** The Heisenberg dual of a local channel circuit of
depth `T` maps an operator acting on the sites `X` to an operator acting on the sites within
ring distance `T` of `X`.

Source: arXiv:2307.01696, main text after Theorem 1 ("strictly finite light cone") and
Supplemental Material, proof of Theorem 1, here for channels in place of unitary gates. -/
theorem channelCircuitDual_mem_supportedOperators (Ls : List (ChannelLayer d N))
    {X : Set (Fin N)} {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ supportedOperators d X) :
    channelCircuitDual Ls A ∈ supportedOperators d (neighbourhood X Ls.length) :=
  lightCone_ringBond X Ls.length ▸ channelCircuitDual_mem_supportedOperators_lightCone Ls hA

/-- On the ring, the Heisenberg dual of a local channel circuit of depth `T` is multiplicative
on operators acting on sets whose `T`-neighbourhoods are disjoint. -/
theorem channelCircuitDual_mul (Ls : List (ChannelLayer d N)) {X Y : Set (Fin N)}
    (hXY : Disjoint (neighbourhood X Ls.length) (neighbourhood Y Ls.length))
    {A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (hA : A ∈ supportedOperators d X)
    (hB : B ∈ supportedOperators d Y) :
    channelCircuitDual Ls (A * B) = channelCircuitDual Ls A * channelCircuitDual Ls B :=
  channelCircuitDual_mul_of_disjoint_lightCone Ls
    (by rwa [lightCone_ringBond, lightCone_ringBond]) hA hB

/-- A density matrix is *prepared in depth `T` by local channels* on the ring when it is a
local channel circuit of depth `T` applied to a product density `⊗ᵢ σᵢ`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits
applied to product states"), with channels in place of unitary gates and product densities in
place of product vectors; arXiv:2103.13367, main text, paragraph "Quantum circuits and
LOCC", for circuits of local operations. -/
abbrev IsChannelPreparedInDepth (T : ℕ) (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    Prop :=
  IsBondChannelPreparedInDepth ringBond T ρ

/-- A density matrix prepared in depth `T` by local channels is a density matrix. -/
theorem IsChannelPreparedInDepth.posSemidef {T : ℕ} {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hρ : IsChannelPreparedInDepth T ρ) : ρ.PosSemidef ∧ trace ρ = 1 := by
  obtain ⟨Ls, -, σ, hσ, rfl⟩ := hρ
  exact ⟨posSemidef_channelCircuitMap Ls (finKronecker_posSemidef σ fun i ↦ (hσ i).1),
    (trace_channelCircuitMap Ls _).trans (trace_rectKronecker_eq_one hσ)⟩

/-- **Vanishing connected correlations beyond the light cone.** For a density matrix `ρ`
prepared in depth `T` by local channels and operators `A`, `B` acting on sets at ring distance
larger than `2T`, `tr(ρ AB) = tr(ρ A) tr(ρ B)`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 ("every connected
correlation for operators at a distance larger than `2T` vanishes"), here for channels in
place of unitary gates and product densities in place of product vectors. -/
theorem trace_mul_mul_eq_of_isChannelPreparedInDepth {T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (hρ : IsChannelPreparedInDepth T ρ)
    {X Y : Set (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y) :
    trace (ρ * (A * B)) = trace (ρ * A) * trace (ρ * B) :=
  IsBondChannelPreparedInDepth.trace_mul_mul_eq hρ
    (disjoint_lightCone_ringBond_of_isSeparatedBy hXY) hA hB

end Ring

end QuantumCircuit
