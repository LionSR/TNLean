/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Conversion
import TNLean.Circuit.Channel.RegisterEncoding
import TNLean.Circuit.SiteEmbedding

/-!
# Product onsite register codes for arbitrary chain inputs

Each site is encoded and decoded independently. The global decoder is the product of
the local completed decoders, not a joint completion on the complement of the global
code. The global decoding/encoding identity holds on every chain operator and after
tensoring with an arbitrary external reference. Local channels intertwine with these
site-consistent codes, even when their input and output dimensions differ.

These are the onsite steps for comparing bounded local-channel protocols with the
fixed-physical-port resource convention of arXiv:2103.13367, Supplement pp. 7–8.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m n q r : ℕ}

omit [DecidableEq ι] in
private theorem linearMap_ext_rectKronecker {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (Φ Ψ : Matrix (ι → Fin m) (ι → Fin m) ℂ →ₗ[ℂ] M)
    (h : ∀ A : ι → Matrix (Fin m) (Fin m) ℂ, Φ (rectKronecker A) = Ψ (rectKronecker A)) :
    Φ = Ψ := by
  apply LinearMap.ext
  intro X
  exact LinearMap.eqOn_span' (by rintro _ ⟨A, _, rfl⟩; exact h A)
    (mem_supportedOperators_univ X)

namespace OnsiteChannel

/-- Assemble sitewise CPTP maps into the existing finite-Kraus onsite-channel API. -/
noncomputable def ofSiteMaps
    (Φ : ι → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
    (hΦ : ∀ i, IsKrausCPTP (Φ i)) : OnsiteChannel m n ι where
  r i := (hΦ i).choose
  kraus i := (hΦ i).choose_spec.choose
  sum_kraus i := (hΦ i).choose_spec.choose_spec.2

omit [Fintype ι] [DecidableEq ι] in
/-- The assembled channel has exactly the specified map at every site. -/
theorem ofSiteMaps_siteMap
    (Φ : ι → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
    (hΦ : ∀ i, IsKrausCPTP (Φ i)) (i : ι) : (ofSiteMaps Φ hΦ).siteMap i = Φ i := by
  apply LinearMap.ext
  intro X
  exact ((hΦ i).choose_spec.choose_spec.1 X).symm

/-- Onsite channel composition, allowing the intermediate local dimension to change. -/
noncomputable def comp (Φ : OnsiteChannel m n ι) (Ψ : OnsiteChannel n q ι) :
    OnsiteChannel m q ι :=
  ofSiteMaps (fun i => Ψ.siteMap i ∘ₗ Φ.siteMap i) (fun i =>
    isKrausCPTP_comp (rectangularKrausMap_isKrausCPTP _ (Φ.sum_kraus i))
      (rectangularKrausMap_isKrausCPTP _ (Ψ.sum_kraus i)))

/-- Sitewise composition agrees with the actual chain-channel composition. -/
theorem comp_map (Φ : OnsiteChannel m n ι) (Ψ : OnsiteChannel n q ι) :
    (Φ.comp Ψ).map = Ψ.map ∘ₗ Φ.map := by
  apply linearMap_ext_rectKronecker
  intro A
  simp only [LinearMap.comp_apply, map_rectKronecker, comp, ofSiteMaps_siteMap]

/-- A product of identity site maps is the identity on every chain operator. -/
theorem map_eq_id_of_siteMap_eq_id (Φ : OnsiteChannel m m ι)
    (hΦ : ∀ i, Φ.siteMap i = LinearMap.id) : Φ.map = LinearMap.id := by
  apply linearMap_ext_rectKronecker
  intro A
  rw [map_rectKronecker]
  simp only [hΦ, LinearMap.id_apply]

/-- Independent isometric basis encodings at all sites. -/
noncomputable def encodeRegisters (e : ι → (Fin m ↪ Fin q)) : OnsiteChannel m q ι where
  r _ := 1
  kraus i _ := registerEncoding (e i)
  sum_kraus i := by
    simpa only [Fin.sum_univ_one, Matrix.IsIsometry] using registerEncoding_isIsometry (e i)

omit [Fintype ι] [DecidableEq ι] in
/-- The site encoder is its single isometric Kraus map. -/
theorem encodeRegisters_siteMap (e : ι → (Fin m ↪ Fin q)) (i : ι) :
    (encodeRegisters e).siteMap i = singleKrausMap (registerEncoding (e i)) := by
  apply LinearMap.ext
  intro X
  change (∑ _ : Fin 1, registerEncoding (e i) * X * (registerEncoding (e i))ᴴ) = _
  simp only [Fin.sum_univ_one, singleKrausMap_apply]

/-- The global encoding is the tensor product of the local isometries. -/
theorem encodeRegisters_map (e : ι → (Fin m ↪ Fin q)) :
    (encodeRegisters e).map = singleKrausMap (rectKronecker fun i => registerEncoding (e i)) := by
  apply LinearMap.ext
  intro X
  change (∑ _ : ι → Fin 1, rectKronecker (fun i => registerEncoding (e i)) * X *
    (rectKronecker (fun i => registerEncoding (e i)))ᴴ) = _
  simp only [Finset.univ_unique, Finset.sum_singleton, singleKrausMap_apply]

/-- Decode independently at each site, completing only that site's unused code subspace. -/
noncomputable def decodeRegisters (e : ι → (Fin m ↪ Fin q))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) : OnsiteChannel q m ι :=
  ofSiteMaps (fun i => registerDecoding (e i) (ρ i))
    (fun i => registerDecoding_isKrausCPTP (e i) (hρ i) (htr i))

/-- The product decoder inverts the product encoder on every chain operator. -/
theorem decodeRegisters_encodeRegisters (e : ι → (Fin m ↪ Fin q))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (decodeRegisters e ρ hρ htr).map ∘ₗ (encodeRegisters e).map = LinearMap.id := by
  rw [← comp_map]
  apply map_eq_id_of_siteMap_eq_id
  intro i
  simp only [comp, ofSiteMaps_siteMap, decodeRegisters, encodeRegisters_siteMap,
    registerDecoding_comp_encoding]

/-- Product onsite coding preserves an arbitrary finite external reference exactly. -/
theorem decodeRegisters_encodeRegisters_reference {δ : Type*}
    (e : ι → (Fin m ↪ Fin q)) (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    tensorMapIdLM (δ := δ) (decodeRegisters e ρ hρ htr).map ∘ₗ
      tensorMapIdLM (δ := δ) (encodeRegisters e).map = LinearMap.id := by
  rw [← tensorMapIdLM_comp, decodeRegisters_encodeRegisters, tensorMapIdLM_id]

/-- Extend an existing onsite channel between fixed-size register codes at every site. -/
noncomputable def encoded (Φ : OnsiteChannel m n ι)
    (e : ι → (Fin m ↪ Fin q)) (f : ι → (Fin n ↪ Fin r))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) : OnsiteChannel q r ι :=
  ofSiteMaps (fun i => registerEncodedMap (e i) (f i) (ρ i) (Φ.siteMap i))
    (fun i => registerEncodedMap_isKrausCPTP (e i) (f i) (hρ i) (htr i)
      (rectangularKrausMap_isKrausCPTP _ (Φ.sum_kraus i)))

/-- The encoded onsite channel intertwines with the original channel globally, including
arbitrary entanglement between sites; it is not restricted to product input states. -/
theorem encoded_map_encodeRegisters (Φ : OnsiteChannel m n ι)
    (e : ι → (Fin m ↪ Fin q)) (f : ι → (Fin n ↪ Fin r))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (Φ.encoded e f ρ hρ htr).map ∘ₗ (encodeRegisters e).map =
      (encodeRegisters f).map ∘ₗ Φ.map := by
  apply linearMap_ext_rectKronecker
  intro A
  simp only [LinearMap.comp_apply, map_rectKronecker, encoded,
    ofSiteMaps_siteMap, encodeRegisters_siteMap, registerEncodedMap_encoding]

end OnsiteChannel

end QuantumCircuit
