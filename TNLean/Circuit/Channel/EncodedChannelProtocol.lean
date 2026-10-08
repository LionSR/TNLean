/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.DimensionBoundedConversion
import TNLean.Circuit.Channel.EncodedChannelLayer

/-!
# Compiling dimension-bounded native protocols into one register alphabet

A fixed-register word explicitly records onsite channels and pair-channel layers,
all on the same alphabet. Its depth counts only pair layers. Every positive-dimension
native protocol with a common bound compiles to such a word, intertwining exactly with
independent sitewise codes on arbitrary input operators. The theorem preserves the
original number of pair layers; converting register layers to physical-port layers is
a separate constructive step.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

variable {N q B d e : ℕ} [NeZero N]

/-- An onsite channel or a pair-channel layer, with one fixed local alphabet. -/
abbrev FixedRegisterOperation (q N : ℕ) [NeZero N] :=
  Sum (OnsiteChannel q q (Fin N)) (ChannelLayer q N)

namespace FixedRegisterOperation

/-- The actual channel of one fixed-register operation. -/
noncomputable def map (op : FixedRegisterOperation q N) :
    Module.End ℂ (Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ) :=
  op.elim OnsiteChannel.map BondChannelLayer.map

/-- Only a pair-channel layer contributes to intersite depth. -/
def depth (op : FixedRegisterOperation q N) : ℕ := op.elim (fun _ => 0) (fun _ => 1)

/-- Execute a word from right to left, in the order of composition of its maps. -/
noncomputable def wordMap (ops : List (FixedRegisterOperation q N)) :
    Module.End ℂ (Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ) :=
  (ops.map map).prod

/-- Count the pair-channel layers in a word. -/
def wordDepth (ops : List (FixedRegisterOperation q N)) : ℕ :=
  (ops.map depth).sum

/-- A fixed-register word supplies an ordinary native local-channel protocol. -/
theorem wordMap_isLocalChannelProtocol (ops : List (FixedRegisterOperation q N)) :
    IsLocalChannelProtocol (wordDepth ops) (wordMap ops) := by
  induction ops with
  | nil =>
    simpa only [FixedRegisterOperation.wordDepth, FixedRegisterOperation.wordMap,
      List.map_nil, List.sum_nil, List.prod_nil, OnsiteChannel.id_map, Module.End.one_eq_id] using
      IsLocalChannelProtocol.onsite (OnsiteChannel.id q (Fin N))
  | cons op ops ih =>
    cases op with
    | inl Φ => simpa only [wordDepth, wordMap, List.map_cons, List.sum_cons, List.prod_cons,
        depth, map, Sum.elim_inl, Nat.zero_add, Module.End.mul_eq_comp] using ih.onsite_comp Φ
    | inr L => simpa only [wordDepth, wordMap, List.map_cons, List.sum_cons, List.prod_cons,
        depth, map, Sum.elim_inr, Nat.add_comm, Module.End.mul_eq_comp] using ih.layer L

end FixedRegisterOperation

/-- A definite local density used only to complete the decoder away from its code. -/
noncomputable def registerFallbackDensity {m : ℕ} (hm : 0 < m) : Matrix (Fin m) (Fin m) ℂ :=
  vecMulVec (Pi.single ⟨0, hm⟩ 1) (star (Pi.single ⟨0, hm⟩ 1))

/-- The off-code fallback density is positive. -/
theorem registerFallbackDensity_posSemidef {m : ℕ} (hm : 0 < m) :
    (registerFallbackDensity hm).PosSemidef :=
  posSemidef_vecMulVec_self_star _

/-- The off-code fallback density has unit trace. -/
theorem trace_registerFallbackDensity {m : ℕ} (hm : 0 < m) :
    trace (registerFallbackDensity hm) = 1 := by
  simp [registerFallbackDensity, Matrix.trace, Matrix.diag, Matrix.vecMulVec, Pi.single_apply]

/-- A bounded local alphabet embeds into any common register alphabet at least as large. -/
def boundedAlphabetCode (hB : B ≤ q) {m : ℕ} (hm : m ≤ B) : Fin m ↪ Fin q :=
  Fin.castLEEmb (hm.trans hB)

/-- Every bounded native protocol compiles into an actual fixed-register word, with the
same number of pair layers and exact global intertwining on its input code. -/
theorem IsDimensionBoundedLocalChannelProtocol.exists_fixedRegisterWord {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hN : 2 ≤ N) (hB : B ≤ q) :
    ∃ ops : List (FixedRegisterOperation q N),
      FixedRegisterOperation.wordDepth ops = T ∧
      FixedRegisterOperation.wordMap ops ∘ₗ
          (OnsiteChannel.encodeRegisters fun _ =>
            boundedAlphabetCode hB h.dimension_bounds.1.2).map =
        (OnsiteChannel.encodeRegisters fun _ => boundedAlphabetCode hB h.dimension_bounds.2.2).map
          ∘ₗ Ψ := by
  induction h with
  | onsite Φ hd he =>
    let c := fun _ : Fin N => boundedAlphabetCode hB hd.2
    let f := fun _ : Fin N => boundedAlphabetCode hB he.2
    let ρ := fun _ : Fin N => registerFallbackDensity hd.1
    let Φ' := Φ.encoded c f ρ (fun _ => registerFallbackDensity_posSemidef hd.1)
      (fun _ => trace_registerFallbackDensity hd.1)
    refine ⟨[Sum.inl Φ'], rfl, ?_⟩
    simpa only [FixedRegisterOperation.wordMap, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, FixedRegisterOperation.map, Sum.elim_inl] using
      Φ.encoded_map_encodeRegisters c f ρ (fun _ => registerFallbackDensity_posSemidef hd.1)
        (fun _ => trace_registerFallbackDensity hd.1)
  | layer hΨ L ih =>
    obtain ⟨ops, hdepth, hinter⟩ := ih
    let c := fun _ : Fin N => boundedAlphabetCode hB hΨ.dimension_bounds.2.2
    obtain ⟨L', _, hL⟩ := L.exists_encodedRegisters hN hΨ.dimension_bounds.2.1 c
      (fun _ => registerFallbackDensity hΨ.dimension_bounds.2.1)
      (fun _ => registerFallbackDensity_posSemidef hΨ.dimension_bounds.2.1)
      (fun _ => trace_registerFallbackDensity hΨ.dimension_bounds.2.1)
    refine ⟨Sum.inr L' :: ops, ?_, ?_⟩
    · change 1 + FixedRegisterOperation.wordDepth ops = _
      omega
    · change (L'.map ∘ₗ FixedRegisterOperation.wordMap ops) ∘ₗ _ = _
      rw [LinearMap.comp_assoc, hinter, ← LinearMap.comp_assoc, hL, LinearMap.comp_assoc]
  | onsite_comp hΨ Φ hf ih =>
    obtain ⟨ops, hdepth, hinter⟩ := ih
    let c := fun _ : Fin N => boundedAlphabetCode hB hΨ.dimension_bounds.2.2
    let f := fun _ : Fin N => boundedAlphabetCode hB hf.2
    let ρ := fun _ : Fin N => registerFallbackDensity hΨ.dimension_bounds.2.1
    let Φ' := Φ.encoded c f ρ
      (fun _ => registerFallbackDensity_posSemidef hΨ.dimension_bounds.2.1)
      (fun _ => trace_registerFallbackDensity hΨ.dimension_bounds.2.1)
    have hΦ := Φ.encoded_map_encodeRegisters c f ρ
      (fun _ => registerFallbackDensity_posSemidef hΨ.dimension_bounds.2.1)
      (fun _ => trace_registerFallbackDensity hΨ.dimension_bounds.2.1)
    refine ⟨Sum.inl Φ' :: ops, ?_, ?_⟩
    · simpa only [FixedRegisterOperation.wordDepth, List.map_cons, List.sum_cons,
        FixedRegisterOperation.depth, Sum.elim_inl, Nat.zero_add] using hdepth
    · change (Φ'.map ∘ₗ FixedRegisterOperation.wordMap ops) ∘ₗ _ = _
      rw [LinearMap.comp_assoc, hinter, ← LinearMap.comp_assoc, hΦ, LinearMap.comp_assoc]

end QuantumCircuit
