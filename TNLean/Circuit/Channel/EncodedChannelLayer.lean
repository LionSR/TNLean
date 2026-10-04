/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.EncodedChannelPlacement
import TNLean.Circuit.Channel.PortChannelRouting

/-!
# Encoding native channel layers with consistent onsite register codes

A native channel layer supplies Kraus operators supported on disjoint neighboring pairs.
Each supported operator is extracted as an actual two-site matrix, and injectivity of
placement recovers its local completeness relation. After independent local encoding
and completed decoding, these pair maps give another native channel layer on the same
matching. Its action intertwines with the global product code on all chain operators.

The source local dimension is positive, and the ring has at least two sites so that
its neighboring pairs have distinct endpoints. No global simulation equation is assumed.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

noncomputable section

variable {N m q : ℕ}

private theorem matching_intertwine (S : Finset (Fin N))
    (F : Fin N → Module.End ℂ (Matrix (Fin N → Fin m) (Fin N → Fin m) ℂ))
    (G : Fin N → Module.End ℂ (Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ))
    (E : Matrix (Fin N → Fin m) (Fin N → Fin m) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ)
    (hF : (S : Set (Fin N)).Pairwise (Function.onFun Commute F))
    (hG : (S : Set (Fin N)).Pairwise (Function.onFun Commute G))
    (h : ∀ i ∈ S, G i ∘ₗ E = E ∘ₗ F i) :
    S.noncommProd G hG ∘ₗ E = E ∘ₗ S.noncommProd F hF := by
  induction S using Finset.induction_on with
  | empty => rfl
  | insert i S hi ih =>
    have htail := ih
      (hF.mono (by simp only [Finset.coe_insert, Set.subset_insert]))
      (hG.mono (by simp only [Finset.coe_insert, Set.subset_insert]))
      (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
    simp only [Module.End.mul_eq_comp]
    rw [LinearMap.comp_assoc, htail, ← LinearMap.comp_assoc,
      h i (Finset.mem_insert_self i S), LinearMap.comp_assoc]

namespace ChannelLayer

variable [NeZero N]

private def pairEmbedding (hN : 2 ≤ N) (i : Fin N) : Fin 2 ↪ Fin N :=
  ⟨pairSites i (i + 1), pairSites_injective (by
    intro h
    have h01 : (0 : Fin N) = 1 :=
      add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using h)
    have hN1 : N = 1 := Fin.one_eq_zero_iff.mp h01.symm
    omega)⟩

private theorem range_pairEmbedding (hN : 2 ≤ N) (i : Fin N) :
    Set.range (pairEmbedding hN i) = bond i := range_pairSites i (i + 1)

/-- A native gate's supported global Kraus operators come from normalized two-site
Kraus operators. Positivity of the local dimension makes placement injective. -/
theorem exists_pairKraus (L : ChannelLayer m N) (hN : 2 ≤ N) (hm : 0 < m)
    {i : Fin N} (hi : i ∈ L.bonds) :
    ∃ A : Fin (L.r i) → Matrix (Fin 2 → Fin m) (Fin 2 → Fin m) ℂ,
      (∀ a, L.kraus i a = embedOp (pairSites i (i + 1)) (A a)) ∧
      ∑ a, (A a)ᴴ * A a = 1 := by
  classical
  let e := pairEmbedding hN i
  have hs (a : Fin (L.r i)) : L.kraus i a ∈ supportedOperators m (Set.range e) := by
    rw [range_pairEmbedding]
    exact L.kraus_mem_supportedOperators i hi a
  choose A hA using fun a => exists_embedOp_eq_of_mem_supportedOperators e.injective (hs a)
  refine ⟨A, hA, ?_⟩
  apply embedOp_injective e.injective hm
  let E : Matrix (Fin 2 → Fin m) (Fin 2 → Fin m) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin m) (Fin N → Fin m) ℂ :=
    { toFun := embedOp e
      map_add' := embedOp_add e
      map_smul' := fun z X => embedOp_smul e z X }
  change E (∑ a, (A a)ᴴ * A a) = E 1
  rw [map_sum]
  change (∑ a, embedOp e ((A a)ᴴ * A a)) = embedOp e 1
  simp_rw [← embedOp_mul e.injective, ← embedOp_conjTranspose, ← hA]
  rw [embedOp_one]
  exact L.sum_kraus i hi

/-- A native layer can be encoded into any site-consistent family of basis codes.
The output is an actual channel layer with the same bonds and an exact global
intertwining identity, valid for arbitrary correlated input operators. -/
theorem exists_encodedRegisters (L : ChannelLayer m N) (hN : 2 ≤ N) (hm : 0 < m)
    (c : Fin N → (Fin m ↪ Fin q))
    (ρ : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    ∃ L' : ChannelLayer q N, L'.bonds = L.bonds ∧
      L'.map ∘ₗ (OnsiteChannel.encodeRegisters c).map =
        (OnsiteChannel.encodeRegisters c).map ∘ₗ L.map := by
  classical
  choose A hA hsum using fun i (hi : i ∈ L.bonds) => L.exists_pairKraus hN hm hi
  let e := pairEmbedding hN
  let Φ (i : Fin N) : Module.End ℂ (Matrix (Fin 2 → Fin m) (Fin 2 → Fin m) ℂ) :=
    if hi : i ∈ L.bonds then rectangularKrausMap (A i hi) else LinearMap.id
  have hΦ (i : Fin N) : IsKrausCPTP (Φ i) := by
    dsimp only [Φ]
    split_ifs with hi
    · exact rectangularKrausMap_isKrausCPTP _ (hsum i hi)
    · exact isKrausCPTP_id
  have hgate (i : Fin N) (hi : i ∈ L.bonds) :
      registerChannelLift (e i) (Φ i) = L.gateMap i := by
    rw [show Φ i = rectangularKrausMap (A i hi) from dite_eq_left hi, registerChannelLift_kraus]
    exact congrArg rectangularKrausMap (funext fun a => (hA i hi a).symm)
  let E (i : Fin N) := OnsiteChannel.encodeRegisters fun a => c (e i a)
  let D (i : Fin N) := OnsiteChannel.decodeRegisters (fun a => c (e i a))
    (fun a => ρ (e i a)) (fun a => hρ (e i a)) (fun a => htr (e i a))
  have hDE (i : Fin N) : (D i).map ∘ₗ (E i).map = LinearMap.id :=
    OnsiteChannel.decodeRegisters_encodeRegisters _ _ _ _
  let Ψ (i : Fin N) : Module.End ℂ (Matrix (Fin 2 → Fin q) (Fin 2 → Fin q) ℂ) :=
    (E i).map ∘ₗ ((Φ i) ∘ₗ (D i).map)
  have hΨ (i : Fin N) : IsKrausCPTP (Ψ i) :=
    isKrausCPTP_comp (isKrausCPTP_comp (D i).map_isKrausCPTP (hΦ i)) (E i).map_isKrausCPTP
  have hinter (i : Fin N) : Ψ i ∘ₗ (E i).map = (E i).map ∘ₗ Φ i := by
    apply LinearMap.ext
    intro X
    change (E i).map (Φ i ((D i).map ((E i).map X))) = (E i).map (Φ i X)
    have hDX := LinearMap.congr_fun (hDE i) X
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hDX
    rw [hDX]
  choose r B hform hnorm using hΨ
  have hB (i : Fin N) : rectangularKrausMap (B i) = Ψ i := by
    apply LinearMap.ext
    intro X
    exact (hform i X).symm
  let L' : ChannelLayer q N :=
    { bonds := L.bonds
      r := r
      kraus i a := embedOp (e i) (B i a)
      kraus_mem_supportedOperators := by
        intro i _ a
        rw [← range_pairEmbedding hN i]
        exact embedOp_mem_supportedOperators (e i).injective _
      sum_kraus i _ := sum_conjTranspose_embedOp_mul (e i) (B i) (hnorm i)
      pairwiseDisjoint := L.pairwiseDisjoint }
  refine ⟨L', rfl, ?_⟩
  apply matching_intertwine L.bonds L.gateMap L'.gateMap
    (OnsiteChannel.encodeRegisters c).map L.gateMap_commute L'.gateMap_commute
  intro i hi
  have hgate' : L'.gateMap i = registerChannelLift (e i) (Ψ i) := by
    change rectangularKrausMap (fun a => embedOp (e i) (B i a)) = _
    rw [← registerChannelLift_kraus, hB]
  rw [hgate', ← hgate i hi]
  exact registerChannelLift_encodeRegisters (e i) c (Φ i) (Ψ i) (hinter i)

end ChannelLayer

end

end QuantumCircuit
