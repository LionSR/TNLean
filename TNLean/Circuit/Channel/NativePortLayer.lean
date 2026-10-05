/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.NativeRegisterWires
import TNLean.Circuit.Channel.EncodedChannelLayer
import TNLean.Circuit.Channel.OnsiteChannelProduct

/-!
# Physical-port realizations of native register gates and layers

A native alphabet of size `d ^ k` is the basis of `k` physical data qudits at one site.
A channel supported on one native site is therefore free onsite. Every native matching
layer is implemented by one common `k`-layer data-to-scratch routing, local channel
execution, and the inverse routing. The resulting bound is `2 * k`, independently of
the number of gates. All ports and scratch registers remain identity reference systems.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit.PortRegisters

noncomputable section

variable {N k d s r : ℕ}

/-- Regrouping native basis labels into local qudit digits preserves Kraus completeness. -/
theorem nativeMatrixEquiv_complete
    (A : Fin r → Matrix (Fin s → Fin (d ^ k)) (Fin s → Fin (d ^ k)) ℂ)
    (hA : ∑ a, (A a)ᴴ * A a = 1) :
    ∑ a, (nativeMatrixEquiv s k d (A a))ᴴ * nativeMatrixEquiv s k d (A a) = 1 := by
  calc
    ∑ a, (nativeMatrixEquiv s k d (A a))ᴴ * nativeMatrixEquiv s k d (A a) =
        nativeMatrixEquiv s k d (∑ a, (A a)ᴴ * A a) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [map_mul, nativeMatrixEquiv_conjTranspose]
    _ = 1 := by rw [hA, map_one]

/-- Placing a native register Kraus map becomes placement on exactly its physical digits. -/
theorem dataChannelLift_register_kraus (e : Fin s ↪ Fin N)
    (A : Fin r → Matrix (Fin s → Fin (d ^ k)) (Fin s → Fin (d ^ k)) ℂ) :
    dataChannelLift N k d (registerChannelLift e (rectangularKrausMap A)) =
      rectangularKrausMap (fun a => embedOp (selectedData e) (nativeMatrixEquiv s k d (A a))) := by
  rw [registerChannelLift_kraus, dataChannelLift_kraus]
  congr 1
  funext a
  exact dataOperator_embedOp e (A a)

variable [NeZero N]

/-- A channel confined to one native spatial site has zero physical-port depth. -/
theorem dataChannelLift_local (e : Fin s ↪ Fin N)
    (Φ : Module.End ℂ (Matrix (Fin s → Fin (d ^ k)) (Fin s → Fin (d ^ k)) ℂ))
    (hΦ : IsKrausCPTP Φ) (i : Fin N) (he : ∀ a, e a = i) :
    IsPhysicalPortProtocol (layout N k) 0
      (dataChannelLift N k d (registerChannelLift e Φ)) := by
  obtain ⟨r, A, hform, hnorm⟩ := hΦ
  have hA : Φ = rectangularKrausMap A := by
    apply LinearMap.ext
    intro X
    exact hform X
  rw [hA, dataChannelLift_register_kraus]
  apply IsPhysicalPortProtocol.onsite (P := layout N k) i
  · intro a
    apply supportedOperators_mono _
      (embedOp_mem_supportedOperators (selectedData e).injective _)
    rintro x ⟨p, rfl⟩
    change (layout N k).site (selectedData e p) = i
    obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective p
    simpa only [selectedData_apply, site_data] using he j
  · exact sum_conjTranspose_embedOp_mul (selectedData e) _ (nativeMatrixEquiv_complete A hnorm)

/-- A full product onsite channel on native registers has zero physical-port depth. -/
theorem dataChannelLift_onsiteChannel (Φ : OnsiteChannel (d ^ k) (d ^ k) (Fin N)) :
    IsPhysicalPortProtocol (layout N k) 0 (dataChannelLift N k d Φ.map) := by
  rw [Φ.map_eq_prod_onSites_singleton, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  apply List.prod_induction (fun F => IsPhysicalPortProtocol (layout N k) 0 F)
  · intro A B hA hB
    simpa only [Nat.zero_add, Module.End.mul_eq_comp] using hB.comp hA
  · exact IsPhysicalPortProtocol.one _
  · intro F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
    rw [Φ.onSites_singleton_map_eq_lift]
    exact dataChannelLift_local (singletonSite i) (Φ.oneSite i).map
      (Φ.oneSite i).map_isKrausCPTP i (fun _ => rfl)

private theorem routed_selected_pair_site (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1) (p : Fin (2 * k)) :
    (layout N k).site (routingPermutation K hK
      (selectedData (⟨pairSites i (i + 1), pairSites_injective hne⟩ : Fin 2 ↪ Fin N) p)) =
      i + 1 := by
  have hselected : ∃ a : Fin (k + k),
      selectedData (⟨pairSites i (i + 1), pairSites_injective hne⟩ : Fin 2 ↪ Fin N) p =
        pairData i (i + 1) hne a := by
    obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective p
    fin_cases j
    · refine ⟨Fin.castAdd k t, ?_⟩
      rw [selectedData_apply, pairData_left]
      rfl
    · refine ⟨Fin.natAdd k t, ?_⟩
      rw [selectedData_apply, pairData_right]
      rfl
  obtain ⟨a, ha⟩ := hselected
  rw [ha]
  exact routingPermutation_pairData_site K hK hi hne a

/-- A native matching layer on `d ^ k` levels per site has a physical-port realization
of depth at most `2 * k`, restoring all wires outside the data registers exactly. -/
theorem dataChannelLift_channelLayer (hd : 0 < d) (hN : 2 ≤ N)
    (L : ChannelLayer (d ^ k) N) :
    IsPhysicalPortProtocol (layout N k) (2 * k) (dataChannelLift N k d L.map) := by
  classical
  rw [ChannelLayer.map, Finset.map_noncommProd]
  apply IsPhysicalPortProtocol.of_routed_family (layout N k) L.bonds
    (fun i => dataChannelLift N k d (L.gateMap i)) _
    (routingPermutation L.bonds L.pairwiseDisjoint)
    (routingPermutation_isPhysicalPortUnitary L.bonds L.pairwiseDisjoint)
  intro i hi
  have hne : i ≠ i + 1 := by
    intro h
    have h01 : (0 : Fin N) = 1 :=
      add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using h)
    have hN1 : N = 1 := Fin.one_eq_zero_iff.mp h01.symm
    omega
  let e : Fin 2 ↪ Fin N := ⟨pairSites i (i + 1), pairSites_injective hne⟩
  obtain ⟨A, hA, hnorm⟩ := L.exists_pairKraus hN (Nat.pow_pos hd) hi
  have hgate : L.gateMap i = registerChannelLift e (rectangularKrausMap A) := by
    rw [registerChannelLift_kraus]
    exact congrArg rectangularKrausMap (funext hA)
  rw [hgate, dataChannelLift_register_kraus, routingChannelConj_embeddedKraus]
  let σ := routingPermutation (k := k) L.bonds L.pairwiseDisjoint
  let f := (selectedData (k := k) e).trans σ.toEmbedding
  change IsPhysicalPortProtocol (layout N k) 0
    (rectangularKrausMap fun a => embedOp f (nativeMatrixEquiv 2 k d (A a)))
  apply IsPhysicalPortProtocol.onsite (P := layout N k) (i + 1)
  · intro a
    apply supportedOperators_mono _ (embedOp_mem_supportedOperators f.injective _)
    rintro x ⟨p, rfl⟩
    exact routed_selected_pair_site L.bonds L.pairwiseDisjoint hi hne p
  · exact sum_conjTranspose_embedOp_mul f _ (nativeMatrixEquiv_complete A hnorm)

end

end QuantumCircuit.PortRegisters
