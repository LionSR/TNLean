/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.NativePortLayer

/-!
# Free channels on complete spatial-site wire blocks

Grouping all the physical port, data and scratch digits at one site is only a choice
of coordinates. An independently specified channel on each complete site block has
an actual zero-depth physical-port realization. The proof places its Kraus operators
inside that spatial site, rather than assigning a free cost to a global reindexing.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit.PortRegisters

noncomputable section

variable {N s w d k r : ℕ}

/-- Flatten the selected spatial sites together with all their local digits. -/
def blockDigits (e : Fin s ↪ Fin N) : Fin (s * w) ↪ Fin (N * w) :=
  finProdFinEquiv.symm.toEmbedding.trans
    ((e.prodMap (Function.Embedding.refl (Fin w))).trans finProdFinEquiv.toEmbedding)

@[simp] theorem blockDigits_apply (e : Fin s ↪ Fin N) (i : Fin s) (t : Fin w) :
    blockDigits e (finProdFinEquiv (i, t)) = finProdFinEquiv (e i, t) := by
  change finProdFinEquiv (e (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (i, t))).2) = _
  rw [Equiv.symm_apply_apply]

private theorem allData_comp_blockDigits (e : Fin s ↪ Fin N) :
    (allData N w : Fin (N * w) → _) ∘ blockDigits e = selectedData e := by
  funext p
  obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [Function.comp_apply, blockDigits_apply, allData_apply, selectedData_apply]

/-- Sitewise digit grouping preserves the placement of every selected native operator. -/
theorem nativeMatrixEquiv_embedOp (hd : 0 < d) (e : Fin s ↪ Fin N)
    (A : Matrix (Fin s → Fin (d ^ w)) (Fin s → Fin (d ^ w)) ℂ) :
    nativeMatrixEquiv N w d (embedOp e A) =
      embedOp (blockDigits e) (nativeMatrixEquiv s w d A) := by
  apply embedOp_injective (allData N w).injective hd
  change dataOperator (embedOp e A) =
    embedOp (allData N w) (embedOp (blockDigits e) (nativeMatrixEquiv s w d A))
  rw [embedOp_embedOp (allData N w).injective, allData_comp_blockDigits]
  exact dataOperator_embedOp e A

/-- A reindexed native register channel is the actual Kraus channel on the corresponding
physical site blocks. -/
theorem nativeChannelReindex_register_kraus (hd : 0 < d) (e : Fin s ↪ Fin N)
    (A : Fin r → Matrix (Fin s → Fin (d ^ w)) (Fin s → Fin (d ^ w)) ℂ) :
    nativeChannelReindex N w d (registerChannelLift e (rectangularKrausMap A)) =
      rectangularKrausMap (fun a => embedOp (blockDigits e) (nativeMatrixEquiv s w d (A a))) := by
  rw [registerChannelLift_kraus, nativeChannelReindex_kraus]
  congr 1
  funext a
  exact nativeMatrixEquiv_embedOp hd e (A a)

variable [NeZero N]

/-- A channel on one complete physical site block costs no intersite layer. -/
theorem wholeSite_local (hd : 0 < d) (e : Fin s ↪ Fin N)
    (Φ : Module.End ℂ (Matrix (Fin s → Fin (d ^ (1 + k + k)))
      (Fin s → Fin (d ^ (1 + k + k))) ℂ))
    (hΦ : IsKrausCPTP Φ) (i : Fin N) (he : ∀ a, e a = i) :
    IsPhysicalPortProtocol (layout N k) 0
      (nativeChannelReindex N (1 + k + k) d (registerChannelLift e Φ)) := by
  obtain ⟨r, A, hform, hnorm⟩ := hΦ
  have hA : Φ = rectangularKrausMap A := by
    apply LinearMap.ext
    exact hform
  rw [hA, nativeChannelReindex_register_kraus hd]
  apply IsPhysicalPortProtocol.onsite (P := layout N k) i
  · intro a
    apply supportedOperators_mono _
      (embedOp_mem_supportedOperators (blockDigits e).injective _)
    rintro x ⟨p, rfl⟩
    change (layout N k).site (blockDigits e p) = i
    obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective p
    rw [blockDigits_apply]
    change (finProdFinEquiv.symm (finProdFinEquiv (e j, t))).1 = i
    rw [Equiv.symm_apply_apply]
    exact he j
  · exact sum_conjTranspose_embedOp_mul (blockDigits e) _ (nativeMatrixEquiv_complete A hnorm)

/-- A product of independent channels on complete physical site blocks has depth zero. -/
theorem wholeSite_onsiteChannel (hd : 0 < d)
    (Φ : OnsiteChannel (d ^ (1 + k + k)) (d ^ (1 + k + k)) (Fin N)) :
    IsPhysicalPortProtocol (layout N k) 0
      (nativeChannelReindex N (1 + k + k) d Φ.map) := by
  rw [Φ.map_eq_prod_onSites_singleton, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  apply List.prod_induction (fun F => IsPhysicalPortProtocol (layout N k) 0 F)
  · intro A B hA hB
    simpa only [Nat.zero_add, Module.End.mul_eq_comp] using hB.comp hA
  · exact IsPhysicalPortProtocol.one _
  · intro F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
    rw [Φ.onSites_singleton_map_eq_lift]
    exact wholeSite_local hd (singletonSite i) (Φ.oneSite i).map
      (Φ.oneSite i).map_isKrausCPTP i (fun _ => rfl)

end

end QuantumCircuit.PortRegisters
