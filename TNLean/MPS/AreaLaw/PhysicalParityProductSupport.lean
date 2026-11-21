/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.SupportedComplementProduct
import TNLean.MPS.AreaLaw.PhysicalFrustrationFreeTruncation

/-!
# Support of the actual physical parity products

A parity product acts on any region containing its selected bond terms.
This is the support step in ALVV, arXiv:1602.08828v2, `thm:FF-tH`,
lines 1543–1568. No commutation or projection hypothesis is required.
-/

open ManyBody (interval mem_interval)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)

/-- The actual parity product retains the common support of its selected terms.
ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1568. -/
theorem isSupportedOn_physicalParityProduct
    (Φ : ManyBody.BondInteraction L q)
    (p : ℕ) (D : Finset (Fin L))
    (hs : ∀ i, i.val % 2 = p → ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (Φ.term i) D) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      ((T).symm (physicalParityProduct Φ p)) D := by
  change _ ∈ ManyBody.supportedOperators _ _
  apply QuantumCircuit.mem_supportedOperators_complementProd
  intro k hk
  change (T).symm (if hk' : k < L - 1 then
      if k % 2 = p then T (Φ.term ⟨k, hk'⟩) else 0 else 0) ∈
    ManyBody.supportedOperators (fun _ ↦ Fin q) D
  rw [dite_eq_left hk]
  split_ifs with hp
  · rw [StarAlgEquiv.symm_apply_apply]
    exact hs ⟨k, hk⟩ hp
  · simpa only [map_zero] using
      (zero_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) D))

/-- The actual parity product of the interval-restricted family is supported
on that same site interval. The support is derived from the original
nearest-neighbour terms. ALVV, arXiv:1602.08828v2, `def:FF-tH`,
lines 1467--1487. -/
theorem isSupportedOn_regionalParityProduct
    (Φ : ManyBody.BondInteraction L q) (a b p : ℕ) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      ((T).symm (physicalParityProduct (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p))
      (interval L a b) := by
  change _ ∈ ManyBody.supportedOperators _ _
  apply isSupportedOn_physicalParityProduct
  intro i _
  rw [ManyBody.Interaction.restrict_term]
  split_ifs with hi
  · apply ManyBody.IsSupportedOn.mono (Φ.mem i)
    intro v hv
    simp only [mem_interval] at *
    omega
  · change _ ∈ ManyBody.supportedOperators _ _
    exact zero_mem (ManyBody.supportedOperators (fun _ : Fin L ↦ Fin q) _)

end TNLean.MPS.AreaLaw
