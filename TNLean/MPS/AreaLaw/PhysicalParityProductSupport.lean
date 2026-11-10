/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedComplementProduct
import TNLean.MPS.AreaLaw.PhysicalFrustrationFreeTruncation

/-!
# Support of the actual physical parity products

A parity product acts on any region containing its selected bond terms.
This is the support step in ALVV, arXiv:1602.08828v2, `thm:FF-tH`,
lines 1543–1568. No commutation or projection hypothesis is required.
-/

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)

/-- The actual parity product retains the common support of its selected terms.
ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1568. -/
theorem isSupportedOn_physicalParityProduct
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (p : ℕ) (D : Finset (Fin L))
    (hs : ∀ i, i.val % 2 = p → Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) D) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      ((T).symm (physicalParityProduct h p)) D := by
  apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
  apply QuantumCircuit.mem_supportedOperators_complementProd
  intro k hk
  change (T).symm (if hk' : k < L - 1 then
      if k % 2 = p then T (h ⟨k, hk'⟩) else 0 else 0) ∈
    QuantumCircuit.supportedOperators q (D : Set (Fin L))
  rw [dite_eq_left hk]
  split_ifs with hp
  · simpa only [StarAlgEquiv.symm_apply_apply] using
      QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs ⟨k, hk⟩ hp)
  · simpa only [map_zero] using
      (QuantumCircuit.supportedOperators q (D : Set (Fin L))).zero_mem

/-- The actual parity product of the interval-restricted family is supported
on that same site interval. The support is derived from the original
nearest-neighbour terms. ALVV, arXiv:1602.08828v2, `def:FF-tH`,
lines 1467--1487. -/
theorem isSupportedOn_regionalParityProduct
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b p : ℕ) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      ((T).symm (physicalParityProduct (intervalBondRestriction a b h) p)) (interval L a b) := by
  classical
  apply isSupportedOn_physicalParityProduct
  intro i _
  unfold intervalBondRestriction
  split_ifs with hi
  · apply (hs i).mono
    intro v hv
    simp only [mem_interval] at *
    omega
  · exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators (Submodule.zero_mem _)

end TNLean.MPS.AreaLaw
