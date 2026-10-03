/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.JoiningPacketSupport
import TNLean.MPS.MPU.IntervalInitializationBounds
import TNLean.Circuit.LocalCircuit

/-!
# Support of an interval merger in joining-packet coordinates

The supports of two adjacent child intervals are contained in their parent
interval. The parent auxiliary initialization sites and the joining packet
also lie in this support. These inclusions are preserved when a site bijection
places the joining packet at the end of the logical register.

The coordinate equation for the joining packet is the actual equation obtained
by its placement. No operator-support identity is supplied for the selected
flags or the packet. Child operator support is the recursive induction data.

Source: the interval merger and common-register construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit

namespace MPUCircuit

variable {d D N j m k : ℕ}

/-- The left child's support is contained in the parent interval.
Source: the interval support decomposition in Section 5 of the circuit manuscript. -/
theorem intervalConsecutiveSupport_left_subset (hjm : j < m) (hmk : m < k) :
    intervalConsecutiveSupport d D N j m ⊆ intervalConsecutiveSupport d D N j k := by
  rintro x ⟨s, hs, rfl⟩
  refine ⟨s, ?_, rfl⟩
  rw [intervalLogicalSupport_split hjm hmk]
  exact Or.inl (Or.inl hs)

/-- The right child's support is contained in the parent interval.
Source: the interval support decomposition in Section 5 of the circuit manuscript. -/
theorem intervalConsecutiveSupport_right_subset (hjm : j < m) (hmk : m < k) :
    intervalConsecutiveSupport d D N m k ⊆ intervalConsecutiveSupport d D N j k := by
  rintro x ⟨s, hs, rfl⟩
  refine ⟨s, ?_, rfl⟩
  rw [intervalLogicalSupport_split hjm hmk]
  exact Or.inl (Or.inr hs)

/-- Actual child operators supported in their respective intervals are supported
in their parent interval. The child support assertions are induction data.
Source: the recursive interval merger in Section 5 of the circuit manuscript. -/
theorem interval_children_mem_parent_supportedOperators
    (hjm : j < m) (hmk : m < k)
    {X Y : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ}
    (hX : X ∈ supportedOperators d (intervalConsecutiveSupport d D N j m))
    (hY : Y ∈ supportedOperators d (intervalConsecutiveSupport d D N m k)) :
    X ∈ supportedOperators d (intervalConsecutiveSupport d D N j k) ∧
      Y ∈ supportedOperators d (intervalConsecutiveSupport d D N j k) :=
  ⟨supportedOperators_mono (intervalConsecutiveSupport_left_subset hjm hmk) hX,
    supportedOperators_mono (intervalConsecutiveSupport_right_subset hjm hmk) hY⟩

/-- The selected parent auxiliary initialization sites remain in the parent
support after any site-coordinate bijection. The selection is the actual
finite enumeration of the interval initialization set.
Source: the initialized-register reflections in Section 5 of the circuit manuscript. -/
theorem interval_initializedSites_range_subset_reindexed_parent {L : ℕ}
    (e : Fin L ≃ Fin (logicalSiteCount d D N)) :
    Set.range ((logicalSupportSites
      (intervalAuxiliaryInitializationSupport d D N j k)).trans e.symm.toEmbedding) ⊆
      e.symm '' intervalConsecutiveSupport d D N j k := by
  rintro x ⟨i, rfl⟩
  refine ⟨logicalSupportSites (intervalAuxiliaryInitializationSupport d D N j k) i, ?_, rfl⟩
  have hi : logicalSupportSites (intervalAuxiliaryInitializationSupport d D N j k) i ∈
      (logicalSiteEquivFin d D N) '' intervalAuxiliaryInitializationSupport d D N j k := by
    rw [← logicalSupportSites_range]
    exact ⟨i, rfl⟩
  rcases hi with ⟨s, hs, hsi⟩
  exact ⟨s, hs.1, hsi⟩

/-- A suffix identified with the actual joining packet lies in the reindexed
parent support. The placement equation is used to derive the inclusion,
without an additional support premise for the suffix.
Source: the joining-packet placement in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem interval_joiningSuffix_range_subset_reindexed_parent {a : ℕ}
    (c : Fin (N - 1)) (j k : Fin (N + 1))
    (hjm : j.val < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k.val)
    (hn : a + (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) =
      logicalSiteCount d D N)
    (τ : Equiv.Perm (Fin (logicalSiteCount d D N)))
    (hτ : ∀ i, τ (Fin.cast hn (Fin.natAdd a i)) = joiningPacketSites d D N c i) :
    Set.range (Fin.natAdd a :
      Fin (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) →
        Fin (a + (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2))) ⊆
      ((finCongr hn).trans τ).symm '' intervalConsecutiveSupport d D N j.val k.val := by
  rintro x ⟨i, rfl⟩
  refine ⟨joiningPacketSites d D N c i,
    joiningPacketSites_range_subset_interval c hjm hmk ⟨i, rfl⟩, ?_⟩
  apply ((finCongr hn).trans τ).injective
  rw [Equiv.apply_symm_apply]
  exact (hτ i).symm

end MPUCircuit
