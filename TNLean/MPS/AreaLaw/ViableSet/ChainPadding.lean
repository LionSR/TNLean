/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.Models
import TNLean.Circuit.ProductBasisPenalty
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates
import TNLean.MPS.AreaLaw.Hamiltonian
import QICLean.Analysis.DoubledSystemGap

/-!
# Product-ancilla padding of a positive nearest-neighbour chain

The original terms are placed on the initial sites. Every new bond carries
one actual on-site penalty on its right site, vanishing at the specified
basis level. The interaction is chosen from the original terms and lengths,
without selecting a ground vector or energy.

Source: product-ancilla accuracy reduction for the successive construction of
LVV13, arXiv:1307.5143v1, final induction, lines 652--678. This is an algebraic
physical reduction; it asserts no computational running time.
-/

open ManyBody (interval mem_interval)

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Placing an original prefix operator preserves its interval support. -/
theorem isSupportedOn_embedOp_prefix {L N q a b : ℕ} (hi : L ≤ N)
    {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hX : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) X (interval L a b)) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (QuantumCircuit.embedOp (Fin.castLE hi) X) (interval N a b) := by
  have h := QuantumCircuit.embedOp_mem_supportedOperators_image
    (Fin.castLE_injective hi) hX
  change _ ∈ ManyBody.supportedOperators _ _
  apply ManyBody.supportedOperators_mono ?_ h
  intro _ hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  exact mem_interval.mpr ((mem_interval (L := L)).mp hv)

/-- Padded bonds are exactly the old bonds together with the new sites on
which their right-end penalties act. The positive original length is essential. -/
def paddingBondEquiv {L N : ℕ} (hL : 1 ≤ L) (hi : L ≤ N) :
    Fin (N - 1) ≃ Fin (L - 1) ⊕ {v : Fin N // v ∉ leftBlock N L} where
  toFun j := if hj : j.val < L - 1 then Sum.inl ⟨j.val, hj⟩ else
    Sum.inr ⟨⟨j.val + 1, by omega⟩, by
      intro hv
      have hv' : j.val + 1 < L := mem_leftBlock.mp hv
      omega⟩
  invFun p := match p with
    | Sum.inl j => ⟨j.val, by omega⟩
    | Sum.inr v => ⟨v.1.val - 1, by
        have hv : ¬v.1.val < L := fun h ↦ v.2 (mem_leftBlock.mpr h)
        omega⟩
  left_inv j := by
    dsimp only
    split_ifs with hj
    · rfl
    · apply Fin.ext
      simp
  right_inv p := by
    cases p with
    | inl j =>
      have hj := j.isLt
      simp only [hj, dite_true]
    | inr v =>
      have hv : ¬v.1.val < L := fun h ↦ v.2 (mem_leftBlock.mpr h)
      have hj : ¬v.1.val - 1 < L - 1 := by omega
      simp only [hj, dite_false]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Fin.ext
      change v.1.val - 1 + 1 = v.1.val
      omega

/-- The old bond terms act on the initial sites; each later bond carries the
penalty on its new right-hand site. All choices precede ground data. -/
noncomputable def paddedInteraction {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Φ : ManyBody.BondInteraction L q)
    (j : Fin (N - 1)) : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ :=
  if hj : j.val < L - 1 then QuantumCircuit.embedOp (Fin.castLE hi) (Φ.term ⟨j.val, hj⟩)
  else QuantumCircuit.siteOp ⟨j.val + 1, by omega⟩ (QuantumCircuit.siteBasisPenalty z)

/-- Every padded term has its actual nearest-neighbour support. -/
theorem paddedInteraction_supported {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Φ : ManyBody.BondInteraction L q) (j : Fin (N - 1)) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (paddedInteraction hi z Φ j) (interval N j.val (j.val + 2)) := by
  unfold paddedInteraction
  split_ifs with hj
  · exact isSupportedOn_embedOp_prefix hi (Φ.mem ⟨j.val, hj⟩)
  · change _ ∈ ManyBody.supportedOperators _ _
    apply ManyBody.supportedOperators_mono ?_
      (QuantumCircuit.siteOp_mem_supportedOperators
        (⟨j.val + 1, by omega⟩ : Fin N) (QuantumCircuit.siteBasisPenalty z))
    intro v hv
    rw [Finset.mem_singleton.mp hv]
    apply mem_interval.mpr
    change j.val ≤ j.val + 1 ∧ j.val + 1 < j.val + 2
    omega

/-- The padded terms retain both original positive-contraction bounds. -/
theorem paddedInteraction_nonneg_le_one {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1) (j : Fin (N - 1)) :
    0 ≤ paddedInteraction hi z Φ j ∧ paddedInteraction hi z Φ j ≤ 1 := by
  unfold paddedInteraction
  split_ifs with hj
  · constructor
    · exact (QuantumCircuit.embedOp_posSemidef (Fin.castLE_injective hi)
        (Matrix.nonneg_iff_posSemidef.mp (h0 ⟨j.val, hj⟩))).nonneg
    · simpa only [QuantumCircuit.embedOp_one] using
        QuantumCircuit.embedOp_le (Fin.castLE_injective hi) (h1 ⟨j.val, hj⟩)
  · constructor
    · exact (QuantumCircuit.siteOp_posSemidef _
        (QuantumCircuit.siteBasisPenalty_posSemidef z)).nonneg
    · simpa only [QuantumCircuit.siteOp_one] using
        QuantumCircuit.siteOp_le _ (QuantumCircuit.siteBasisPenalty_le_one z)

/-- The padded Hamiltonian is the embedded original sum plus the actual
sum of one on-site penalty for every appended site. -/
theorem sum_paddedInteraction {L N q : ℕ} (hL : 1 ≤ L) (hi : L ≤ N) (z : Fin q)
    (Φ : ManyBody.BondInteraction L q) :
    ∑ j, paddedInteraction hi z Φ j = QuantumCircuit.embedOp (Fin.castLE hi) Φ.hamiltonian +
      ∑ v : {v : Fin N // v ∉ leftBlock N L},
        QuantumCircuit.siteOp v.1 (QuantumCircuit.siteBasisPenalty z) := by
  classical
  let f : Fin (L - 1) ⊕ {v : Fin N // v ∉ leftBlock N L} →
      Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ :=
    Sum.elim (fun j ↦ QuantumCircuit.embedOp (Fin.castLE hi) (Φ.term j))
      (fun v ↦ QuantumCircuit.siteOp v.1 (QuantumCircuit.siteBasisPenalty z))
  have heval (j : Fin (N - 1)) :
      f (paddingBondEquiv hL hi j) = paddedInteraction hi z Φ j := by
    simp only [f, paddingBondEquiv, Equiv.coe_fn_mk, paddedInteraction]
    split_ifs <;> rfl
  have hsum := Equiv.sum_comp (paddingBondEquiv hL hi) f
  simp_rw [heval] at hsum
  rw [hsum]
  simp only [Fintype.sum_sum_type, f, Sum.elim_inl, Sum.elim_inr]
  have hlinear : (∑ j, QuantumCircuit.embedOp (Fin.castLE hi) (Φ.term j)) =
      QuantumCircuit.embedOp (Fin.castLE hi) Φ.hamiltonian :=
    (map_sum (QuantumCircuit.embedOpLinearMap (Fin.castLE hi)) Φ.term Finset.univ).symm
  rw [hlinear]

end TNLean.MPS.AreaLaw
