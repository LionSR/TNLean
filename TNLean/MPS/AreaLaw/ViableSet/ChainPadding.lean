/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
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

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Placing an original prefix operator preserves its interval support. -/
theorem isSupportedOn_embedOp_prefix {L N q a b : ℕ} (hi : L ≤ N)
    {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hX : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) X (interval L a b)) :
    Entropy.IsSupportedOn (n := fun _ : Fin N ↦ q)
      (QuantumCircuit.embedOp (Fin.castLE hi) X) (interval N a b) := by
  have h := QuantumCircuit.embedOp_mem_supportedOperators_image
    (Fin.castLE_injective hi) (QuantumCircuit.mem_supportedOperators_of_isSupportedOn hX)
  apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
  apply QuantumCircuit.supportedOperators_mono ?_ h
  rintro _ ⟨v, hv, rfl⟩
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (j : Fin (N - 1)) : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ :=
  if hj : j.val < L - 1 then QuantumCircuit.embedOp (Fin.castLE hi) (h ⟨j.val, hj⟩)
  else QuantumCircuit.siteOp ⟨j.val + 1, by omega⟩ (QuantumCircuit.siteBasisPenalty z)

/-- Every padded term has its actual nearest-neighbour support. -/
theorem paddedInteraction_supported {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h j) (interval L j.val (j.val + 2))) (j : Fin (N - 1)) :
    Entropy.IsSupportedOn (n := fun _ : Fin N ↦ q)
      (paddedInteraction hi z h j) (interval N j.val (j.val + 2)) := by
  unfold paddedInteraction
  split_ifs with hj
  · exact isSupportedOn_embedOp_prefix hi (hs ⟨j.val, hj⟩)
  · apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    apply QuantumCircuit.supportedOperators_mono ?_
      (QuantumCircuit.siteOp_mem_supportedOperators
        (⟨j.val + 1, by omega⟩ : Fin N) (QuantumCircuit.siteBasisPenalty z))
    rintro v rfl
    apply mem_interval.mpr
    change j.val ≤ j.val + 1 ∧ j.val + 1 < j.val + 2
    omega

/-- The padded terms retain both original positive-contraction bounds. -/
theorem paddedInteraction_nonneg_le_one {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1) (j : Fin (N - 1)) :
    0 ≤ paddedInteraction hi z h j ∧ paddedInteraction hi z h j ≤ 1 := by
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ∑ j, paddedInteraction hi z h j = QuantumCircuit.embedOp (Fin.castLE hi) (∑ j, h j) +
      ∑ v : {v : Fin N // v ∉ leftBlock N L},
        QuantumCircuit.siteOp v.1 (QuantumCircuit.siteBasisPenalty z) := by
  classical
  let f : Fin (L - 1) ⊕ {v : Fin N // v ∉ leftBlock N L} →
      Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ :=
    Sum.elim (fun j ↦ QuantumCircuit.embedOp (Fin.castLE hi) (h j))
      (fun v ↦ QuantumCircuit.siteOp v.1 (QuantumCircuit.siteBasisPenalty z))
  have heval (j : Fin (N - 1)) :
      f (paddingBondEquiv hL hi j) = paddedInteraction hi z h j := by
    simp only [f, paddingBondEquiv, Equiv.coe_fn_mk, paddedInteraction]
    split_ifs <;> rfl
  have hsum := Equiv.sum_comp (paddingBondEquiv hL hi) f
  simp_rw [heval] at hsum
  rw [hsum]
  simp only [Fintype.sum_sum_type, f, Sum.elim_inl, Sum.elim_inr]
  have hlinear : (∑ j, QuantumCircuit.embedOp (Fin.castLE hi) (h j)) =
      QuantumCircuit.embedOp (Fin.castLE hi) (∑ j, h j) :=
    (map_sum (QuantumCircuit.embedOpLinearMap (Fin.castLE hi)) h Finset.univ).symm
  rw [hlinear]

end TNLean.MPS.AreaLaw
