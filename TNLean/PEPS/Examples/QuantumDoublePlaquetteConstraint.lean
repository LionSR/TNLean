/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleBondAverage

/-!
# The four-block plaquette term in the clockwise quantum double

SCP10, arXiv:1001.3807v3, source lines 2801–2813 and 2918–2923:
the remaining A plaquettes lie between four blocked tensors. With colors
`(p,q,r,s)` on north, east, south, west bonds, the clockwise K spins are
`(a,b,c,d) = (pq⁻¹,qr⁻¹,rs⁻¹,sp⁻¹)`. The central hole reads
`NW.b * SW.a * SE.d * NE.c`; that order telescopes on matched bonds.
This file defines the full sixteen-spin diagonal projector, proves its
invariance under the incident coherent top-bond action and shows that it
fixes the actual four-tensor contraction. It does not identify a periodic
ground space with a single trivial-holonomy contraction.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

/-- Four full blocked-spin tuples, ordered `((NW,NE),(SE,SW))`. -/
abbrev QuantumDoubleKPlaquetteConfig (G : Type*) :=
  ((G × G × G × G) × (G × G × G × G)) ×
    ((G × G × G × G) × (G × G × G × G))

instance {G : Type*} [DecidableEq G] : DecidableEq (QuantumDoubleKPlaquetteConfig G) :=
  fun x y => decidable_of_iff (x.1 = y.1 ∧ x.2 = y.2) Prod.ext_iff.symm

variable {G : Type*} [Group G]

/-- The source's oriented product around the hole between four tensors. -/
def quantumDoubleKPlaquetteHolonomy (x : QuantumDoubleKPlaquetteConfig G) : G :=
  x.1.1.2.1 * x.2.2.1 * x.2.1.2.2.2 * x.1.2.2.2.1

/-- Four K spin tuples with the four internal bond colors matched. The eight
boundary colors are `(northNW,westNW,northNE,eastNE;eastSE,southSE,southSW,westSW)`;
the internal colors are `(eastNW,southNW,eastSW,southNE)`. -/
def quantumDoubleKPlaquetteSpins
    (b : (G × G × G × G) × (G × G × G × G)) (k : G × G × G × G) :
    QuantumDoubleKPlaquetteConfig G :=
  ((quantumDoubleKSpins (b.1.1, k.1, k.2.1, b.1.2.1),
    quantumDoubleKSpins (b.1.2.2.1, b.1.2.2.2, k.2.2.2, k.1)),
    (quantumDoubleKSpins (k.2.2.2, b.2.1, b.2.2.1, k.2.2.1),
      quantumDoubleKSpins (k.2.1, k.2.2.1, b.2.2.2.1, b.2.2.2.2)))

/-- Flatness around the actual four-tensor hole follows by cancellation of
its matched virtual bond colors, with no commutativity assumption. -/
@[simp]
theorem quantumDoubleKPlaquetteHolonomy_spins
    (b : (G × G × G × G) × (G × G × G × G)) (k : G × G × G × G) :
    quantumDoubleKPlaquetteHolonomy (quantumDoubleKPlaquetteSpins b k) = 1 := by
  simp [quantumDoubleKPlaquetteHolonomy, quantumDoubleKPlaquetteSpins,
    quantumDoubleKSpins, mul_assoc]

/-- The coherent physical action of the top horizontal bond on the full
four-block spin space; the two bottom blocks are spectators. -/
def quantumDoubleKPlaquetteTopBond (u : G) : Equiv.Perm (QuantumDoubleKPlaquetteConfig G) :=
  Equiv.prodCongr (quantumDoubleKBondPermutation u) (Equiv.refl _)

/-- A top-bond color change conjugates, rather than fixes pointwise, the
ordered hole holonomy. In particular it preserves the product-one condition. -/
theorem quantumDoubleKPlaquetteHolonomy_topBond (u : G)
    (x : QuantumDoubleKPlaquetteConfig G) :
    quantumDoubleKPlaquetteHolonomy (quantumDoubleKPlaquetteTopBond u x) =
      u * quantumDoubleKPlaquetteHolonomy x * u⁻¹ := by
  simp [quantumDoubleKPlaquetteHolonomy, quantumDoubleKPlaquetteTopBond,
    quantumDoubleKBondPermutation, quantumDoubleKBondAction, quantumDoubleKBondLeft,
    quantumDoubleKBondRight, mul_assoc]

/-- The four-tensor plaquette constraint is invariant under the top bond action. -/
theorem quantumDoubleKPlaquetteHolonomy_topBond_eq_one_iff (u : G)
    (x : QuantumDoubleKPlaquetteConfig G) :
    quantumDoubleKPlaquetteHolonomy (quantumDoubleKPlaquetteTopBond u x) = 1 ↔
      quantumDoubleKPlaquetteHolonomy x = 1 := by
  rw [quantumDoubleKPlaquetteHolonomy_topBond]
  constructor
  · intro h
    have hh := congrArg (fun z => u⁻¹ * z * u) h
    simpa [mul_assoc] using hh
  · intro h
    simp [h]

variable [Fintype G] [DecidableEq G]

/-- The second source Hamiltonian constraint, on all sixteen physical spins. -/
def quantumDoubleKPlaquetteProjector :
    Matrix (QuantumDoubleKPlaquetteConfig G) (QuantumDoubleKPlaquetteConfig G) ℂ :=
  Matrix.diagonal fun x => if quantumDoubleKPlaquetteHolonomy x = 1 then 1 else 0

/-- The complementary physical four-block Hamiltonian term. -/
def quantumDoubleKPlaquetteTerm :
    Matrix (QuantumDoubleKPlaquetteConfig G) (QuantumDoubleKPlaquetteConfig G) ℂ :=
  1 - quantumDoubleKPlaquetteProjector

/-- The explicit oriented plaquette constraint is an orthogonal projector. -/
theorem quantumDoubleKPlaquetteProjector_isStarProjection :
    IsStarProjection (quantumDoubleKPlaquetteProjector (G := G)) := by
  apply (isStarProjection_iff').mpr
  constructor
  · rw [quantumDoubleKPlaquetteProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> simp
  · change (quantumDoubleKPlaquetteProjector (G := G))ᴴ = _
    ext x y
    simp only [quantumDoubleKPlaquetteProjector, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all

/-- The plaquette Hamiltonian term is an orthogonal projector. -/
theorem quantumDoubleKPlaquetteTerm_isStarProjection :
    IsStarProjection (quantumDoubleKPlaquetteTerm (G := G)) :=
  quantumDoubleKPlaquetteProjector_isStarProjection.one_sub

/-- The incident physical coherent action commutes with the full-ambient
four-block plaquette projector, including non-flat configurations. -/
theorem quantumDoubleKPlaquetteProjector_commute_topBond (u : G) :
    Commute (quantumDoubleKPlaquetteProjector (G := G))
      (Matrix.permMatrixHom (R := ℂ) (quantumDoubleKPlaquetteTopBond u)) := by
  change Commute _ ((quantumDoubleKPlaquetteTopBond u)⁻¹.permMatrix ℂ)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro x y
  have he : (quantumDoubleKPlaquetteTopBond u)⁻¹ = quantumDoubleKPlaquetteTopBond u⁻¹ := by
    apply Equiv.ext
    intro z
    rfl
  rw [he]
  simp only [quantumDoubleKPlaquetteProjector, Matrix.diagonal_apply,
    (quantumDoubleKPlaquetteTopBond u⁻¹).injective.eq_iff,
    quantumDoubleKPlaquetteHolonomy_topBond_eq_one_iff]

/-- Averaging the actual adjacent bond action also commutes with the hole
constraint; the average uses the same normalization as the two-block term. -/
theorem quantumDoubleKPlaquetteProjector_commute_topBondAverage :
    Commute (quantumDoubleKPlaquetteProjector (G := G))
      ((Fintype.card G : ℂ)⁻¹ • ∑ u : G,
        Matrix.permMatrixHom (R := ℂ) (quantumDoubleKPlaquetteTopBond u)) := by
  apply Commute.smul_right
  exact Commute.sum_right _ _ _ (fun u _ => quantumDoubleKPlaquetteProjector_commute_topBond u)

/-- Actual product of the four K tensors, summed over the four internal bonds. -/
def quantumDoubleKPlaquetteContraction : Matrix (QuantumDoubleKPlaquetteConfig G)
    ((G × G × G × G) × (G × G × G × G)) ℂ := fun x b =>
  ∑ k : G × G × G × G,
    quantumDoubleKTensor G b.1.1 k.1 k.2.1 b.1.2.1 x.1.1 *
      quantumDoubleKTensor G b.1.2.2.1 b.1.2.2.2 k.2.2.2 k.1 x.1.2 *
      quantumDoubleKTensor G k.2.2.2 b.2.1 b.2.2.1 k.2.2.1 x.2.1 *
      quantumDoubleKTensor G k.2.1 k.2.2.1 b.2.2.2.1 b.2.2.2.2 x.2.2

/-- Coordinate expansion of the real four-tensor contraction. -/
theorem quantumDoubleKPlaquetteContraction_eq
    (b : (G × G × G × G) × (G × G × G × G)) (x : QuantumDoubleKPlaquetteConfig G) :
    quantumDoubleKPlaquetteContraction x b =
      ∑ k : G × G × G × G, if x = quantumDoubleKPlaquetteSpins b k then 1 else 0 := by
  unfold quantumDoubleKPlaquetteContraction quantumDoubleKTensor quantumDoubleKPlaquetteSpins
  apply Finset.sum_congr rfl
  intro k _
  simp only [Prod.ext_iff]
  split_ifs <;> simp_all

/-- The source's physical plaquette projector fixes every open-boundary
column of the actual four-tensor K network. -/
theorem quantumDoubleKPlaquetteProjector_contraction :
    quantumDoubleKPlaquetteProjector (G := G) * quantumDoubleKPlaquetteContraction =
      quantumDoubleKPlaquetteContraction := by
  ext x b
  rw [quantumDoubleKPlaquetteProjector, Matrix.diagonal_mul]
  by_cases hx : quantumDoubleKPlaquetteHolonomy x = 1
  · simp [hx]
  · simp only [hx, ite_false, zero_mul]
    rw [quantumDoubleKPlaquetteContraction_eq]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne : x ≠ quantumDoubleKPlaquetteSpins b k := by
      rintro rfl
      exact hx (quantumDoubleKPlaquetteHolonomy_spins b k)
    simp [hne]

end TNLean.PEPS
