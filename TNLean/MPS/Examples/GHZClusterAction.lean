/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.Examples.GHZCluster

/-!
# The GHZ–cluster physical representation and literal action table

The onsite representation and virtual matrices of arXiv:2502.20257,
`example:z4z2`, lines 4481–4487. Physical coordinates are
`|p,s,r⟩ ↔ 4*p + 2*s + r`: the blocked cluster tensor stores its first
factor in the least significant bit. Thus physical qubits 2 and 3 correspond
to the second and first stored cluster factors, respectively.

Only the representation and block covariance are treated here, not L-symbols,
block independence, defect normalization, or gauging.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPSTensor

/-- The physical basis permutation for `(a,b)`, obtained by applying
`(X₁ ⊗ X₂) CNOT₁→₂` `a` times and `X₃` `b` times.
Source: arXiv:2502.20257, `example:z4z2`. -/
def z4z2GHZClusterBasisAction (g : ZMod 4 × ZMod 2) (i : Fin 8) : Fin 8 :=
  finProdFinEquiv
    ((![![0, 1, 2, 3], ![3, 2, 0, 1], ![1, 0, 3, 2], ![2, 3, 1, 0]]
      g.1 ((finProdFinEquiv (m := 4) (n := 2)).symm i).1 : Fin 4),
      ((finProdFinEquiv (m := 4) (n := 2)).symm i).2 + (⟨g.2.val, g.2.val_lt⟩ : Fin 2))

private theorem basisAction_zero : ∀ i, z4z2GHZClusterBasisAction 0 i = i := by decide

private theorem basisAction_add : ∀ g h i,
    z4z2GHZClusterBasisAction (g + h) i =
      z4z2GHZClusterBasisAction g (z4z2GHZClusterBasisAction h i) := by decide

/-- The finite permutation representation underlying the onsite symmetry. -/
def z4z2GHZClusterPerm : Multiplicative (ZMod 4 × ZMod 2) →* Equiv.Perm (Fin 8) where
  toFun g :=
    { toFun := z4z2GHZClusterBasisAction g.toAdd
      invFun := z4z2GHZClusterBasisAction (-g.toAdd)
      left_inv i := by rw [← basisAction_add, neg_add_cancel]; exact basisAction_zero i
      right_inv i := by rw [← basisAction_add, add_neg_cancel]; exact basisAction_zero i }
  map_one' := Equiv.ext basisAction_zero
  map_mul' g h := Equiv.ext (basisAction_add g.toAdd h.toAdd)

/-- The source's onsite Z₄ × Z₂ representation as eight-dimensional matrices. -/
noncomputable def z4z2GHZClusterAction :
    Multiplicative (ZMod 4 × ZMod 2) →* Matrix (Fin 8) (Fin 8) ℂ where
  toFun g := monomial (z4z2GHZClusterPerm g) (fun _ ↦ 1)
  map_one' := by rw [map_one]; exact monomial_one
  map_mul' g h := by simp [monomial_mul_monomial]

/-- Every physical action matrix is unitary. -/
theorem z4z2GHZClusterAction_unitary (g : Multiplicative (ZMod 4 × ZMod 2)) :
    z4z2GHZClusterAction g ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  monomial_mem_unitaryGroup _ _ (by simp)

/-- The literal Pauli Y, including its imaginary phases, in the source table. -/
noncomputable def z4z2GHZClusterPauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- The two rows of the action table of arXiv:2502.20257, lines 4483–4487.
The inner columns are ordered `(0,0),(0,1),(1,0),(1,1),...,(3,1)`;
this is the printed table reordered by the standard product coordinates. -/
noncomputable def z4z2GHZClusterVirtual (g : ZMod 4 × ZMod 2) (x : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (![![![1, pauliZ], ![pauliX, z4z2GHZClusterPauliY],
        ![pauliX, z4z2GHZClusterPauliY], ![1, pauliZ]],
      ![![1, pauliZ], ![1, pauliZ],
        ![pauliX, z4z2GHZClusterPauliY], ![pauliX, z4z2GHZClusterPauliY]]]
      x) g.1 g.2

/-- The action on block labels is parity of the first group coordinate. -/
def z4z2GHZClusterBlockAction (g : ZMod 4 × ZMod 2) (x : Fin 2) : Fin 2 :=
  x + ⟨g.1.val % 2, Nat.mod_lt _ (by decide)⟩

private theorem clusterBlocked_table (q : Fin 4) :
    clusterBlocked q =
      ![(1 / 2 : ℂ) • !![1, 0; 1, 0], (1 / 2 : ℂ) • !![1, 0; -1, 0],
        (1 / 2 : ℂ) • !![0, 1; 0, 1], (1 / 2 : ℂ) • !![0, -1; 0, 1]] q := by
  fin_cases q <;> simp

private theorem block_table (x : Fin 2) (i : Fin 8) :
    z4z2GHZClusterBlock x i =
      if ((finProdFinEquiv (m := 2) (n := 4)).symm i).1 = x then
        clusterBlocked ((finProdFinEquiv (m := 2) (n := 4)).symm i).2 else 0 := by
  simpa using z4z2GHZClusterBlock_apply x
    ((finProdFinEquiv (m := 2) (n := 4)).symm i).1
    ((finProdFinEquiv (m := 2) (n := 4)).symm i).2

private theorem pauliX_literal : pauliX = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

private theorem I_mul_mul_I (c : ℂ) : Complex.I * (c * Complex.I) = -c := by
  rw [mul_left_comm, Complex.I_mul_I, mul_neg_one]

/-- Every literal action tensor is Hermitian. -/
theorem z4z2GHZClusterVirtual_adjoint (g : ZMod 4 × ZMod 2) (x : Fin 2) :
    (z4z2GHZClusterVirtual g x)ᴴ = z4z2GHZClusterVirtual g x := by
  rcases g with ⟨a, b⟩
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    (ext j k; fin_cases j <;> fin_cases k <;>
      simp [z4z2GHZClusterVirtual, z4z2GHZClusterPauliY, pauliX, pauliZ,
        Matrix.conjTranspose_apply])

set_option maxHeartbeats 1600000 in
-- Check eight group elements, two block labels, and eight physical coordinates.
/-- Exact covariance for all sixteen virtual matrices in the printed table.
The physical index is transported forward by the onsite permutation.
Source: arXiv:2502.20257, `example:z4z2`, lines 4481–4487. -/
theorem z4z2GHZClusterBlock_transport (g : ZMod 4 × ZMod 2) (x : Fin 2) (i : Fin 8) :
    z4z2GHZClusterBlock (z4z2GHZClusterBlockAction g x)
        (z4z2GHZClusterBasisAction g i) =
      z4z2GHZClusterVirtual g x * z4z2GHZClusterBlock x i *
        (z4z2GHZClusterVirtual g x)ᴴ := by
  rcases g with ⟨a, b⟩
  rw [z4z2GHZClusterVirtual_adjoint]
  simp only [block_table, clusterBlocked_table]
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases i <;>
    simp [z4z2GHZClusterBlockAction, z4z2GHZClusterBasisAction,
      z4z2GHZClusterVirtual, z4z2GHZClusterPauliY, pauliX_literal, pauliZ,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.add_def, ZMod.val,
      mul_assoc, I_mul_mul_I]

/-- Three-qubit coordinates, with the source's qubit order. -/
def z4z2GHZClusterIndex (p s r : Fin 2) : Fin 8 :=
  finProdFinEquiv (p, finProdFinEquiv (s, r))

/-- The source generators and the square of the first generator, stated on
computational basis columns. These are precisely `(X₁⊗X₂) CNOT₁→₂`, `X₃`,
and `X₂`, respectively (arXiv:2502.20257, lines 4481 and 4487). -/
theorem z4z2GHZClusterAction_generators (p s r : Fin 2) (i : Fin 8) :
    (z4z2GHZClusterAction (.ofAdd (1, 0)) i (z4z2GHZClusterIndex p s r) =
      if i = z4z2GHZClusterIndex (p + 1) (s + p + 1) r then 1 else 0) ∧
    (z4z2GHZClusterAction (.ofAdd (0, 1)) i (z4z2GHZClusterIndex p s r) =
      if i = z4z2GHZClusterIndex p s (r + 1) then 1 else 0) ∧
    (z4z2GHZClusterAction (.ofAdd (2, 0)) i (z4z2GHZClusterIndex p s r) =
      if i = z4z2GHZClusterIndex p (s + 1) r then 1 else 0) := by
  have h : ∀ p s r,
      z4z2GHZClusterBasisAction (1, 0) (z4z2GHZClusterIndex p s r) =
        z4z2GHZClusterIndex (p + 1) (s + p + 1) r ∧
      z4z2GHZClusterBasisAction (0, 1) (z4z2GHZClusterIndex p s r) =
        z4z2GHZClusterIndex p s (r + 1) ∧
      z4z2GHZClusterBasisAction (2, 0) (z4z2GHZClusterIndex p s r) =
        z4z2GHZClusterIndex p (s + 1) r := by decide
  simp [z4z2GHZClusterAction, monomial_apply, z4z2GHZClusterPerm,
    (h p s r).1, (h p s r).2.1, (h p s r).2.2]

/-- The exact table in the paper's printed column order, with no projective
replacement of Y by a real Pauli product. -/
theorem z4z2GHZClusterVirtual_table :
    (fun x : Fin 2 ↦ ![z4z2GHZClusterVirtual (0, 0) x,
      z4z2GHZClusterVirtual (2, 0) x, z4z2GHZClusterVirtual (0, 1) x,
      z4z2GHZClusterVirtual (2, 1) x, z4z2GHZClusterVirtual (1, 0) x,
      z4z2GHZClusterVirtual (3, 0) x, z4z2GHZClusterVirtual (1, 1) x,
      z4z2GHZClusterVirtual (3, 1) x]) =
    ![![1, pauliX, pauliZ, z4z2GHZClusterPauliY, pauliX, 1,
        z4z2GHZClusterPauliY, pauliZ],
      ![1, pauliX, pauliZ, z4z2GHZClusterPauliY, 1, pauliX,
        pauliZ, z4z2GHZClusterPauliY]] := by
  funext x
  fin_cases x <;> rfl

/-- All virtual representatives in the literal table are involutions. -/
theorem z4z2GHZClusterVirtual_sq (g : ZMod 4 × ZMod 2) (x : Fin 2) :
    z4z2GHZClusterVirtual g x * z4z2GHZClusterVirtual g x = 1 := by
  rcases g with ⟨a, b⟩
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    simp [z4z2GHZClusterVirtual, z4z2GHZClusterPauliY, pauliX_literal, pauliZ,
      Matrix.one_fin_two]

/-- The onsite matrix action on each block is implemented by the literal
virtual representative, while its block label changes by parity of `a`.
This is the block action claim of arXiv:2502.20257, `example:z4z2`;
no normalization claim about defect tensors is made here. -/
theorem z4z2GHZClusterBlock_covariance (g : Multiplicative (ZMod 4 × ZMod 2))
    (x : Fin 2) (i : Fin 8) :
    twistedTensor (z4z2GHZClusterBlock x) z4z2GHZClusterAction g i =
      z4z2GHZClusterVirtual g.toAdd x *
        z4z2GHZClusterBlock (z4z2GHZClusterBlockAction g.toAdd x) i *
        (z4z2GHZClusterVirtual g.toAdd x)ᴴ := by
  obtain ⟨j, rfl⟩ := (z4z2GHZClusterPerm g).surjective i
  have htw : twistedTensor (z4z2GHZClusterBlock x) z4z2GHZClusterAction g
      (z4z2GHZClusterPerm g j) = z4z2GHZClusterBlock x j := by
    simp [twistedTensor, z4z2GHZClusterAction, monomial_apply,
      (z4z2GHZClusterPerm g).injective.eq_iff]
  rw [htw]
  change _ = _ * z4z2GHZClusterBlock _ (z4z2GHZClusterBasisAction g.toAdd j) * _
  rw [z4z2GHZClusterBlock_transport, z4z2GHZClusterVirtual_adjoint]
  simp only [← mul_assoc, z4z2GHZClusterVirtual_sq, one_mul]
  rw [mul_assoc, z4z2GHZClusterVirtual_sq, mul_one]

/-- On the unbroken subgroup `(2a,b)`, the table is the existing cluster
projective representation with swapped physical coordinates and the literal
phase `-i` at `(a,b)=(1,1)`. In particular the Y entries are not the real
product ZX. Source: arXiv:2502.20257, line 4487. -/
theorem z4z2GHZClusterVirtual_stabilizer (a b : ZMod 2) (x : Fin 2) :
    z4z2GHZClusterVirtual (2 * (a.val : ZMod 4), b) x =
      (if a = 1 ∧ b = 1 then -Complex.I else 1) •
        (clusterProjRep.X (.ofAdd (b, a)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hv : ∀ (a b : ZMod 2) (x : Fin 2),
      z4z2GHZClusterVirtual (2 * (a.val : ZMod 4), b) x =
        if a = 0 then (if b = 0 then 1 else pauliZ)
        else (if b = 0 then pauliX else z4z2GHZClusterPauliY) := by
    intro a b x
    fin_cases a <;> fin_cases b <;> fin_cases x <;> rfl
  rw [hv]
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;>
    norm_num [z4z2GHZClusterPauliY, clusterProjRep, clusterRepX,
      pauliX_literal, pauliZ, Matrix.one_fin_two]

end MPSTensor
