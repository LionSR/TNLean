/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonianBasic
import TNLean.MPS.CanonicalForm.BNT.Basic
import TNLean.MPS.Transfer.Irreducible.Periodic

/-!
# Commuting parent Hamiltonians

This file records the commutation equations for parent Hamiltonians, the
length-two specialization used in the nearest-neighbor commuting parent
Hamiltonian part of arXiv:1606.00608, and the source ground-space spanning
clause from Definition 3.9.

## Main definitions

* `MPSTensor.IsCommutingParentHam A L N` — the local terms of the parent
  Hamiltonian on \(N\) sites with block length \(L\) mutually commute.
* `MPSTensor.IsNNCPH A N` — length-two commutativity of the translated parent
  interaction terms.
* `MPSTensor.HasParentHamiltonianGroundSpaceSpanning B L A` — the Definition
  3.9 condition that the kernel of \(H_L^{(N)}\) is spanned by the BNT vectors
  \(V^{(N)}(A_j)\) for every \(N>L\).
* `MPSTensor.HasNNCPHGroundSpace B A N` — the fixed-chain nearest-neighbor
  form: length-two commutation and the ground-space spanning equation (the zero energy of
  \(V^{(N)}(B)\) holds for every tensor and is not recorded).
* `MPSTensor.HasNNCPHGroundSpaces B A` — the all-chain source condition:
  `HasNNCPHGroundSpace B A N` for every \(N>2\).

## Main results

* `MPSTensor.IsCommutingParentHam.ham_comm_parentRingInteraction_term` — if local terms commute,
  the full Hamiltonian commutes with each local term.
* `MPSTensor.hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning` —
  the all-chain source condition is equivalently all-chain nearest-neighbor
  commutation together with the ground-space spanning clause of
  arXiv:1606.00608, Definition 3.9.
* `MPSTensor.nncph_implies_rfp` is proved downstream in
  `TNLean.MPS.RFP.BeigiLoopBNTIdentification`, after the Beigi loop construction
  and its comparison with normal tensors are available.

## References

* arXiv:1606.00608, Section 3.3 Definition 3.9, Theorem 3.10
* S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306 —
  ground-space characterization for commuting nearest-neighbor
  Hamiltonians in 1D (consumed only in the NNCPH \(\Longrightarrow\) RFP direction)
-/

open MPTensor

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A parent Hamiltonian has **commuting** local terms when the translated
interaction projectors commute.

See arXiv:1606.00608, Definition 3.9. The source writes the local translated
condition as $[\tau_j(P_L),P_L]=0$ for the interacting translates; this
predicate records the resulting pairwise commutativity of the translated local
terms. The source definition of a parent Hamiltonian also includes the
ground-space spanning condition by the periodic MPS vectors of the BNT
components. -/
def IsCommutingParentHam (A : MPSTensor d D) (L N : ℕ) : Prop :=
  ∀ i j : Fin N, haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toLin' ((parentRingInteraction A L N).term i) *
        Matrix.toLin' ((parentRingInteraction A L N).term j) =
      Matrix.toLin' ((parentRingInteraction A L N).term j) *
        Matrix.toLin' ((parentRingInteraction A L N).term i)

/-- **Nearest-neighbor commuting parent Hamiltonian** (NNCPH): the length-two
commutation equations for the translated parent interaction terms.

See arXiv:1606.00608, Definition 3.9. The source nearest-neighbor condition
also fixes \(L=2\) and includes the parent-Hamiltonian ground-space spanning
condition, which is not part of this predicate. -/
def IsNNCPH (A : MPSTensor d D) (N : ℕ) : Prop :=
  IsCommutingParentHam A 2 N

/-- Gauge-equivalent tensors have the same nearest-neighbor parent-Hamiltonian
commutation equations. -/
theorem _root_.MPTensor.GaugeEquiv.isNNCPH {A B : MPSTensor d D} (h : GaugeEquiv A B) {N : ℕ} :
    IsNNCPH A N → IsNNCPH B N := by
  intro hA i j
  have : NeZero N := NeZero.of_pos i.pos
  rw [← h.parentRingInteraction_eq 2 N]
  exact hA i j

/-- Source Definition 3.9 parent-Hamiltonian ground-space spanning clause.

Given a canonical-form tensor \(B\) with BNT components \(A_j\), the source says
that \(H_L^{(N)}\) is a parent Hamiltonian when, for every \(N>L\), the kernel
of \(H_L^{(N)}\) is spanned by \(|V^{(N)}(A_j)\rangle\).

The predicate records only this spanning equation; a theorem using it must
separately supply the hypothesis that the family \(A_j\) is the BNT family of
\(B\).

See arXiv:1606.00608, Definition 3.9, source lines 522--524. -/
def HasParentHamiltonianGroundSpaceSpanning (B : MPSTensor d D) (L : ℕ)
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j)) : Prop :=
  ∀ N : ℕ, (hLN : L < N) → haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toLin' (parentRingInteraction B L N).hamiltonian) = bntMPSVectorSpan A N

/-- Fixed-chain nearest-neighbor commuting parent-Hamiltonian ground-space
condition from arXiv:1606.00608, Definition 3.9 and Theorem 3.10(iii).

For a canonical-form tensor \(B\) with BNT components \(A_j\), this packages
the two finite-chain equations
\[
  h_i h_j=h_j h_i,\qquad
  \ker H_2^{(N)}(B)=\operatorname{span}\{V^{(N)}(A_j)\}_j .
\]
The third equation of the source, the zero energy \(h_iV^{(N)}(B)=0\) of the periodic vector,
holds for every tensor (`toLp_mpv_mem_zeroSpace_parentRingInteraction`) and is not recorded.
The source theorem quantifies this condition over all \(N>2\).  This definition
only records the condition for one fixed chain length; it does not assert that
the displayed spanning equation has been proved for any tensor. -/
def HasNNCPHGroundSpace (B : MPSTensor d D)
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j))
    (N : ℕ) [NeZero N] : Prop :=
  IsNNCPH B N ∧
    LinearMap.ker (Matrix.toLin' (parentRingInteraction B 2 N).hamiltonian) =
      bntMPSVectorSpan A N

/-- All-chain nearest-neighbor commuting parent-Hamiltonian ground-space
condition.

This is the source quantification in arXiv:1606.00608, Theorem 3.10(iii):
for every \(N>2\), the nearest-neighbor parent terms commute and the ground space of
\(H_2^{(N)}\) is spanned by the BNT vectors (the zero energy of the periodic MPS vector is
automatic). It packages only the condition; it does not prove the spanning
equation for any tensor. -/
def HasNNCPHGroundSpaces (B : MPSTensor d D)
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j)) : Prop :=
  ∀ N : ℕ, (hN : 2 < N) → haveI : NeZero N := ⟨by omega⟩; HasNNCPHGroundSpace B A N

/-- The nearest-neighbor commuting condition is a special case of the commuting
parent Hamiltonian (length two). -/
theorem IsNNCPH.isCommutingParentHam {A : MPSTensor d D} {N : ℕ} (h : IsNNCPH A N) :
    IsCommutingParentHam A 2 N :=
  h

/-- The full fixed-chain NNCPH ground-space condition includes length-two
local-term commutation. -/
theorem HasNNCPHGroundSpace.isNNCPH {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} [NeZero N] (h : HasNNCPHGroundSpace B A N) :
    IsNNCPH B N :=
  h.1

/-- The full fixed-chain NNCPH ground-space condition contains the BNT
ground-space spanning equation. -/
theorem HasNNCPHGroundSpace.groundSpaceSpanning {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} [NeZero N] (h : HasNNCPHGroundSpace B A N) :
    LinearMap.ker (Matrix.toLin' (parentRingInteraction B 2 N).hamiltonian) =
      bntMPSVectorSpan A N :=
  h.2

/-- Quantifying the fixed-chain NNCPH ground-space condition over \(N>2\)
supplies the nearest-neighbor instance of the parent-Hamiltonian spanning
predicate. -/
theorem HasNNCPHGroundSpace.hasParentHamiltonianGroundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (h : ∀ N : ℕ, (hN : 2 < N) → haveI : NeZero N := ⟨by omega⟩;
      HasNNCPHGroundSpace B A N) :
    HasParentHamiltonianGroundSpaceSpanning B 2 A := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  exact (h N (by omega)).groundSpaceSpanning

/-- The all-chain NNCPH ground-space condition gives the fixed-chain condition. -/
theorem HasNNCPHGroundSpaces.hasNNCPHGroundSpace {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} (h : HasNNCPHGroundSpaces B A) (hN : 2 < N) :
    haveI : NeZero N := ⟨by omega⟩;
    HasNNCPHGroundSpace B A N :=
  h N hN

/-- The all-chain source condition contains the parent-Hamiltonian
ground-space spanning clause. -/
theorem HasNNCPHGroundSpaces.hasParentHamiltonianGroundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (h : HasNNCPHGroundSpaces B A) :
    HasParentHamiltonianGroundSpaceSpanning B 2 A :=
  HasNNCPHGroundSpace.hasParentHamiltonianGroundSpaceSpanning h

/-- The all-chain NNCPH ground-space condition is equivalently the all-chain
nearest-neighbor commutation equations together with the source ground-space
spanning clause.

For \(N>2\), the zero-energy equation for \(V^{(N)}(B)\) is an unconditional
consequence of the parent-Hamiltonian construction. It therefore need not be
assumed separately; the remaining conditions are the length-two commuting
condition and the spanning equation of arXiv:1606.00608, Definition 3.9.

See arXiv:1606.00608, Definition 3.9 and Theorem 3.10(iii). -/
theorem hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)} :
    HasNNCPHGroundSpaces B A ↔
      (∀ N : ℕ, 2 < N → IsNNCPH B N) ∧
        HasParentHamiltonianGroundSpaceSpanning B 2 A := by
  constructor
  · intro h
    exact
      ⟨fun N hN => haveI : NeZero N := ⟨by omega⟩; (h N hN).isNNCPH,
        h.hasParentHamiltonianGroundSpaceSpanning⟩
  · rintro ⟨hComm, hSpan⟩ N hN
    have : NeZero N := ⟨by omega⟩
    exact ⟨hComm N hN, hSpan N (by omega)⟩

/-- If each BNT vector is killed by the parent Hamiltonian, then their span is
contained in the parent-Hamiltonian kernel.

This is the easy inclusion in the source spanning equation
\[
  \ker H_L^{(N)}(B)
  =
  \operatorname{span}\{V^{(N)}(A_j):j=1,\ldots,g\}
\]
from arXiv:1606.00608, Definition 3.9, source lines 522--524. -/
theorem bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_annihilates
    {B : MPSTensor d D} {r : ℕ} {dim : Fin r → ℕ}
    {A : (j : Fin r) → MPSTensor d (dim j)} {L N : ℕ} [NeZero N]
    (h : ∀ j : Fin r, Matrix.toLin' (parentRingInteraction B L N).hamiltonian (mpv (A j)) = 0) :
    bntMPSVectorSpan A N ≤
      LinearMap.ker (Matrix.toLin' (parentRingInteraction B L N).hamiltonian) := by
  rw [bntMPSVectorSpan]
  refine Submodule.span_le.mpr ?_
  intro v hv
  rcases hv with ⟨j, rfl⟩
  exact LinearMap.mem_ker.mpr (h j)

/-- If each BNT vector lies in the zero space of the parent interaction on the ring, then the
BNT span is contained in the parent-Hamiltonian kernel.

This records the zero-energy half of the source parent-Hamiltonian ground-space
spanning condition from arXiv:1606.00608, Definition 3.9, source lines
522--524. The reverse inclusion is the hard spanning direction. -/
theorem bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_mem_zeroSpace
    {B : MPSTensor d D} {r : ℕ} {dim : Fin r → ℕ}
    {A : (j : Fin r) → MPSTensor d (dim j)} {L N : ℕ} [NeZero N]
    (h : ∀ j : Fin r,
      WithLp.toLp 2 (mpv (A j) : NSiteSpace d N) ∈ (parentRingInteraction B L N).zeroSpace) :
    bntMPSVectorSpan A N ≤
      LinearMap.ker (Matrix.toLin' (parentRingInteraction B L N).hamiltonian) := by
  refine bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_annihilates ?_
  intro j
  rw [Matrix.toLin'_apply, ManyBody.Interaction.hamiltonian, Matrix.sum_mulVec]
  exact Finset.sum_eq_zero fun i _ => ManyBody.Interaction.mem_zeroSpace_iff.mp (h j) i

/-- The commuting condition is symmetric: if `h i j` holds, then `h j i` holds. -/
theorem IsCommutingParentHam.symm {A : MPSTensor d D} {L N : ℕ}
    (h : IsCommutingParentHam A L N) (i j : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toLin' ((parentRingInteraction A L N).term j) *
        Matrix.toLin' ((parentRingInteraction A L N).term i) =
      Matrix.toLin' ((parentRingInteraction A L N).term i) *
        Matrix.toLin' ((parentRingInteraction A L N).term j) :=
  (h i j).symm

/-- If the parent Hamiltonian commutes, then the Hamiltonian commutes with
each local term. -/
theorem IsCommutingParentHam.ham_comm_parentRingInteraction_term {A : MPSTensor d D} {L N : ℕ}
    (_h : IsCommutingParentHam A L N) (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toLin' (parentRingInteraction A L N).hamiltonian *
        Matrix.toLin' ((parentRingInteraction A L N).term i) =
      Matrix.toLin' ((parentRingInteraction A L N).term i) *
        Matrix.toLin' (parentRingInteraction A L N).hamiltonian := by
  have : NeZero N := NeZero.of_pos i.pos
  simp only [ManyBody.Interaction.hamiltonian, map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  ext j : 1
  exact _h j i

end MPSTensor
