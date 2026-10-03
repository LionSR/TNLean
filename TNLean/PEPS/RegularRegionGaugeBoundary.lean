/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionTreeGauge
import TNLean.PEPS.RegularBoundaryState

/-!
# The boundary projector after a regular vertex gauge

A vertex gauge transports the crossing labels by a permutation of their group
basis. Pulling back the regular boundary projector along this permutation gives
an orthogonal projector of the same rank and trace. The permutation includes
the inserted bond operator when the region endpoint is the head of the bond.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, accessible virtual
systems and the boundary disentangling argument, local source lines 1765–1820
and 1935–1990. These are coordinate identities; no assertion of flatness of
arbitrary internal operators or of an entropy formula is made here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]

/-- The boundary transport in an ordering of the crossing bonds.
Source: SCP10, disentangling of boundary group operators, lines 1935–1990. -/
noncomputable def regularRegionBoundaryGaugeEquiv (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (Fin b → G) ≃ (Fin b → G) :=
  (e.symm.arrowCongr (Equiv.refl G)).trans
    ((regularRegionBoundaryTransport R k u).trans (e.arrowCongr (Equiv.refl G)))

omit [Fintype G] in
/-- Numbering the transported crossing labels agrees with their native transport. -/
theorem regularRegionBoundaryGaugeEquiv_apply (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (x : Fin b → G) (f : {f : Edge Γ // IsRegionBoundaryEdge R f}) :
    regularRegionBoundaryGaugeEquiv R k u e x (e f) =
      regularRegionBoundaryTransport R k u (fun f => x (e f)) f := by
  simp [regularRegionBoundaryGaugeEquiv, Equiv.arrowCongr, Function.comp_def]

variable [DecidableEq G]

/-- The invariant boundary projector pulled back along the actual label transport.
Source: SCP10, the boundary coordinate changes of lines 1935–1990. -/
noncomputable def regularRegionGaugeBoundaryProjector (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    Matrix (Fin b → G) (Fin b → G) ℂ :=
  (regularBoundaryProjector b).submatrix (regularRegionBoundaryGaugeEquiv R k u e)
    (regularRegionBoundaryGaugeEquiv R k u e)

/-- Boundary transport preserves idempotence of the averaging projector. -/
theorem regularRegionGaugeBoundaryProjector_mul_self (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularRegionGaugeBoundaryProjector R k u e * regularRegionGaugeBoundaryProjector R k u e =
      regularRegionGaugeBoundaryProjector R k u e := by
  rw [regularRegionGaugeBoundaryProjector, Matrix.submatrix_mul_equiv,
    regularBoundaryProjector_mul_self]

/-- Pulling back by the transported labels preserves self-adjointness. -/
theorem regularRegionGaugeBoundaryProjector_conjTranspose (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) (n : ℕ)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (regularRegionGaugeBoundaryProjector R k u e).conjTranspose =
      regularRegionGaugeBoundaryProjector R k u e := by
  rw [regularRegionGaugeBoundaryProjector, Matrix.conjTranspose_submatrix,
    regularBoundaryProjector_conjTranspose]

/-- A nonempty transported boundary has the usual invariant-subspace dimension.
Source: SCP10, the boundary dimension count in Theorem 6.9, lines 2027–2037. -/
theorem rank_regularRegionGaugeBoundaryProjector (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) {b : ℕ} (hb : 0 < b)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (regularRegionGaugeBoundaryProjector R k u e).rank = Fintype.card G ^ (b - 1) := by
  rw [regularRegionGaugeBoundaryProjector, Matrix.rank_submatrix,
    rank_regularBoundaryProjector b hb]

/-- The transported projector has the same trace as the regular boundary average. -/
theorem trace_regularRegionGaugeBoundaryProjector (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) (n : ℕ)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (regularRegionGaugeBoundaryProjector R k u e).trace = (Fintype.card G : ℂ) ^ n := by
  have h := (regularRegionBoundaryGaugeEquiv R k u e).sum_comp
    (fun x => regularBoundaryProjector (G := G) (n + 1) x x)
  change (∑ x, regularBoundaryProjector (G := G) (n + 1)
    (regularRegionBoundaryGaugeEquiv R k u e x)
    (regularRegionBoundaryGaugeEquiv R k u e x)) = _
  rw [h]
  exact trace_regularBoundaryProjector n

end TNLean.PEPS
