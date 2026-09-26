/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.Defs

/-!
# Virtual symmetry equation for symmetric MPS

If a physical symmetry U(g) leaves an MPS state invariant (i.e., the rotated
tensor generates the same MPV family for every group element g), then the
single-block Fundamental Theorem produces an invertible virtual matrix X(g)
such that the rotated tensor equals A conjugated by X(g).

On-site symmetry is also transported along a rescaling of the tensor
(`IsOnSiteSymmetric.smul`) and along a virtual gauge transformation
(`IsOnSiteSymmetric.of_gaugeEquiv`).

## References

* M. M. Wolf, *Quantum Channels & Operations: Guided Tour*, 2012, Section 6
* arXiv:2011.12127 (CPSV review), Equation 48
* arXiv:0802.0447 (PGWSVC 2008), Condition C1
-/

open scoped Matrix

namespace MPSTensor

variable {G : Type*} [Monoid G] {d D : ℕ}

/-- **Virtual symmetry equation** (explicit form): if `A` is injective and
on-site symmetric under `U`, then for each `g` there exists an invertible matrix
`X(g)` and a nonzero scalar `φ(g)` such that
`∑_j U(g)_{ij} A^j = φ(g) • X * A^i * X⁻¹`.

In the single-block (injective) case one can take `φ = 1`, but the statement
includes the phase because the general symmetry relation allows a nonzero
scalar factor; this is the form that appears in the paper
(arXiv:0802.0447 Condition C1). -/
theorem virtual_symmetry_eq
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hA : Kraus.IsInjective A) (hSym : IsOnSiteSymmetric A U) (g : G) :
    GaugePhaseEquiv A (twistedTensor A U g) :=
  let ⟨X, hX⟩ := gaugeEquiv_twistedTensor_of_injective A hA U hSym g
  ⟨X, 1, one_ne_zero, fun i => by rw [one_smul]; exact hX i⟩

/-- On-site symmetry is invariant under rescaling the tensor by any scalar. -/
theorem IsOnSiteSymmetric.smul {A : MPSTensor d D} {U : G →* Matrix (Fin d) (Fin d) ℂ}
    (c : ℂ) (hA : IsOnSiteSymmetric A U) : IsOnSiteSymmetric (c • A) U := by
  intro g N σ
  have hmpv : ∀ B : MPSTensor d D, mpv (c • B) σ = c ^ N * mpv B σ := by
    intro B
    simp only [mpv, coeff]
    rw [show (c • B : MPSTensor d D) = fun i => c • B i from rfl, Kraus.evalWord_smul]
    simp [List.length_ofFn, Matrix.trace_smul]
  have htw : twistedTensor (c • A) U g = c • twistedTensor A U g := by
    funext i
    simp only [twistedTensor, Pi.smul_apply, Finset.smul_sum, smul_comm c]
  rw [htw, hmpv, hmpv, hA g N σ]

/-- On-site symmetry is invariant under a virtual gauge transformation. -/
theorem IsOnSiteSymmetric.of_gaugeEquiv {A B : MPSTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ}
    (hA : IsOnSiteSymmetric A U) (hAB : GaugeEquiv A B) : IsOnSiteSymmetric B U := by
  intro g N σ
  obtain ⟨X, hX⟩ := hAB
  have hTw : GaugeEquiv (twistedTensor A U g) (twistedTensor B U g) := by
    refine ⟨X, fun i => ?_⟩
    simp only [twistedTensor, hX, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  exact ((GaugeEquiv.sameMPV ⟨X, hX⟩ N σ).symm.trans (hA g N σ)).trans (hTw.sameMPV N σ)

end MPSTensor
