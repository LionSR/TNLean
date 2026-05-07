import TNLean.MPS.Symmetry.Defs

/-!
# Virtual symmetry equation for symmetric MPS

If a physical symmetry U(g) leaves an MPS state invariant (i.e., the rotated
tensor generates the same MPV family for every group element g), then the
single-block Fundamental Theorem produces an invertible virtual matrix X(g)
such that the rotated tensor equals A conjugated by X(g).

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

In the single-block (injective) case `φ = 1`, but we include the phase to
match the general form needed by the projective-representation arguments
(arXiv:0802.0447 Condition C1). -/
theorem virtual_symmetry_eq
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hA : IsInjective A) (hSym : IsOnSiteSymmetric A U) (g : G) :
    GaugePhaseEquiv A (twistedTensor A U g) :=
  let ⟨X, hX⟩ := gaugeEquiv_twistedTensor_of_injective A hA U hSym g
  ⟨X, 1, one_ne_zero, fun i => by rw [one_smul]; exact hX i⟩

end MPSTensor
