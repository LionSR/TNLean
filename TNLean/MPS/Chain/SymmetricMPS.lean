import TNLean.MPS.FundamentalTheorem.Basic

/-!
# Virtual symmetry equation for symmetric MPS

If a physical symmetry U(g) leaves an MPS state invariant (i.e., the rotated
tensor generates the same MPV family for every group element g), then the
single-block Fundamental Theorem produces an invertible virtual matrix X(g)
such that the rotated tensor equals A conjugated by X(g).

## References

* M. M. Wolf, *Quantum Channels & Operations: Guided Tour*, 2012, §6
* arXiv:2011.12127 (CPSV review), Eq. 48
* arXiv:0802.0447 (PGWSVC 2008), Condition C1
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- An MPS tensor `A` is symmetric under a monoid homomorphism `U` if
the rotated tensor `∑ j, U(g)_{ij} A^j` generates the same MPV family as `A`
for every element `g`. -/
def IsSymmetricMPS (G : Type*) [Monoid G]
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g : G, SameMPV A (fun i => ∑ j, U g i j • A j)

/-- **Virtual symmetry equation** (gauge-equiv form): if `A` is injective and
symmetric under `U`, then for each `g` the rotated tensor is gauge-equivalent
to `A`. -/
theorem virtual_symmetry_gaugeEquiv
    {G : Type*} [Monoid G]
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hA : IsInjective A) (hSym : IsSymmetricMPS G A U) (g : G) :
    GaugeEquiv A (fun i => ∑ j, U g i j • A j) :=
  fundamentalTheorem_singleBlock hA (hSym g)

/-- **Virtual symmetry equation** (explicit form): if `A` is injective and
symmetric under `U`, then for each `g` there exists an invertible matrix
`X(g)` and a nonzero scalar `φ(g)` such that
`∑_j U(g)_{ij} A^j = φ(g) • X * A^i * X⁻¹`.

In the single-block (injective) case `φ = 1`, but we include the phase to
match the general form expected by downstream projective-representation
arguments (arXiv:0802.0447 Condition C1, issue #76).

**Implementation note:** the proof extracts the `GL` witness from
`GaugeEquiv`, then packages the result as `GaugePhaseEquiv` with phase `φ = 1`.
If `GaugeEquiv` is refactored (e.g., to use `MulEquiv` or change the
conjugation convention), this proof will need updating. -/
theorem virtual_symmetry_eq
    {G : Type*} [Monoid G]
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hA : IsInjective A) (hSym : IsSymmetricMPS G A U) (g : G) :
    GaugePhaseEquiv A (fun i => ∑ j, U g i j • A j) :=
  let ⟨X, hX⟩ := virtual_symmetry_gaugeEquiv A U hA hSym g
  ⟨X, 1, one_ne_zero, fun i => by rw [one_smul]; exact hX i⟩

end MPSTensor
