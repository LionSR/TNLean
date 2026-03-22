import TNLean.MPS.FundamentalTheorem.Basic

/-!
# Virtual symmetry equation for symmetric MPS

If a physical symmetry U(g) leaves an MPS state invariant (i.e., the rotated
tensor generates the same MPV family for every group element g), then the
single-block Fundamental Theorem produces an invertible virtual matrix X(g)
such that the rotated tensor equals A conjugated by X(g).

## References

* Wolf 2012 §6
* arXiv:2011.12127 (CPSV review), Eq. 48
* arXiv:0802.0447 (PGWSVC 2008), Condition C1
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- An MPS tensor `A` is symmetric under a group representation `U` if
the rotated tensor `∑ j, U(g)_{ij} A^j` generates the same MPV family as `A`
for every group element `g`. -/
def IsSymmetricMPS (G : Type*) [Group G]
    (A : MPSTensor d D) (U : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g : G, SameMPV A (fun i => ∑ j, U g i j • A j)

/-- **Virtual symmetry equation** (gauge-equiv form): if `A` is injective and
symmetric under `U`, then for each `g` the rotated tensor is gauge-equivalent
to `A`. -/
theorem virtual_symmetry_gaugeEquiv
    {G : Type*} [Group G]
    (A : MPSTensor d D) (U : G → Matrix (Fin d) (Fin d) ℂ)
    (hA : IsInjective A) (hSym : IsSymmetricMPS G A U) (g : G) :
    GaugeEquiv A (fun i => ∑ j, U g i j • A j) :=
  fundamentalTheorem_singleBlock hA (hSym g)

/-- **Virtual symmetry equation** (explicit form): if `A` is injective and
symmetric under `U`, then for each `g` there exists an invertible matrix
`X(g)` such that `∑_j U(g)_{ij} A^j = X * A^i * X⁻¹`. -/
theorem virtual_symmetry_eq
    {G : Type*} [Group G]
    (A : MPSTensor d D) (U : G → Matrix (Fin d) (Fin d) ℂ)
    (hA : IsInjective A) (hSym : IsSymmetricMPS G A U) (g : G) :
    ∃ (X : GL (Fin D) ℂ), ∀ i,
      ∑ j, U g i j • A j =
        (X : Matrix (Fin D) (Fin D) ℂ) * A i *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
  virtual_symmetry_gaugeEquiv A U hA hSym g

end MPSTensor
