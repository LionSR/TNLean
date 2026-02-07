import MPSLean.MPS.Defs

namespace MPSTensor

variable {d D : ℕ}

/-- Algebraic injectivity (spanning formulation): the matrices `{A i}` span the full matrix
algebra `Matrix (Fin D) (Fin D) ℂ`. -/
def IsInjective (A : MPSTensor d D) : Prop :=
  Submodule.span ℂ (Set.range A) = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))

/-- `N`-block injectivity: after blocking `N` sites, the set of all products
`A^{i₁} * ⋯ * A^{i_N}` spans the full matrix algebra.

We index the blocked tensors by `σ : Fin N → Fin d`, i.e. words of length `N`. -/
def IsNBlkInjective (A : MPSTensor d D) (N : ℕ) : Prop :=
  Submodule.span ℂ (Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ))
    = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))

/-- Normality (a.k.a. quantum Wielandt property, in this algebraic formulation):
there exists some blocking length `N` such that the tensor is `N`-block-injective. -/
def IsNormal (A : MPSTensor d D) : Prop :=
  ∃ N : ℕ, IsNBlkInjective (d := d) (D := D) A N

end MPSTensor
