/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GaussRepresentation
import TNLean.Algebra.MonomialMatrix

/-!
# Local Gauss operators of monomial matter unitaries

When every matter unitary $U_{a,b}$ of a tuple is a monomial matrix
$U_{a,b}\ket{i}=\varphi_{a,b}(i)\ket{\sigma_{a,b}(i)}$, the local Gauss
operator

$\widetilde{\mathcal G}_g=\sum_{a,b}U_{T_g(a,b)}^\dagger U_{a,b}
  \otimes\ket{T_g(a,b)}\bra{a,b}$

of FBC25, Equation `eq:mcG` (arXiv:2502.20257, lines 3380--3387) is again a
monomial matrix. Its permutation part sends $(i,(a,b))$ to
$(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i),T_g(a,b))$, and its phase is
$\overline{\varphi_{T_g(a,b)}(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i))}\,
\varphi_{a,b}(i)$.
-/

noncomputable section

namespace TNLean.Algebra

open Matrix

variable {G n : Type*} [Group G]

/-- The permutation part of the local Gauss operator of a tuple of monomial matter
unitaries: $(i,(a,b))\mapsto(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i),T_g(a,b))$. -/
def gaussMonomialPerm (σ : G → G → Equiv.Perm n) (g : G) : Equiv.Perm (n × (G × G)) :=
  (Equiv.prodComm n (G × G)).trans
    ((Equiv.prodShear (gaussLegAction g)
      (fun l ↦ (σ l.1 l.2).trans
        (σ (gaussLegAction g l).1 (gaussLegAction g l).2).symm)).trans
      (Equiv.prodComm (G × G) n))

@[simp]
theorem gaussMonomialPerm_apply (σ : G → G → Equiv.Perm n) (g : G) (x : n × (G × G)) :
    gaussMonomialPerm σ g x =
      ((σ (gaussLegAction g x.2).1 (gaussLegAction g x.2).2).symm (σ x.2.1 x.2.2 x.1),
        gaussLegAction g x.2) :=
  rfl

/-- The phase of the local Gauss operator of a tuple of monomial matter unitaries:
$\overline{\varphi_{T_g(a,b)}(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i))}\,
\varphi_{a,b}(i)$. -/
def gaussMonomialPhase (σ : G → G → Equiv.Perm n) (φ : G → G → n → ℂ) (g : G)
    (x : n × (G × G)) : ℂ :=
  star (φ (gaussLegAction g x.2).1 (gaussLegAction g x.2).2
    ((σ (gaussLegAction g x.2).1 (gaussLegAction g x.2).2).symm (σ x.2.1 x.2.2 x.1))) *
    φ x.2.1 x.2.2 x.1

variable [DecidableEq G] [Fintype n] [DecidableEq n]

/-- The local Gauss operator of a tuple of monomial matter unitaries is monomial.
This is FBC25, Equation `eq:mcG` (arXiv:2502.20257, lines 3380--3387) evaluated on
monomial blocks. -/
theorem gaussOperator_eq_monomial (R : G → G → Matrix.unitaryGroup n ℂ)
    (σ : G → G → Equiv.Perm n) (φ : G → G → n → ℂ)
    (hR : ∀ a b, (R a b : Matrix n n ℂ) = monomial (σ a b) (φ a b)) (g : G) :
    gaussOperator R g = monomial (gaussMonomialPerm σ g) (gaussMonomialPhase σ φ g) := by
  classical
  ext x y
  by_cases h2 : x.2 = gaussLegAction g y.2
  · obtain ⟨i, l⟩ := x
    obtain ⟨j, m⟩ := y
    simp only at h2
    subst h2
    have hblock : (Matrix.unitaryFactorizationComparison R m.1 m.2
        (gaussLegAction g m).1 (gaussLegAction g m).2 : Matrix n n ℂ) =
        monomial ((σ m.1 m.2).trans
            (σ (gaussLegAction g m).1 (gaussLegAction g m).2).symm)
          fun s ↦ star (φ (gaussLegAction g m).1 (gaussLegAction g m).2
            ((σ (gaussLegAction g m).1 (gaussLegAction g m).2).symm (σ m.1 m.2 s))) *
            φ m.1 m.2 s := by
      rw [Matrix.unitaryFactorizationComparison_coe, hR, hR, star_eq_conjTranspose,
        conjTranspose_monomial, monomial_mul_monomial]
      rfl
    have hx : gaussOperator R g (i, gaussLegAction g m) (j, m) =
        (Matrix.unitaryFactorizationComparison R m.1 m.2
          (gaussLegAction g m).1 (gaussLegAction g m).2 : Matrix n n ℂ) i j := by
      simp [gaussOperator]
    rw [hx, hblock, monomial_apply, monomial_apply]
    by_cases hij : i = (σ (gaussLegAction g m).1 (gaussLegAction g m).2).symm (σ m.1 m.2 j)
    · subst hij
      simp [gaussMonomialPhase]
    · rw [ite_eq_right, ite_eq_right]
      · intro h
        exact hij (by simpa using congrArg Prod.fst h)
      · simpa using hij
  · rw [gaussOperator_apply_of_ne R g x y h2, monomial_apply_of_ne]
    intro h
    exact h2 (by simpa using congrArg Prod.snd h)

end TNLean.Algebra
