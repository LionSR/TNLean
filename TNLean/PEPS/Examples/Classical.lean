/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import TNLean.PEPS.TorusSiteTensor

/-!
# Classical models: the Gibbs weights of a classical model as a PEPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"PEPS from classical models", `Papers/2011.12127/TN-Review-main.tex` lines 2483–2494: for a
classical model $H=\sum_{(i,j)}h(\sigma_i,\sigma_j)$ with nearest-neighbour interactions on the
square lattice and inverse temperature $\beta$, with
$M=\sum_{i,j}e^{-\beta h(i,j)/2}\lvert i)(j\rvert$, the PEPS tensor
$A=\bigl[\sum_i\lvert i\rangle(i\,i\,i\,i\rvert\bigr](1\otimes 1\otimes M\otimes M)$ reproduces the
expectation values of diagonal observables in the Gibbs state $e^{-\beta H}/Z$.
Review: arXiv:2011.12127, Appendix A, "PEPS from classical models".

**Formalized here.** On a torus the review's tensor has coefficient
$e^{-\beta H(\sigma)/2}$ at the configuration `σ`, where `H` counts each nearest-neighbour bond
once, read from a site to its left and to its lower neighbour. Hence its squared modulus is
the Gibbs weight $e^{-\beta H(\sigma)}$, and for every diagonal observable the normalized
expectation value in the PEPS equals the Gibbs expectation value. No symmetry of `h` is used:
each bond carries one factor of `M`, read from the site to its left or lower neighbour, and
`M` is never contracted with itself. The review's further remark on power-law correlations at
the critical temperature and gapless parent Hamiltonians is not formalized.

**Scope restriction (torus size):** stated for a torus of width and height at least three
sites. On a torus of width two the two bonds between horizontally neighbouring sites are one
edge of the simple lattice graph. Documented in
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## Main definitions

* `TNLean.PEPS.classicalBondMatrix`: the matrix $M_{ij}=e^{-\beta h(i,j)/2}$.
* `TNLean.PEPS.classicalSiteTensor`: the tensor
  $\bigl[\sum_i\lvert i\rangle(i\,i\,i\,i\rvert\bigr](1\otimes 1\otimes M\otimes M)$.
* `TNLean.PEPS.classicalPEPS`: the tensor at every site of the torus.
* `TNLean.PEPS.classicalEnergy`: the nearest-neighbour energy of a configuration.

## Main results

* `TNLean.PEPS.stateCoeff_classicalPEPS`: the coefficient is $e^{-\beta H(\sigma)/2}$.
* `TNLean.PEPS.normSq_stateCoeff_classicalPEPS`: its squared modulus is $e^{-\beta H(\sigma)}$.
* `TNLean.PEPS.expectation_classicalPEPS`: diagonal expectation values are Gibbs averages.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators ComplexConjugate

namespace TNLean
namespace PEPS

variable {q : ℕ}

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2490–2491.
The matrix $M=\sum_{i,j}e^{-\beta h(i,j)/2}\lvert i)(j\rvert$ of a nearest-neighbour
interaction `h` on the local states `Fin q` at inverse temperature `β`. -/
noncomputable def classicalBondMatrix (β : ℝ) (h : Fin q → Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℂ :=
  fun i j => (Real.exp (-(β / 2 * h i j)) : ℂ)

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2491–2493.
The tensor $A=\bigl[\sum_i\lvert i\rangle(i\,i\,i\,i\rvert\bigr](1\otimes 1\otimes M\otimes M)$
with virtual arguments ordered top, right, down, left: the top and right legs copy the
physical index `s`, and the bra $(s\rvert$ on the down and left legs composed with `M` gives
the factors $(s\rvert M\lvert b) = M_{sb}$ and $M_{sl}$. -/
noncomputable def classicalSiteTensor (β : ℝ) (h : Fin q → Fin q → ℝ) (t r b l s : Fin q) :
    ℂ :=
  if t = s ∧ r = s then classicalBondMatrix β h s b * classicalBondMatrix β h s l else 0

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2488–2489.
The nearest-neighbour energy $H(\sigma)=\sum_{(i,j)}h(\sigma_i,\sigma_j)$ on the torus, each bond
counted once and read from a site `v` to its left neighbour `v - (1,0)` and to its lower
neighbour `v - (0,1)`. For symmetric `h` this is the usual sum over unordered bonds. -/
def classicalEnergy {width height : ℕ} [NeZero width] [NeZero height] (h : Fin q → Fin q → ℝ)
    (σ : TorusVertex width height → Fin q) : ℝ :=
  ∑ v : TorusVertex width height, (h (σ v) (σ (v.1 - 1, v.2)) + h (σ v) (σ (v.1, v.2 - 1)))

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2491–2493.
The classical-model tensor at every site of the `width × height` torus. -/
noncomputable def classicalPEPS (β : ℝ) (h : Fin q → Fin q → ℝ) :
    Tensor (torusGraph width height) q :=
  torusSiteTensor (classicalSiteTensor β h)

variable {width height} [Fact (2 < width)] [Fact (2 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2483–2493.
The classical-model PEPS on a torus has coefficient $e^{-\beta H(\sigma)/2}$ at `σ`: every
bond contributes one factor $e^{-\beta h/2}$. Stated for width and height at least three (the
module's scope restriction on the torus size). -/
theorem stateCoeff_classicalPEPS (β : ℝ) (h : Fin q → Fin q → ℝ)
    (σ : TorusVertex width height → Fin q) :
    stateCoeff (classicalPEPS width height β h) σ =
      (Real.exp (-(β / 2 * classicalEnergy h σ)) : ℂ) := by
  rw [classicalPEPS, stateCoeff_torusSiteTensor, Fintype.sum_eq_single σ,
    Fintype.sum_eq_single σ]
  · have hsite : ∀ v : TorusVertex width height,
        classicalSiteTensor β h (σ v) (σ v) (σ (v.1, v.2 - 1)) (σ (v.1 - 1, v.2)) (σ v) =
          (Real.exp (-(β / 2 * (h (σ v) (σ (v.1 - 1, v.2)) +
            h (σ v) (σ (v.1, v.2 - 1))))) : ℂ) := by
      intro v
      rw [classicalSiteTensor, ite_eq_left (show σ v = σ v ∧ σ v = σ v from ⟨rfl, rfl⟩),
        classicalBondMatrix, classicalBondMatrix, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    simp only [hsite]
    rw [← Complex.ofReal_prod, ← Real.exp_sum, classicalEnergy, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
  · intro vb hvb
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hvb
    exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right fun h => hv h.1)
  · intro hb hhb
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hhb
    exact Finset.sum_eq_zero fun vb _ =>
      Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right fun h => hv h.2)

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2483–2493.
The product of the classical-model coefficient with its complex conjugate is the Gibbs
weight $e^{-\beta H(\sigma)}$. -/
theorem conj_mul_stateCoeff_classicalPEPS (β : ℝ) (h : Fin q → Fin q → ℝ)
    (σ : TorusVertex width height → Fin q) :
    conj (stateCoeff (classicalPEPS width height β h) σ) *
        stateCoeff (classicalPEPS width height β h) σ =
      (Real.exp (-(β * classicalEnergy h σ)) : ℂ) := by
  rw [stateCoeff_classicalPEPS, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2483–2493.
The squared modulus of the classical-model coefficient is the Gibbs weight
$e^{-\beta H(\sigma)}$. -/
theorem normSq_stateCoeff_classicalPEPS (β : ℝ) (h : Fin q → Fin q → ℝ)
    (σ : TorusVertex width height → Fin q) :
    Complex.normSq (stateCoeff (classicalPEPS width height β h) σ) =
      Real.exp (-(β * classicalEnergy h σ)) := by
  rw [stateCoeff_classicalPEPS, Complex.normSq_ofReal, ← Real.exp_add]
  congr 1
  ring

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2483–2494.
Diagonal expectation values of the classical-model PEPS are Gibbs averages. For the diagonal
observable $O=\sum_\sigma O(\sigma)\lvert\sigma\rangle\langle\sigma\rvert$ the expectation value
$\langle\psi\rvert O\lvert\psi\rangle/\langle\psi\vert\psi\rangle$ in the PEPS state
$\psi=\sum_\sigma\psi(\sigma)\lvert\sigma\rangle$ is
$\sum_\sigma\overline{\psi(\sigma)}O(\sigma)\psi(\sigma)/\sum_\sigma\lvert\psi(\sigma)\rvert^2$,
written here as explicit sums over configurations, and it equals
$\sum_\sigma O(\sigma)e^{-\beta H(\sigma)}/Z$ with $Z=\sum_\sigma e^{-\beta H(\sigma)}$. -/
theorem expectation_classicalPEPS (β : ℝ) (h : Fin q → Fin q → ℝ)
    (O : (TorusVertex width height → Fin q) → ℂ) :
    (∑ σ, conj (stateCoeff (classicalPEPS width height β h) σ) * O σ *
          stateCoeff (classicalPEPS width height β h) σ) /
        ∑ σ, conj (stateCoeff (classicalPEPS width height β h) σ) *
          stateCoeff (classicalPEPS width height β h) σ =
      (∑ σ : TorusVertex width height → Fin q,
          O σ * (Real.exp (-(β * classicalEnergy h σ)) : ℂ)) /
        ∑ σ : TorusVertex width height → Fin q, (Real.exp (-(β * classicalEnergy h σ)) : ℂ) := by
  congr 1
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_right_comm, conj_mul_stateCoeff_classicalPEPS, mul_comm]
  · exact Finset.sum_congr rfl fun σ _ => conj_mul_stateCoeff_classicalPEPS β h σ

end PEPS
end TNLean
