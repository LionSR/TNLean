/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.PEPS.TorusSiteTensor

/-!
# Cluster: the two-dimensional cluster state as a PEPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"Two dimensions: PEPS", "The cluster state", `Papers/2011.12127/TN-Review-main.tex`
lines 2426–2432: the 2D cluster state on the square lattice is a PEPS with
$A=\lvert 0\rangle(00{+}{+}\rvert+\lvert 1\rangle(11{-}{-}\rvert$, where
$(\pm\rvert=[(0\rvert\pm(1\rvert]/\sqrt2$, obtained from the circuit of controlled-`Z` gates
between nearest neighbours acting on $\lvert +\rangle^{\otimes N}$.
Review: arXiv:2011.12127, Appendix A, "The cluster state" (two dimensions).

**Formalized here.** The review's tensor at every site of a torus of `N = width · height`
sites has coefficient $2^{-N}(-1)^{\sum_{\langle u,v\rangle}\sigma_u\sigma_v}$ at `σ`, the sum
running over the nearest-neighbour bonds. This is `2^{-N/2}` times the coefficient of
$\prod_{\langle u,v\rangle}CZ_{uv}\lvert +\rangle^{\otimes N}$, the review's cluster state; the
factor comes from the normalized legs $(\pm\rvert$ as printed.

**Scope restriction (torus size):** stated for a torus of width and height at least three
sites. On a torus of width two the two bonds between horizontally neighbouring sites are one
edge of the simple lattice graph. Documented in
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## Main definitions

* `TNLean.PEPS.clusterSiteTensor`: the tensor
  $\lvert 0\rangle(00{+}{+}\rvert+\lvert 1\rangle(11{-}{-}\rvert$.
* `TNLean.PEPS.clusterPEPS`: the tensor at every site of the torus.

## Main results

* `TNLean.PEPS.stateCoeff_clusterPEPS`: the coefficient of the cluster PEPS.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2426–2430.
The cluster tensor $A=\lvert 0\rangle(00{+}{+}\rvert+\lvert 1\rangle(11{-}{-}\rvert$ with
virtual arguments ordered top, right, down, left: the top and right legs copy the physical
index `s`, and the down and left legs carry $(+\rvert$ for `s = 0` and $(-\rvert$ for `s = 1`,
with $(\pm\rvert b) = (\pm 1)^b/\sqrt2$. -/
noncomputable def clusterSiteTensor (t r b l s : Fin 2) : ℂ :=
  if t = s ∧ r = s then
    Complex.invSqrtTwo * (-1) ^ (s.val * b.val) * (Complex.invSqrtTwo * (-1) ^ (s.val * l.val))
  else 0

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2426–2430.
The cluster tensor at every site of the `width × height` torus. -/
noncomputable def clusterPEPS : Tensor (torusGraph width height) 2 :=
  torusSiteTensor clusterSiteTensor

variable {width height} [Fact (2 < width)] [Fact (2 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2426–2432.
The cluster PEPS on a torus of `width · height` sites has coefficient
$2^{-\mathrm{width}\cdot\mathrm{height}}(-1)^{\sum_v \sigma_v\sigma_{v+e_1}+\sigma_v
\sigma_{v+e_2}}$: up to the factor `2^{-N/2}`, the coefficient of the controlled-`Z` gates on
all nearest-neighbour bonds applied to $\lvert +\rangle^{\otimes N}$. Stated for width and
height at least three (the module's scope restriction on the torus size). -/
theorem stateCoeff_clusterPEPS (σ : TorusVertex width height → Fin 2) :
    stateCoeff (clusterPEPS width height) σ =
      (2⁻¹ : ℂ) ^ (width * height) *
        ∏ v, (-1 : ℂ) ^ ((σ v).val * (σ (v.1 + 1, v.2)).val +
          (σ v).val * (σ (v.1, v.2 + 1)).val) := by
  rw [clusterPEPS, stateCoeff_torusSiteTensor, Fintype.sum_eq_single σ, Fintype.sum_eq_single σ]
  · have hsite : ∀ v : TorusVertex width height,
        clusterSiteTensor (σ v) (σ v) (σ (v.1, v.2 - 1)) (σ (v.1 - 1, v.2)) (σ v) =
          2⁻¹ * ((-1) ^ ((σ v).val * (σ (v.1, v.2 - 1)).val) *
            (-1) ^ ((σ v).val * (σ (v.1 - 1, v.2)).val)) := by
      intro v
      rw [clusterSiteTensor, ite_eq_left (show σ v = σ v ∧ σ v = σ v from ⟨rfl, rfl⟩),
        ← Complex.invSqrtTwo_mul_self]
      ring
    simp only [hsite, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      pow_add]
    have hcard : Fintype.card (TorusVertex width height) = width * height := by
      simp [TorusVertex, ZMod.card]
    have hdown :
        ∏ v : TorusVertex width height, (-1 : ℂ) ^ ((σ v).val * (σ (v.1, v.2 - 1)).val) =
        ∏ v : TorusVertex width height, (-1 : ℂ) ^ ((σ v).val * (σ (v.1, v.2 + 1)).val) :=
      (Fintype.prod_equiv (Equiv.addRight ((0, 1) : TorusVertex width height)) _ _ fun u => by
        simp only [Equiv.coe_addRight]
        rw [show u + (0, 1) = (u.1, u.2 + 1) from Prod.ext (add_zero _) rfl]
        simp [mul_comm]).symm
    have hleft :
        ∏ v : TorusVertex width height, (-1 : ℂ) ^ ((σ v).val * (σ (v.1 - 1, v.2)).val) =
        ∏ v : TorusVertex width height, (-1 : ℂ) ^ ((σ v).val * (σ (v.1 + 1, v.2)).val) :=
      (Fintype.prod_equiv (Equiv.addRight ((1, 0) : TorusVertex width height)) _ _ fun u => by
        simp only [Equiv.coe_addRight]
        rw [show u + (1, 0) = (u.1 + 1, u.2) from Prod.ext rfl (add_zero _)]
        simp [mul_comm]).symm
    rw [hcard, hdown, hleft]
    ring
  · intro vb hvb
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hvb
    exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right fun h => hv h.1)
  · intro hb hhb
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hhb
    exact Finset.sum_eq_zero fun vb _ =>
      Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right fun h => hv h.2)

end PEPS
end TNLean
