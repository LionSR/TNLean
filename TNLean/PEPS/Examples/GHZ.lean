/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSiteTensor

/-!
# GHZ: the two-dimensional GHZ state as a PEPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"Two dimensions: PEPS", "The GHZ state", `Papers/2011.12127/TN-Review-main.tex`
lines 2417–2423: the 2D GHZ state $\sum_{i=0}^{d-1}\lvert i,i,\dots,i\rangle$ is a PEPS with
`D = d` and $A^i_{\alpha\beta\gamma\delta}=\delta_{i=\alpha=\beta=\gamma=\delta}$.
Review: arXiv:2011.12127, Appendix A, "The GHZ state" (two dimensions).

**Formalized here.** The review's tensor placed at every site of the discrete torus of any
width and height at least two generates the unnormalized GHZ state: its coefficient at a
configuration `σ` is `∑ i, ∏ v, [σ v = i]`, which is `1` when `σ` is constant and `0`
otherwise.

## Main definitions

* `TNLean.PEPS.ghzSiteTensor`: the tensor $A^i_{\alpha\beta\gamma\delta}=\delta_{i=\alpha=
  \beta=\gamma=\delta}$.
* `TNLean.PEPS.ghzPEPS`: the tensor at every site of the torus.

## Main results

* `TNLean.PEPS.stateCoeff_ghzPEPS`: the PEPS is the unnormalized GHZ state.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2417–2423.
The two-dimensional GHZ tensor $A^i_{\alpha\beta\gamma\delta}=\delta_{i=\alpha=\beta=\gamma=
\delta}$ with bond dimension `D = d`, virtual arguments ordered top, right, down, left. -/
def ghzSiteTensor (d : ℕ) (α β γ δ i : Fin d) : ℂ :=
  if i = α ∧ i = β ∧ i = γ ∧ i = δ then 1 else 0

variable (width height d : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2417–2423.
The GHZ tensor at every site of the `width × height` torus. -/
def ghzPEPS : Tensor (torusGraph width height) d :=
  torusSiteTensor (ghzSiteTensor d)

variable {width height d}

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2417–2423.
The GHZ PEPS generates the unnormalized GHZ state $\sum_{i=0}^{d-1}\lvert i,\dots,i\rangle$:
its coefficient at `σ` is `∑ i, ∏ v, [σ v = i]`. -/
theorem stateCoeff_ghzPEPS (σ : TorusVertex width height → Fin d) :
    stateCoeff (ghzPEPS width height d) σ = ∑ i : Fin d, ∏ v, if σ v = i then 1 else 0 := by
  rw [ghzPEPS, stateCoeff_torusSiteTensor_eq_sum_edge]
  simp only [ghzSiteTensor, Finset.prod_boole]
  rw [Fintype.sum_eq_single (fun _ => σ 0), Fintype.sum_eq_single (σ 0)]
  · simp
  · exact fun i hi => ite_eq_right fun h => hi (h 0 (Finset.mem_univ _)).symm
  · refine fun η hη => ite_eq_right fun h => hη ?_
    have hv := fun v => h v (Finset.mem_univ v)
    -- every vertex agrees with its right and upper neighbours through the shared bond
    have hconst : ∀ v, σ v = σ 0 := torusVertex_apply_eq_apply_zero_of_shift σ
      (fun v => by
        have h1 := (hv (v.1 + 1, v.2)).2.2.2
        rw [torusLeftEdge_add_one] at h1
        exact h1.trans (hv v).2.1.symm)
      (fun v => by
        have h1 := (hv (v.1, v.2 + 1)).2.2.1
        rw [torusDownEdge_add_one] at h1
        exact h1.trans (hv v).1.symm)
    funext e
    rcases torusEdge_horizontal_or_vertical e with he | he
    · obtain ⟨p, rfl⟩ := isHorizontalTorusEdge_eq_rightEdge he
      exact ((hv p).2.1.symm.trans (hconst p))
    · obtain ⟨p, rfl⟩ := isVerticalTorusEdge_eq_upEdge he
      exact ((hv p).1.symm.trans (hconst p))

end PEPS
end TNLean
