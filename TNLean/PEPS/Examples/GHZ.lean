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
lines 2417–2421: the 2D GHZ state $\sum_{i=0}^{d-1}\lvert i,i,\dots,i\rangle$ is a PEPS with
`D = d` and $A^i_{\alpha\beta\gamma\delta}=\delta_{i=\alpha=\beta=\gamma=\delta}$.
Review: arXiv:2011.12127, Appendix A, "The GHZ state" (two dimensions).

**Formalized here.** The four-leg tensor contraction on every torus of positive width and
height generates the unnormalized GHZ state: its coefficient at `σ` is
`∑ i, ∏ v, [σ v = i]`. Horizontal and vertical bond arrays retain self-loops and parallel
bonds. The state is invariant under all simultaneous permutations of its physical labels,
with the same permutation on all four virtual legs. The site tensor is not injective for
`d ≥ 2`.

**Scope restriction (simple-graph representation):** the results about `ghzPEPS` require
width and height at least two, because the simple graph does not represent self-loops.
The contraction identities `sum_prod_ghzSiteTensor` and `sum_prod_ghzSiteTensor_perm` do not
have this restriction. See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## Main definitions

* `TNLean.PEPS.ghzSiteTensor`: the tensor $A^i_{\alpha\beta\gamma\delta}=\delta_{i=\alpha=
  \beta=\gamma=\delta}$.
* `TNLean.PEPS.ghzPEPS`: the tensor at every site of the torus.

## Main results

* `TNLean.PEPS.sum_prod_ghzSiteTensor`: the GHZ contraction at every positive lattice size.
* `TNLean.PEPS.sum_prod_ghzSiteTensor_perm`: its on-site permutation symmetry.
* `TNLean.PEPS.ghzSiteTensor_not_linearIndependent`: local non-injectivity for `d ≥ 2`.
* `TNLean.PEPS.stateCoeff_ghzPEPS`: the simple-graph PEPS is the same GHZ state.
* `TNLean.PEPS.ghzPEPS_not_isVertexInjective`: non-injectivity for `d ≥ 2`.
* `TNLean.PEPS.ghzSiteTensor_perm`, `TNLean.PEPS.ghzSiteTensor_add`: the virtual action.
* `TNLean.PEPS.stateCoeff_ghzPEPS_perm`, `TNLean.PEPS.stateCoeff_ghzPEPS_add`: on-site symmetry.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2417–2421.
The two-dimensional GHZ tensor $A^i_{\alpha\beta\gamma\delta}=\delta_{i=\alpha=\beta=\gamma=
\delta}$ with bond dimension `D = d`, virtual arguments ordered top, right, down, left. -/
def ghzSiteTensor (d : ℕ) (α β γ δ i : Fin d) : ℂ :=
  if i = α ∧ i = β ∧ i = γ ∧ i = δ then 1 else 0

/-- The four-leg contraction of the GHZ tensor on every nonempty periodic lattice is the
GHZ state. Horizontal and vertical bonds are indexed separately, so the formula includes
parallel bonds and self-loops at widths or heights one and two.
Source: arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem sum_prod_ghzSiteTensor {width height d : ℕ} [NeZero width] [NeZero height]
    (σ : TorusVertex width height → Fin d) :
    (∑ hb : TorusVertex width height → Fin d, ∑ vb : TorusVertex width height → Fin d,
      ∏ v, ghzSiteTensor d (vb v) (hb v) (vb (v.1, v.2 - 1))
        (hb (v.1 - 1, v.2)) (σ v)) =
      ∑ i : Fin d, ∏ v, if σ v = i then 1 else 0 := by
  simp only [ghzSiteTensor, Finset.prod_boole]
  rw [Fintype.sum_eq_single σ, Fintype.sum_eq_single σ, Fintype.sum_eq_single (σ 0)]
  · congr 1
    simp only [Finset.mem_univ, forall_true_left, true_and]
    apply propext
    constructor
    · intro h
      apply torusVertex_apply_eq_apply_zero_of_shift σ
      · intro v
        simpa using (h (v.1 + 1, v.2)).2
      · intro v
        simpa using (h (v.1, v.2 + 1)).1
    · intro h v
      exact ⟨(h v).trans (h _).symm, (h v).trans (h _).symm⟩
  · exact fun i hi => ite_eq_right fun h => hi (h 0 (Finset.mem_univ _)).symm
  · exact fun vb hvb => ite_eq_right fun h =>
      hvb (funext fun v => (h v (Finset.mem_univ _)).1.symm)
  · exact fun hb hhb => Finset.sum_eq_zero fun vb _ => ite_eq_right fun h =>
      hhb (funext fun v => (h v (Finset.mem_univ _)).2.1.symm)

/-- The GHZ contraction on every nonempty periodic lattice is invariant under simultaneous
permutations of the physical labels, including the cyclic on-site shifts.
Source state: arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem sum_prod_ghzSiteTensor_perm {width height d : ℕ} [NeZero width] [NeZero height]
    (π : Equiv.Perm (Fin d)) (σ : TorusVertex width height → Fin d) :
    (∑ hb : TorusVertex width height → Fin d, ∑ vb : TorusVertex width height → Fin d,
      ∏ v, ghzSiteTensor d (vb v) (hb v) (vb (v.1, v.2 - 1))
        (hb (v.1 - 1, v.2)) (π (σ v))) =
    ∑ hb : TorusVertex width height → Fin d, ∑ vb : TorusVertex width height → Fin d,
      ∏ v, ghzSiteTensor d (vb v) (hb v) (vb (v.1, v.2 - 1))
        (hb (v.1 - 1, v.2)) (σ v) := by
  simp only [sum_prod_ghzSiteTensor]
  exact Fintype.sum_equiv π.symm _ _ (fun i => by simp [Equiv.eq_symm_apply])

/-- The four-leg GHZ tensor is not injective for `d ≥ 2`, independently of the lattice size:
the virtual basis vector labelled `(0, 1, 0, 0)` has zero image.
Source tensor: arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem ghzSiteTensor_not_linearIndependent {d : ℕ} (hd : 2 ≤ d) :
    ¬ LinearIndependent ℂ (fun a : Fin d × Fin d × Fin d × Fin d =>
      ghzSiteTensor d a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  intro h
  apply h.ne_zero (⟨0, by omega⟩, ⟨1, hd⟩, ⟨0, by omega⟩, ⟨0, by omega⟩)
  funext i
  simp only [ghzSiteTensor, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
  intro h0 h1
  have := congrArg Fin.val (h0.symm.trans h1)
  contradiction

variable (width height d : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2417–2421.
The GHZ tensor at every site of the `width × height` torus. -/
def ghzPEPS : Tensor (torusGraph width height) d :=
  torusSiteTensor (ghzSiteTensor d)

variable {width height d}

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2417–2421.
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

/-- Simultaneously relabelling the physical index and all four virtual indices preserves the
GHZ tensor of arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem ghzSiteTensor_perm (π : Equiv.Perm (Fin d)) (α β γ δ i : Fin d) :
    ghzSiteTensor d (π α) (π β) (π γ) (π δ) (π i) = ghzSiteTensor d α β γ δ i := by
  simp [ghzSiteTensor]

/-- The torus GHZ state is invariant under every simultaneous permutation of its physical
labels. This follows from the state in arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem stateCoeff_ghzPEPS_perm (π : Equiv.Perm (Fin d))
    (σ : TorusVertex width height → Fin d) :
    stateCoeff (ghzPEPS width height d) (π ∘ σ) =
      stateCoeff (ghzPEPS width height d) σ := by
  simpa only [stateCoeff_ghzPEPS, sum_prod_ghzSiteTensor, Function.comp_apply] using
    sum_prod_ghzSiteTensor_perm π σ

/-- The GHZ tensor is not vertex-injective for physical dimension at least two: unequal
horizontal and vertical virtual labels give a zero physical vector. The tensor is the one
of arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem ghzPEPS_not_isVertexInjective (hd : 2 ≤ d) :
    ¬ IsVertexInjective (ghzPEPS width height d) := by
  intro h
  let v : TorusVertex width height := 0
  let η : IncidentEdge (torusGraph width height) v → Fin d :=
    fun e => if e.1 = torusRightEdge v then ⟨1, hd⟩ else ⟨0, by omega⟩
  apply (h v).ne_zero η
  funext i
  simp only [ghzPEPS, torusSiteTensor, torusTopLeg, torusRightLeg, ghzSiteTensor,
    (torusRightEdge_ne_torusUpEdge v v).symm, ↓reduceIte, Pi.zero_apply,
    ite_eq_right_iff, one_ne_zero, imp_false, not_and, η]
  intro h0 h1
  have := congrArg Fin.val (h0.symm.trans h1)
  contradiction

/-- The cyclic on-site shift acts by the same shift on each virtual leg of the GHZ tensor.
Source tensor: arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem ghzSiteTensor_add [NeZero d] (g α β γ δ i : Fin d) :
    ghzSiteTensor d (α + g) (β + g) (γ + g) (δ + g) (i + g) =
      ghzSiteTensor d α β γ δ i :=
  ghzSiteTensor_perm (Equiv.addRight g) α β γ δ i

/-- The torus GHZ state is invariant under the on-site cyclic shift by any residue.
Source state: arXiv:2011.12127, Appendix A, lines 2417–2421. -/
theorem stateCoeff_ghzPEPS_add [NeZero d] (g : Fin d)
    (σ : TorusVertex width height → Fin d) :
    stateCoeff (ghzPEPS width height d) (fun v => σ v + g) =
      stateCoeff (ghzPEPS width height d) σ :=
  stateCoeff_ghzPEPS_perm (Equiv.addRight g) σ

end PEPS
end TNLean
