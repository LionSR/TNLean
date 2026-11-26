/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import QICLean.ManyBody.Sites.Placement.PlaceAlong
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.CanonicalForm.Correlation.WindowCorrelator

/-!
# Operators on windows of a chain: centring, norm, nesting and support

The chapter's proof of the depth lower bound (`thm:ldp_depth_lower_bound`, the
chapter's version of arXiv:2307.01696, Theorem 1) places a fixed operator on many
windows of consecutive sites of the chain, `ManyBody.placeAlong` along
`ManyBody.chainWindow`. Placing is a unital `*`-homomorphism (`ManyBody.placeAlongHom`), so it
preserves products and adjoints (`ManyBody.placeAlong_mul`, `ManyBody.placeAlong_conjTranspose`).
This file adds the facts about window placements used there:

* centring and the operator norm (`placeAlong_chainWindow_sub_smul_one`,
  `norm_toEuclideanCLM_placeAlong_chainWindow_le`);
* an operator on a window inside a larger window is an operator on the smaller
  window (`placeAlong_chainWindow_placeAlong_chainWindow`);
* an operator on the window of sites `a, …, a + L - 1` acts on those sites in the sense
  of `ManyBody.supportedOperators`, the support used by the light cone of unitary circuits
  (`placeAlong_chainWindow_mem_supportedOperators`), and every operator acting on those sites
  is placed on the window (`exists_placeAlong_chainWindow_eq_of_mem_supportedOperators`).

All windows here are windows that do not wrap around the ring: `a + L ≤ N`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- Every operator supported on a consecutive window is an actual
placement of a matrix on that complete window. Source context:
arXiv:2307.01696, supported local observables on consecutive blocks. -/
theorem exists_placeAlong_chainWindow_eq_of_mem_supportedOperators
    {L N a : ℕ} (haL : a + L ≤ N)
    {X : Matrix (Cfg d N) (Cfg d N) ℂ}
    (hX : X ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun (i : Fin N) ↦ a ≤ i.val ∧ i.val < a + L)) :
    ∃ Y : Matrix (Cfg d L) (Cfg d L) ℂ,
      X = ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a haL) Y :=
  ManyBody.exists_eq_placeAlong_of_mem_supportedOperators _
    (by rw [ManyBody.map_chainWindow a haL]; exact hX)

/-- The window operator of `X - c` is the window operator of `X` minus `c`: the centred
observables `𝒪 - ⟨𝒪⟩` of the chapter's proof of `thm:ldp_depth_lower_bound`
(arXiv:2307.01696, Supplemental Material, proof of Theorem 1). -/
theorem placeAlong_chainWindow_sub_smul_one {L N a : ℕ} (haL : a + L ≤ N) (c : ℂ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) (ManyBody.chainWindow a haL) (X - c • 1) =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a haL) X - c • 1 := by
  rw [ManyBody.placeAlong_sub, ManyBody.placeAlong_smul, ManyBody.placeAlong_one]

/-- Placing an operator on a window does not increase its operator norm. This bounds the norms
of the translated observables in the chapter's proof of `thm:ldp_depth_lower_bound` ("These have
norm at most `2`"; the chapter's version of arXiv:2307.01696, Supplemental Material, proof of
Theorem 1). -/
theorem norm_toEuclideanCLM_placeAlong_chainWindow_le {L N a : ℕ}
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a haL) X)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) X‖ := by
  open scoped Matrix.Norms.L2Operator in
  have h := ManyBody.norm_placeAlong_le (X := fun _ : Fin N ↦ Fin d) (ManyBody.chainWindow a haL) X
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def] at h
  exact h

/-- **Nested windows.** An operator on the window of sites `b, …, b + L - 1` of a chain of
`w` sites, placed on the window `a, …, a + w - 1` of a chain of `N` sites, is the operator
on the window `a + b, …, a + b + L - 1`. This identifies the block operators of the
chapter's proof of `thm:ldp_depth_lower_bound` (arXiv:2307.01696, Supplemental Material,
proof of Theorem 1) with products of translated observables. -/
theorem placeAlong_chainWindow_placeAlong_chainWindow {L w N a b : ℕ}
    (haw : a + w ≤ N) (hbL : b + L ≤ w) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) (ManyBody.chainWindow a haw)
        (ManyBody.placeAlong (X := fun _ : Fin w ↦ Fin d) (ManyBody.chainWindow b hbL) X) =
      ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow (a + b) (by omega : a + b + L ≤ N)) X := by
  rw [ManyBody.placeAlong_placeAlong, ManyBody.chainWindow_trans_chainWindow]

/-- **Support of a window operator.** The operator `X` placed on the sites
`a, …, a + L - 1` acts on those sites in the sense of `ManyBody.supportedOperators`.
This is what the light cone of arXiv:2307.01696, Supplemental Material, proof of
Theorem 1, is applied to. -/
theorem placeAlong_chainWindow_mem_supportedOperators {L N a : ℕ}
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a haL) X ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d)
          (Finset.univ.filter fun (k : Fin N) ↦ a ≤ k.val ∧ k.val < a + L) := by
  have h := ManyBody.placeAlong_mem_supportedOperators (X := fun _ : Fin N ↦ Fin d)
    (ManyBody.chainWindow a haL) X
  rwa [ManyBody.map_chainWindow a haL] at h

end MPSTensor
