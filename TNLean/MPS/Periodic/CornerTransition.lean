/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Blocking

/-!
# One-site corner transitions and cyclic staircase products

For a cyclic family of matrices `P : Fin m → Matrix (Fin D) (Fin D) ℂ` on the
ambient bond algebra of an MPS tensor `A : MPSTensor d D`, this file defines
the **one-site corner transitions**

$$\tau_k(A)^i := P_k \cdot A^i \cdot P_{k+1}, \qquad k \in \mathrm{Fin}\,m,$$

together with the associated staircase evaluation of a word at a starting
sector and the m-fold cyclic staircase product assembled as an MPSTensor on
blocked physical indices. When `(P_k)` is the cyclic-sector projection family
of `IsCyclicSectorDecomp` (see `TNLean/MPS/Periodic/Overlap.lean`), the m-fold
staircase product at sector `u`, evaluated on a blocked physical index, is the
ambient-algebra representative of the compressed blocked sector tensor
`blocksA u`. This is the matrix-level content of Eq. A.8 in Appendix A of
`arXiv:1708.00029`: the identification with the compressed tensor through the
per-sector compression isometry `φ k` (now exposed by
`exists_compressedTensor_of_supported_projection`) is carried out in the
Tier-A bridge lemmas in `MPS/Periodic/Overlap.lean`; this file provides only
the ambient matrix algebra needed by those bridges.

## Main definitions

* `MPSTensor.cornerTransition A P k` — the single-site corner transition
  `fun i => P k * A i * P (k + 1)`.
* `MPSTensor.cornerEvalWord A P u w` — staircase evaluation of a word `w` at
  starting sector `u`: the alternating product
  `P u * A(w₀) * P(u+1) * A(w₁) * ⋯ * A(w_{L-1}) * P(u+L)`.
* `MPSTensor.blockedCornerTransitionTensor A P u` — the m-fold cyclic
  staircase product assembled as an MPSTensor on blocked physical indices,
  `fun i => cornerEvalWord A P u (wordOfBlock d m i)`.

## Main statements

* `MPSTensor.cornerTransition_proj_left`,
  `MPSTensor.cornerTransition_proj_right` — absorption of the source/target
  projection on the left/right of a transition factor under idempotence.
* `MPSTensor.cornerTransition_proj_left_other`,
  `MPSTensor.cornerTransition_proj_right_other` — cross-sector annihilation
  for an orthogonal projection family.
* `MPSTensor.cornerEvalWord_proj_left` — head-projection absorption of the
  staircase evaluation under idempotence of the intermediate projections.
* `MPSTensor.blockedCornerTransitionTensor_apply` — the m-fold cyclic
  staircase product as the ambient-algebra form of Eq. A.8.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, Appendix A,
  Equation A.8.

## Tags

MPS, periodic, cyclic sector decomposition, corner transition, staircase
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## One-site corner transitions -/

/-- One-site corner transition associated to a cyclic projection family
`P : Fin m → Matrix (Fin D) (Fin D) ℂ`:

$$\tau_k(A)^i := P_k \cdot A^i \cdot P_{k+1}.$$

The projections `P k` are typically the cyclic-sector projections of
`IsCyclicSectorDecomp`; the definition itself does not require `(P k)` to be
a projection, and the algebraic identities below isolate the hypotheses
actually used. -/
def cornerTransition {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k : Fin m) :
    MPSTensor d D :=
  fun i => P k * A i * P (k + 1)

@[simp] lemma cornerTransition_apply
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k : Fin m) (i : Fin d) :
    cornerTransition A P k i = P k * A i * P (k + 1) := rfl

/-- Pointwise equal tensors produce equal corner transitions. -/
lemma cornerTransition_congr
    {m : ℕ} [NeZero m] {A B : MPSTensor d D}
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k : Fin m) (hAB : A = B) :
    cornerTransition A P k = cornerTransition B P k := by
  subst hAB; rfl

/-- Left projection absorption: if `P k` is idempotent, then
`P k · τ_k(A)^i = τ_k(A)^i`. -/
lemma cornerTransition_proj_left
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k : Fin m)
    (hP : P k * P k = P k) (i : Fin d) :
    P k * cornerTransition A P k i = cornerTransition A P k i := by
  simp only [cornerTransition_apply, ← Matrix.mul_assoc, hP]

/-- Right projection absorption: if `P (k+1)` is idempotent, then
`τ_k(A)^i · P (k+1) = τ_k(A)^i`. -/
lemma cornerTransition_proj_right
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k : Fin m)
    (hP : P (k + 1) * P (k + 1) = P (k + 1)) (i : Fin d) :
    cornerTransition A P k i * P (k + 1) = cornerTransition A P k i := by
  simp only [cornerTransition_apply, Matrix.mul_assoc, hP]

/-- Cross-sector annihilation on the left: if `P j * P k = 0`, then
left-multiplying `τ_k(A)^i` by `P j` vanishes. -/
lemma cornerTransition_proj_left_other
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k j : Fin m)
    (hOrth : P j * P k = 0) (i : Fin d) :
    P j * cornerTransition A P k i = 0 := by
  simp only [cornerTransition_apply, ← Matrix.mul_assoc, hOrth,
    Matrix.zero_mul]

/-- Cross-sector annihilation on the right: if `P (k+1) * P j = 0`, then
right-multiplying `τ_k(A)^i` by `P j` vanishes. -/
lemma cornerTransition_proj_right_other
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (k j : Fin m)
    (hOrth : P (k + 1) * P j = 0) (i : Fin d) :
    cornerTransition A P k i * P j = 0 := by
  simp only [cornerTransition_apply, Matrix.mul_assoc, hOrth,
    Matrix.mul_zero]

/-! ## Cyclic staircase evaluation -/

/-- Staircase evaluation of a word at starting sector `u`, recursively
defined by

$$\mathrm{cornerEvalWord}\,A\,P\,u\,\varepsilon = P_u,\qquad
  \mathrm{cornerEvalWord}\,A\,P\,u\,(i \cdot w) =
    P_u \cdot A^i \cdot \mathrm{cornerEvalWord}\,A\,P\,(u+1)\,w.$$

For a word of length `L`, this expands to

$$P_u \cdot A^{w_0} \cdot P_{u+1} \cdot A^{w_1} \cdot P_{u+2} \cdot
  \ldots \cdot A^{w_{L-1}} \cdot P_{u+L}.$$ -/
def cornerEvalWord {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) :
    Fin m → List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | u, [] => P u
  | u, i :: w => P u * A i * cornerEvalWord A P (u + 1) w

@[simp] lemma cornerEvalWord_nil
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (u : Fin m) :
    cornerEvalWord A P u [] = P u := rfl

@[simp] lemma cornerEvalWord_cons
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (u : Fin m)
    (i : Fin d) (w : List (Fin d)) :
    cornerEvalWord A P u (i :: w) =
      P u * A i * cornerEvalWord A P (u + 1) w := rfl

/-- A single-site staircase evaluation equals the corner transition factor
`τ_u(A)^i` on the nose. -/
lemma cornerEvalWord_singleton
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (u : Fin m) (i : Fin d) :
    cornerEvalWord A P u [i] = cornerTransition A P u i := by
  simp [cornerEvalWord, cornerTransition]

/-- Head-projection absorption: staircase evaluation starts with `P u` as a
left factor (under idempotence of `P u`). -/
lemma cornerEvalWord_proj_left
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hProj : ∀ k : Fin m, P k * P k = P k) :
    ∀ (u : Fin m) (w : List (Fin d)),
      P u * cornerEvalWord A P u w = cornerEvalWord A P u w := by
  intro u w
  match w with
  | [] =>
      simp [cornerEvalWord, hProj u]
  | i :: w =>
      simp only [cornerEvalWord]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hProj u]

/-! ## m-fold cyclic staircase product on blocked physical indices -/

/-- The cyclic staircase product at sector `u`, assembled as an MPSTensor on
blocked physical indices `Fin (blockPhysDim d m)`. For a blocked index `i`
corresponding to a word `(i_0, i_1, …, i_{m-1})`, this returns the ambient
matrix

$$P_u \cdot A^{i_0} \cdot P_{u+1} \cdot A^{i_1} \cdot P_{u+2}
  \cdots P_{u+m-1} \cdot A^{i_{m-1}} \cdot P_{u+m} = P_u \cdot A^{i_0}
  \cdot P_{u+1} \cdots A^{i_{m-1}} \cdot P_u,$$

using `u + m = u` in `Fin m`. This is the ambient-algebra representative of
`blocksA u i`; identifying the two via the compression isometry `φ u` from
`IsCyclicSectorDecomp` is the content of the Tier-A bridge lemmas. -/
noncomputable def blockedCornerTransitionTensor
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (u : Fin m) :
    MPSTensor (blockPhysDim d m) D :=
  fun i => cornerEvalWord A P u (wordOfBlock d m i)

@[simp] lemma blockedCornerTransitionTensor_apply
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (u : Fin m)
    (i : Fin (blockPhysDim d m)) :
    blockedCornerTransitionTensor A P u i =
      cornerEvalWord A P u (wordOfBlock d m i) := rfl

/-- Left projection absorption for the blocked cyclic staircase product. -/
lemma blockedCornerTransitionTensor_proj_left
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hProj : ∀ k : Fin m, P k * P k = P k)
    (u : Fin m) (i : Fin (blockPhysDim d m)) :
    P u * blockedCornerTransitionTensor A P u i =
      blockedCornerTransitionTensor A P u i := by
  simpa [blockedCornerTransitionTensor]
    using cornerEvalWord_proj_left (A := A) (P := P) hProj u (wordOfBlock d m i)

end MPSTensor
