/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition

/-!
# Wolf Theorem 6.16 — block-permutation cycle structure

This file packages the *block-permutation* side of
Wolf, *Quantum Channels & Operations*, Theorem 6.16, on top of the existing
cyclic-decomposition infrastructure.

Thm. 6.16 describes the asymptotic dynamics of a general trace-preserving
positive Schwarz map `T` as acting on a direct sum of equal-size blocks by
conjugation with a unitary followed by a permutation of the blocks.  Concretely

  T(X) = 0 ⊕ ⊕ₖ U_k · X_{π(k)} · U_k† ⊗ ρ_k

for a suitable permutation `π`.

The current file isolates and formalizes the *block-permutation* data
(the projection family together with the permutation `π`) as a reusable
structure `CycleStructure T`.  All results below are sorry-free.

The remaining *existence* direction of Thm. 6.16 — that every TP positive
Schwarz map admits such a block-permutation decomposition on its asymptotic
image — relies on Wolf Thm. 6.14 (Wedderburn decomposition of the
fixed-point algebra, issues #27/#360) and is left to future work.

## Main definitions

* `CycleStructure T` — bundled block-permutation data for `T`: a finite
  family of orthogonal projections `P : ι → M_D(ℂ)`, a permutation
  `σ : Equiv.Perm ι`, the block-permutation compatibility
  `T (P (σ k)) = P k`, and the multiplicative-domain factorisation
  properties `T (P k · X) = T (P k) · T X` and `T (X · P k) = T X · T (P k)`.

## Main results

* `CycleStructure.map_proj_pow` — `T^n (P (σ^n k)) = P k`.

* `CycleStructure.preserves_corner_pow_orderOf` — `T ^ orderOf σ` preserves
  each corner `P k · M_D(ℂ) · P k`.  This is the corner-preservation half
  of Wolf Thm. 6.16 in its permutation-of-blocks form and is the basis for
  descending the dynamics of `T ^ orderOf σ` to each block.

* `CycleStructure.ofPermDecomp` — convenient constructor from raw
  permutation-decomposition data.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm. 6.16, §6.5]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

variable {D : ℕ}

/-- Bundled data for the **block-permutation form** of Wolf Theorem 6.16.

A `CycleStructure T` records a finite family of orthogonal projections
`P : ι → M_D(ℂ)` on equal-size blocks together with a permutation
`σ : Equiv.Perm ι` and the compatibility conditions that govern the
permutation dynamics of `T` on the corresponding corners:

* `permute` — `T` permutes the projections via `σ`, i.e. `T (P (σ k)) = P k`.
  This captures the block-permutation action of `T` on the Wedderburn
  decomposition of the asymptotic image.
* `mulLeft` / `mulRight` — each `P k` lies in the multiplicative domain
  of `T` (abstract Schwarz-map consequence).

This is the block-permutation data appearing in the asymptotic image of a
general trace-preserving positive Schwarz map, after the Wedderburn /
cyclic-sector decomposition has been carried out. -/
structure CycleStructure (T : MatrixEnd D) where
  /-- Finite index type for the blocks. -/
  ι : Type
  /-- `ι` is finite. -/
  [fintype : Fintype ι]
  /-- `ι` has decidable equality. -/
  [decidableEq : DecidableEq ι]
  /-- The family of block projections. -/
  P : ι → MatrixAlg D
  /-- Each `P k` is an orthogonal projection. -/
  isProj : ∀ k : ι, IsOrthogonalProjection (P k)
  /-- The block-permuting automorphism on block indices. -/
  σ : Equiv.Perm ι
  /-- `T` sends the block indexed by `σ k` back to the block indexed by `k`. -/
  permute : ∀ k : ι, T (P (σ k)) = P k
  /-- Each `P k` lies in the left multiplicative domain of `T`. -/
  mulLeft : ∀ k : ι, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X
  /-- Each `P k` lies in the right multiplicative domain of `T`. -/
  mulRight : ∀ k : ι, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)

namespace CycleStructure

attribute [instance] fintype decidableEq

variable {T : MatrixEnd D}

/-- The `n`-th iterate of `T` sends the projection labelled by `σ^n k`
back to `P k`.  This is the permutation-of-blocks analogue of the
single-cycle result `(T ^ n) (P (cyclicIndex k n)) = P k` used in the
irreducible case of Wolf Thm. 6.6. -/
theorem map_proj_pow (C : CycleStructure T) (n : ℕ) (k : C.ι) :
    (T ^ n) (C.P ((C.σ ^ n) k)) = C.P k := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (T ^ (n + 1)) (C.P ((C.σ ^ (n + 1)) k))
            = (T ^ n) (T (C.P ((C.σ ^ (n + 1)) k))) := by
                simp [pow_succ]
        _ = (T ^ n) (T (C.P (C.σ ((C.σ ^ n) k)))) := by
                simp [pow_succ']
        _ = (T ^ n) (C.P ((C.σ ^ n) k)) := by
                rw [C.permute ((C.σ ^ n) k)]
        _ = C.P k := ih

/-- After `orderOf σ` applications of `T`, each projection `P k` returns
to itself. -/
theorem pow_orderOf_apply_proj (C : CycleStructure T) (k : C.ι) :
    (T ^ orderOf C.σ) (C.P k) = C.P k := by
  have hmain : (T ^ orderOf C.σ) (C.P ((C.σ ^ orderOf C.σ) k)) = C.P k :=
    C.map_proj_pow (orderOf C.σ) k
  have hσ : (C.σ ^ orderOf C.σ) = 1 := pow_orderOf_eq_one C.σ
  simpa [hσ] using hmain

/-- **Wolf Theorem 6.16 — corner preservation.**

The `orderOf σ`-th iterate of `T` preserves each corner
`P k · M_D(ℂ) · P k`.  This is the fundamental corner-preservation half
of Wolf Thm. 6.16 in its permutation-of-blocks form and is what allows
one to descend the dynamics of `T ^ orderOf σ` to each block.

It is obtained by specialising the generic permutation-decomposition
lemma `preserves_corner_pow_orderOf_of_perm_decomp` to the bundled data
`C`. -/
theorem preserves_corner_pow_orderOf (C : CycleStructure T) (k : C.ι) :
    PreservesCorner (C.P k) (T ^ orderOf C.σ) :=
  preserves_corner_pow_orderOf_of_perm_decomp
    (σ := C.σ) (P := C.P) C.isProj C.permute C.mulLeft C.mulRight k

/-- Convenient constructor from raw permutation-decomposition data.

This exposes the hypotheses of `preserves_corner_pow_orderOf_of_perm_decomp`
as a bundled `CycleStructure`. -/
def ofPermDecomp
    {T : MatrixEnd D} {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (P : ι → MatrixAlg D)
    (hPproj : ∀ k : ι, IsOrthogonalProjection (P k))
    (hperm : ∀ k : ι, T (P (σ k)) = P k)
    (hMulLeft : ∀ k : ι, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : ι, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    CycleStructure T where
  ι := ι
  P := P
  isProj := hPproj
  σ := σ
  permute := hperm
  mulLeft := hMulLeft
  mulRight := hMulRight

end CycleStructure
